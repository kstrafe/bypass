//! # Bypass: Thread-local dynamic key-value store #
//!
//! It is sometimes convenient to pass certain values by using an implicit
//! environment. This crate implements such an environment. We "bypass" the
//! standard way of passing values through arguments and return values, and
//! instead store our values in a thread-local key-value store.
//!
//! This approach effectively mimics the concept known as "dynamic variables"
//! in other programming languages.
//!
//! # Examples #
//!
//! ```
//! // Define a thread-local scope.
//! bypass::scope!(static MY_SCOPE);
//!
//! MY_SCOPE.scope(|| {
//!     MY_SCOPE.insert("some name", 123);
//!     some_function();
//! });
//!
//! fn some_function() {
//!     let item: i32 = MY_SCOPE.get("some name");
//!     println!("Fetched 'some name': {}", item);
//! }
//! ```
//!
//! This also allows us to pass data from `some_function` to the caller by
//! calling [insert](Scope::insert) inside `some_function` followed by calling
//! [get](Scope::get) or [remove](Scope::remove) after the function call
//! completes.
//!
//! # Scoping #
//!
//! A scope constrains the extent of [insert](Scope::insert)s.
//!
//! The following example shows its usage. If we did not have the
//! inner scope surrounding the `function` call, then this code would panic on
//! the second iteration of the for loop
//! because it would cause a duplicate key to exist.
//!
//! ```
//! bypass::scope!(static MAIN);
//!
//! // Initial scope.
//! MAIN.scope(|| {
//!     for _ in 0..10 {
//!         // Second scope.
//!         MAIN.scope(|| function());
//!     }
//! });
//!
//! fn function() {
//!     // Only lives for the duration of the second scope.
//!     MAIN.insert("x", 123);
//!
//!     // Further calls that use "x"
//!     // ...
//! }
//! ```
//!
//! Inside a scope, performing [get](Scope::get), [modify](Scope::modify), or
//! [remove](Scope::remove) will first search the current scope for a matching
//! key. If not found, search the parent. If not found, search the parent's
//! parent, and so on.
//!
//! # Lifting #
//!
//! Lifting a key inside a scope means to defer all its [core operations] to the
//! parent scope, if any such parent exists. Otherwise the current scope is
//! used.
//!
//! ```
//! bypass::scope!(static MAIN);
//!
//! MAIN.scope(|| {
//!     MAIN.scope(|| {
//!         MAIN.lift("x");
//!         MAIN.insert("x", 123);
//!     });
//!
//!     let value: i32 = MAIN.get("x");
//!     println!("x={}", value);
//! });
//! ```
//!
//! The above would panic on `get` if the lift were to be removed, since the
//! innermost scope would capture the insert which the outermost scope can't
//! access.
//!
//! ## Translations ##
//!
//! Lifts allow you to translate a key. This can be useful when two pieces of
//! code need to share some data but internally use different keys,
//! so you wrap one piece of code in a
//! scope that lifts that key into another key.
//!
//! ```
//! bypass::scope!(static MAIN);
//!
//! MAIN.scope(|| {
//!     MAIN.scope(|| {
//!         // Translates any core operation on "x" into "y".
//!         MAIN.lift("x").to("y");
//!         MAIN.insert("x", 123);
//!     });
//!
//!     let value: i32 = MAIN.get("y");
//!     println!("y={}", value);
//! });
//! ```
//!
//! # Intended usage #
//!
//! Bypass is not intended to supplant the normal
//! argument-and-return method of passing data around. Its main purpose is to
//! provide a way to avoid tramp data, i.e. data that is only passed through a
//! significant amount of functions without being used directly.
//!
//! Passing such data along through every intermediary may be cumbersome and
//! noisy. Bypass serves as an alternative mainly for such cases. Especially
//! during the exploratory phase of programming, we may want to experiment with
//! just making some value available somewhere else. Having to pass said value
//! through many places can consume significant time. Bypass can be used instead
//! to quickly get a prototype up and running.
//!
//! Similarly, we can use bypass to "return" data from a deeply nested call
//! where we are not interested in returning it through every stack frame
//! manually.
//!
//! As such, this library explicitly does not provide methods like `contains`,
//! and panics as soon as something is not as expected.
//!
//! # Logging #
//!
//! Keys can be either `&'static str` or a `String`. When strings are
//! constructed (e.g. via `format!`), it may be hard to figure out where a key
//! is inserted in a codebase. To debug this library you can set a logger via
//! [debug](Scope::debug).
//!
//! If no logger is set then the default logger will be used that prints all
//! operations to stderr. The default logger prints the code location of each
//! [get](Scope::get) and [remove](Scope::remove), and at which location that
//! data was inserted at.
//!
//! The output per operation looks like the following.
//!
//! ```text
//! bypass: get "a" | tests/test.rs:206:28 <--- tests/test.rs:193:11
//! |         |  |      |                       |
//! | Library |  | Key  | Called from           | Inserted at
//!           |
//!           | Operation type
//! ```
//!
//! # Dropping #
//!
//! Upon exiting a [scope], values that are part of that scope will be dropped
//! in lexicographic order of their associated keys.
//!
//! # Core Operations #
//!
//! Core operations are [insert](Scope::insert), [get](Scope::get),
//! [modify](Scope::modify), and [remove](Scope::remove).
//!
//! [core operations]: crate#core-operations
#![deny(
    missing_docs,
    rustdoc::broken_intra_doc_links,
    unused_crate_dependencies,
    unused_imports,
    unused_qualifications
)]
use std::{
    any::Any,
    borrow::Cow,
    cell::RefCell,
    collections::{BTreeMap, HashMap},
    fmt, panic,
};

/// Creates a scope.
#[macro_export]
macro_rules! scope {
    ($(#[$attrs:meta])* $vis:vis static $name:ident) => (
        $(#[$attrs])*
        /// [bypass](crate) scope.
        $vis static $name: $crate::Scope = $crate::Scope {
            inner: {
                ::std::thread_local!(static FOO: ::std::cell::RefCell<$crate::ScopeInner> = {
                    ::std::cell::RefCell::new($crate::ScopeInner::new())
                });
                &FOO
            },
        };
    )
}

type Location = &'static panic::Location<'static>;

type CowStr = Cow<'static, str>;

struct Item {
    item: Box<dyn Any>,
    location: Location,
}

struct ScopeArray<'a>(&'a [Store]);

impl<'a> ScopeArray<'a> {
    fn new(scopes: &'a [Store]) -> Self {
        Self(scopes)
    }

    fn split(&self) -> Option<(&Store, ScopeArray<'a>)> {
        let len = self.0.len();
        if len > 0 {
            Some((&self.0[len - 1], ScopeArray::new(&self.0[0..len - 1])))
        } else {
            None
        }
    }
}

/// Describes the operation that is being performed.
pub enum Operation {
    /// Set to this value when a call to [get](Scope::get) is invoked.
    Get,
    /// Set to this value when a call to [modify](Scope::modify) is invoked.
    Modify,
    /// Set to this value when a call to [remove](Scope::remove) is invoked.
    Remove,
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operation::Get => f.write_str("get"),
            Operation::Modify => f.write_str("modify"),
            Operation::Remove => f.write_str("remove"),
        }
    }
}

/// Contains information used in logging.
pub struct Log<'a> {
    /// Type of operation, either [get](Scope::get) or [remove](Scope::remove).
    pub operation: Operation,
    /// Source location corresponding to the [insert](Scope::insert).
    pub source: Location,
    /// Source location from which [get](Scope::get) or [remove](Scope::remove)
    /// was called.
    pub destination: Location,
    /// Key used to perform the lookup.
    ///
    /// This is the final key that was used, and may be different from the key
    /// provided to [get](Scope::get) or
    /// [remove](Scope::remove) due to [lift](Scope::lift)s that may have
    /// translated the original key.
    pub key: &'a CowStr,
}

impl<'a> fmt::Display for Log<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "bypass: {} {:?} | {} <--- {}",
            self.operation, self.key, self.destination, self.source
        )
    }
}

struct Store {
    // This is a BTreeMap to make drop order deterministic.
    items: RefCell<BTreeMap<CowStr, Item>>,
    lifts: RefCell<HashMap<CowStr, (CowStr, Location)>>,
}

impl Store {
    fn new() -> Self {
        Self {
            items: Default::default(),
            lifts: Default::default(),
        }
    }

    fn lift(&self, from: CowStr, location: Location) {
        assert!(
            self.lifts
                .borrow_mut()
                .insert(from.clone(), (from, location))
                .is_none(),
            "bypass: lift already exists"
        );
    }

    fn lift_to(&self, from: CowStr, to: CowStr) {
        let mut binding = self.lifts.borrow_mut();
        let Some(entry) = binding.get_mut(&from) else {
            panic!("bypass: internal error");
        };

        assert!(entry.0 == from, "bypass: lift already mapped");

        entry.0 = to;
    }

    fn insert<V: Any>(&self, key: CowStr, value: V, location: Location, parents: ScopeArray) {
        if let Some(lift) = self.lifts.borrow().get(&key) {
            if let Some((parent, rest)) = parents.split() {
                parent.insert(lift.0.clone(), value, location, rest);
            } else {
                self.insert_inner(lift.0.clone(), value, location);
            }
        } else {
            self.insert_inner(key, value, location);
        }
    }

    fn insert_inner<V: Any>(&self, key: CowStr, value: V, location: Location) {
        assert!(
            self.items
                .borrow_mut()
                .insert(
                    key,
                    Item {
                        item: Box::new(value),
                        location,
                    }
                )
                .is_none()
        );
    }

    fn get<V: Any + Clone>(
        &self,
        key: CowStr,
        location: Location,
        parents: ScopeArray,
        logger: &dyn Fn(Log),
    ) -> V {
        if let Some(lift) = self.lifts.borrow().get(&key) {
            if let Some((parent, rest)) = parents.split() {
                parent.get(lift.0.clone(), location, rest, logger)
            } else {
                self.get_inner(lift.0.clone(), location, parents, logger)
            }
        } else {
            self.get_inner(key, location, parents, logger)
        }
    }

    fn get_inner<V: Any + Clone>(
        &self,
        key: CowStr,
        location: Location,
        parents: ScopeArray,
        logger: &dyn Fn(Log),
    ) -> V {
        let this = self.items.borrow();

        let Some(item): Option<&Item> = this.get(&key) else {
            if let Some((parent, rest)) = parents.split() {
                return parent.get(key, location, rest, logger);
            } else {
                panic!("bypass: key not present: {:?}", key)
            }
        };

        let result = (*item.item)
            .downcast_ref::<V>()
            .expect("bypass: type not as expected")
            .clone();

        let log = Log {
            operation: Operation::Get,
            source: item.location,
            destination: location,
            key: &key,
        };
        logger(log);

        result
    }

    fn modify<V: Any, F: FnOnce(&mut V) -> R, R>(
        &self,
        key: CowStr,
        modifier: F,
        location: Location,
        parents: ScopeArray,
        logger: &dyn Fn(Log),
    ) -> R {
        if let Some(lift) = self.lifts.borrow().get(&key) {
            if let Some((parent, rest)) = parents.split() {
                parent.modify(lift.0.clone(), modifier, location, rest, logger)
            } else {
                self.modify_inner(lift.0.clone(), modifier, location, parents, logger)
            }
        } else {
            self.modify_inner(key, modifier, location, parents, logger)
        }
    }

    fn modify_inner<V: Any, F: FnOnce(&mut V) -> R, R>(
        &self,
        key: CowStr,
        modifier: F,
        location: Location,
        parents: ScopeArray,
        logger: &dyn Fn(Log),
    ) -> R {
        let mut this = self.items.borrow_mut();

        let Some(item): Option<&mut Item> = this.get_mut(&key) else {
            if let Some((parent, rest)) = parents.split() {
                return parent.modify(key, modifier, location, rest, logger);
            } else {
                panic!("bypass: key not present: {:?}", key)
            }
        };

        let value = (*item.item)
            .downcast_mut::<V>()
            .expect("bypass: type not as expected");

        let log = Log {
            operation: Operation::Modify,
            source: item.location,
            destination: location,
            key: &key,
        };
        logger(log);

        modifier(value)
    }

    fn remove<V: Any>(
        &self,
        key: CowStr,
        location: Location,
        parents: ScopeArray,
        logger: &dyn Fn(Log),
    ) -> V {
        if let Some(lift) = self.lifts.borrow().get(&key) {
            if let Some((parent, rest)) = parents.split() {
                parent.remove(lift.0.clone(), location, rest, logger)
            } else {
                self.remove_inner(lift.0.clone(), location, parents, logger)
            }
        } else {
            self.remove_inner(key, location, parents, logger)
        }
    }

    fn remove_inner<V: Any>(
        &self,
        key: CowStr,
        location: Location,
        parents: ScopeArray,
        logger: &dyn Fn(Log),
    ) -> V {
        let mut this = self.items.borrow_mut();

        let Some(item): Option<Item> = this.remove(&key) else {
            if let Some((parent, rest)) = parents.split() {
                return parent.remove(key, location, rest, logger);
            } else {
                panic!("bypass: key not present: {:?}", key)
            }
        };

        let log = Log {
            operation: Operation::Remove,
            source: item.location,
            destination: location,
            key: &key,
        };

        logger(log);

        let result = (item.item)
            .downcast::<V>()
            .unwrap_or_else(|_| panic!("bypass: type not as expected"));

        *result
    }
}

/// Allows setting a translation on a [lift](Scope::lift).
///
/// # Examples #
///
/// ```
/// bypass::scope!(static SCOPE);
///
/// SCOPE.scope(|| {
///     let lift: bypass::Lift = SCOPE.lift("x");
///     lift.to("y");
///
///     // Typically written as:
///     SCOPE.lift("a").to("b");
/// });
pub struct Lift(&'static std::thread::LocalKey<RefCell<ScopeInner>>, CowStr);

impl Lift {
    fn new(scope: &'static std::thread::LocalKey<RefCell<ScopeInner>>, name: CowStr) -> Self {
        Self(scope, name)
    }

    /// Map a lift to anohter name.
    pub fn to<T: Into<CowStr>>(self, to: T) {
        let to = to.into();
        self.0.with_borrow_mut(|x| {
            x.scopes.last_mut().expect(NO_SCOPE).lift_to(self.1, to);
        });
    }
}

const NO_SCOPE: &str = "bypass: scope has not been created";

/// Named scope created using [bypass::scope](crate::scope).
///
/// # Examples #
///
/// ```
/// // Declare a thread-local scope called `NAME`.
/// bypass::scope!(static NAME);
///
/// // Creates the first, top-level subscope.
/// NAME.scope(|| {
///     // Perform operations on the scope.
///     NAME.insert("x", 123);
/// });
/// ```
pub struct Scope {
    #[doc(hidden)]
    pub inner: &'static std::thread::LocalKey<RefCell<ScopeInner>>,
}

impl Scope {
    /// A scope constrains the extent of [insert](Scope::insert)s. It can insert
    /// into its parent using [lift](Scope::lift).
    ///
    /// # Examples #
    ///
    /// ```
    /// bypass::scope!(static NAME);
    ///
    /// NAME.scope(|| {
    ///     NAME.insert("x", 1);
    ///
    ///     NAME.scope(|| {
    ///         NAME.insert("x", 2);
    ///
    ///         let value: i32 = NAME.get("x");
    ///         assert_eq!(value, 2);
    ///     });
    ///
    ///     let value: i32 = NAME.get("x");
    ///     assert_eq!(value, 1);
    /// });
    /// ```
    pub fn scope<F, R>(&self, work: F) -> R
    where
        F: FnOnce() -> R,
    {
        self.inner.with_borrow_mut(|x| x.scopes.push(Store::new()));

        struct OnDrop<'a>(&'a Scope);

        impl Drop for OnDrop<'_> {
            fn drop(&mut self) {
                self.0.inner.with_borrow_mut(|x| x.scopes.pop());
            }
        }

        let on_drop = OnDrop(self);

        let result = (work)();

        drop(on_drop);
        result
    }

    /// Sets the debugger for this scope.
    ///
    /// `log` will be called for each [get](Scope::get) and
    /// [remove](Scope::remove).
    ///
    /// # Examples #
    ///
    /// ```
    /// bypass::scope!(static X);
    ///
    /// X.debug(|log| { println!("{}", log); });
    /// ```
    pub fn debug<F>(&self, log: F)
    where
        F: Fn(Log) + 'static,
    {
        self.inner.with_borrow_mut(|x| x.debug = Box::new(log));
    }

    /// Lifts a given key to the parent scope.
    ///
    /// [Core operations](crate#core-operations) whose keys match a
    /// `lift` will perform their operations in the parent
    /// scope. If no parent scope exists then the current scope is used.
    ///
    /// # Panics #
    ///
    /// Panics if a lift of the same key already exists in the current scope.
    ///
    /// # Examples #
    ///
    /// ```
    /// bypass::scope!(static X);
    ///
    /// X.scope(|| {
    ///     X.scope(|| {
    ///         X.lift("x");
    ///         X.insert("x", 123);
    ///     });
    ///
    ///     let value: i32 = X.get("x");
    ///     println!("{}", value);
    /// });
    /// ```
    #[track_caller]
    pub fn lift<A: Into<CowStr>>(&self, from: A) -> Lift {
        let location = panic::Location::caller();

        let from = from.into();

        self.inner.with_borrow(|x| {
            x.scopes
                .last()
                .expect(NO_SCOPE)
                .lift(from.clone(), location);
            Lift::new(self.inner, from)
        })
    }

    /// Inserts an entry into the scope.
    ///
    /// # Panics #
    ///
    /// Panics if the key already exists.
    ///
    /// # Example #
    ///
    /// ```
    /// bypass::scope!(static X);
    ///
    /// X.scope(|| {
    ///     X.insert("abc", 123);
    /// });
    /// ```
    #[track_caller]
    pub fn insert<K: Into<CowStr>, V: Any>(&self, key: K, value: V) {
        let key = key.into();

        let location = panic::Location::caller();

        self.inner.with_borrow(|x| {
            let items = ScopeArray::new(&x.scopes[..]);
            if let Some((scope, rest)) = items.split() {
                scope.insert(key, value, location, rest);
            } else {
                panic!("{}", NO_SCOPE);
            }
        })
    }

    /// Gets a clone of an entry from the scope.
    ///
    /// # Panics #
    ///
    /// Panics if the key does not exist, or if the value associated with
    /// this key is not does not match `V`.
    ///
    /// # Examples #
    ///
    /// ```
    /// bypass::scope!(static X);
    ///
    /// X.scope(|| {
    ///     X.insert("abc", 123);
    ///     let value: i32 = X.get("abc");
    ///     println!("{}", value);
    /// });
    /// ```
    #[track_caller]
    pub fn get<V: Any + Clone, K: Into<CowStr>>(&self, key: K) -> V {
        let key = key.into();

        let location = panic::Location::caller();
        self.inner.with_borrow(|x| {
            let items = ScopeArray::new(&x.scopes[..]);
            if let Some((scope, rest)) = items.split() {
                scope.get(key, location, rest, &x.debug)
            } else {
                panic!("{}", NO_SCOPE)
            }
        })
    }

    /// Modify an entry in the scope.
    ///
    /// # Panics #
    ///
    /// Panics if the key does not exist, or if the value associated with
    /// this key is not does not match `V`.
    ///
    /// # Examples #
    ///
    /// ```
    /// bypass::scope!(static X);
    ///
    /// X.scope(|| {
    ///     X.insert("abc", 123);
    ///     X.modify("abc", |item: &mut i32| {
    ///         *item += 1;
    ///     });
    ///     let value: i32 = X.get("abc");
    ///     println!("{}", value);
    ///     assert_eq!(value, 124);
    /// });
    /// ```
    #[track_caller]
    pub fn modify<V: Any, K: Into<CowStr>, F: FnOnce(&mut V) -> R, R>(
        &self,
        key: K,
        modifier: F,
    ) -> R {
        let key = key.into();

        let location = panic::Location::caller();
        self.inner.with_borrow(|x| {
            let items = ScopeArray::new(&x.scopes[..]);
            if let Some((scope, rest)) = items.split() {
                scope.modify(key, modifier, location, rest, &x.debug)
            } else {
                panic!("{}", NO_SCOPE)
            }
        })
    }

    /// Removes an entry from the scope.
    ///
    /// # Panics #
    ///
    /// Panics if the key does not exist, or if the value associated with
    /// this key is not does not match `V`.
    ///
    /// # Examples #
    ///
    /// ```
    /// bypass::scope!(static X);
    ///
    /// X.scope(|| {
    ///     X.insert("abc", 123);
    ///     let value: i32 = X.remove("abc");
    ///     println!("{}", value);
    /// });
    /// ```
    #[track_caller]
    pub fn remove<V: Any, K: Into<CowStr>>(&self, key: K) -> V {
        let key = key.into();

        let location = panic::Location::caller();
        self.inner.with_borrow(|x| {
            let items = ScopeArray::new(&x.scopes[..]);
            if let Some((scope, rest)) = items.split() {
                scope.remove(key, location, rest, &x.debug)
            } else {
                panic!("{}", NO_SCOPE)
            }
        })
    }
}

#[doc(hidden)]
pub struct ScopeInner {
    scopes: Vec<Store>,
    debug: Box<dyn Fn(Log)>,
}

impl ScopeInner {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {
            scopes: Vec::new(),
            debug: Box::new(|log| {
                eprintln!("{}", log);
            }),
        }
    }
}

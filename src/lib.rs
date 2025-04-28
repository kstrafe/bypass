//! # Bypass: Thread-local dynamic variables #
//!
//! It is sometimes convenient to pass certain values by using an implicit
//! environment. This crate implements such an environment. We "bypass" the
//! standard way of passing values through arguments and return values, and
//! instead store our values in a thread-local key-value store.
//!
//! This effectively mimics the concept of "dynamic variables" in some other
//! languages.
//!
//! # Examples #
//!
//! ```
//! use bypass as by;
//!
//! by::scope(|| {
//!     by::insert("some name", 123);
//!     some_function();
//! });
//!
//! fn some_function() {
//!     let item: i32 = by::get("some name");
//!     println!("Fetched some name: {}", item);
//! }
//! ```
//!
//! This also allows us to pass data back by calling [insert] inside
//! `some_function`, and calling [get] or [remove] after the function call
//! completes.
//!
//! # Intended usage #
//!
//! Bypass is not intended to supplant the normal
//! argument-and-return method of passing data around. Its main purpose is to
//! provide a way to avoid tramp data - data that is only passed through a
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
//! # Panics #
//!
//! Because of its intended usage being for semi-global configuration
//! parameters, or during the construction of objects in deeply nested object
//! chains, bypass will panic
//! if a key is not found, or the type is not what we expected.
//!
//! # Logging #
//!
//! Keys can be either `&'static str` or a `String`. When strings are
//! constructed (e.g. via `format!`), it may be hard to figure out where a key
//! is inserted in a codebase. To debug this library you can set a logger via
//! [debug]. This logger is local to the current thread.
//!
//! If no logger is set then the default logger will be used that prints all
//! operations to stderr. The default logger prints the code location from where
//! each operation ([scope], [insert], [get], [remove]) is called using
//! `#[track_caller]`.
//!
//! # Dropping #
//!
//! Upon exiting a [scope], values that are part of that scope will be dropped
//! in the lexicographic order of their associated keys.
#![deny(
    missing_docs,
    rustdoc::broken_intra_doc_links,
    unused_crate_dependencies,
    unused_imports,
    unused_qualifications
)]
use scoped_tls::scoped_thread_local;
use std::{
    any::{Any, type_name},
    borrow::Cow,
    cell::{Cell, RefCell},
    collections::{BTreeMap, HashMap},
    fmt,
    panic::Location,
    rc::{Rc, Weak},
};

scoped_thread_local! {
    static SCOPE: Rc<Store>
}

type LoggerFn = Box<dyn Fn(Log)>;

fn default_logger() -> Box<dyn Fn(Log)> {
    let nesting = Cell::new(0);
    Box::new(move |log| match log {
        Log::Scope { location, begin } => {
            if begin {
                eprintln!(
                    "{:>width$}[bypass] => enter scope depth={} ({})",
                    "",
                    nesting.get(),
                    location,
                    width = nesting.get() * 2
                );
                nesting.set(nesting.get() + 1);
            } else {
                nesting.set(nesting.get() - 1);
                eprintln!(
                    "{:>width$}[bypass] <= exit scope depth={} ({})",
                    "",
                    nesting.get(),
                    location,
                    width = nesting.get() * 2
                );
            }
        }
        Log::Operation {
            location,
            operation,
            key,
            r#type,
        } => {
            eprintln!(
                "{:>width$}[bypass] {}: key={:?} type={:?} ({})",
                "",
                operation,
                key,
                r#type,
                location,
                width = nesting.get() * 2
            );
        }
    })
}

thread_local! {
    static LOGGER: RefCell<LoggerFn> = RefCell::new(default_logger());
}

/// Used in logging to denote the type of operation that is going to be
/// performed.
pub enum OperationType {
    /// The operation is [insert].
    Insert,
    /// The operation is [get].
    Get,
    /// The operation is [remove].
    Remove,
}

impl fmt::Display for OperationType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OperationType::Insert => f.write_str("insert"),
            OperationType::Get => f.write_str("get"),
            OperationType::Remove => f.write_str("remove"),
        }
    }
}

/// Describes the details of an operation to the logger.
pub enum Log<'a> {
    /// Informs the logger about a scope that has been entered or exited.
    Scope {
        /// Location of the [scope] call.
        location: &'static Location<'static>,
        /// True if the scope is entered. False if the scope is exited.
        begin: bool,
    },
    /// Informs the logger about one of the operations ([insert], [get],
    /// [remove]).
    Operation {
        /// Key used for the operation.
        key: &'a Cow<'static, str>,
        /// The operation type.
        operation: OperationType,
        /// Calling location for the operation.
        location: &'static Location<'static>,
        /// Name of the type (from [type_name] used for
        /// the value in the operation.
        r#type: &'static str,
    },
}

struct Store {
    // This is a BTreeMap to make drop order deterministic.
    items: RefCell<BTreeMap<Cow<'static, str>, Box<dyn Any>>>,
    lifts: RefCell<HashMap<Cow<'static, str>, Cow<'static, str>>>,
    parent: Weak<Store>,
}

impl Store {
    fn new(parent: Weak<Store>) -> Self {
        Self {
            items: Default::default(),
            lifts: Default::default(),
            parent,
        }
    }

    fn lift(&self, from: Cow<'static, str>) {
        assert!(
            self.lifts.borrow_mut().insert(from.clone(), from).is_none(),
            "bypass: lift already exists"
        );
    }

    fn lift_to(&self, from: Cow<'static, str>, to: Cow<'static, str>) {
        let mut binding = self.lifts.borrow_mut();
        let Some(entry) = binding.get_mut(&from) else {
            panic!("bypass: internal error");
        };

        assert!(*entry == from, "bypass: lift already mapped");

        *entry = to;
    }

    fn insert<V: Any>(&self, key: Cow<'static, str>, value: V) {
        if let Some(lift) = self.lifts.borrow().get(&key) {
            if let Some(parent) = self.parent.upgrade() {
                parent.insert(lift.clone(), value);
            } else {
                self.insert_inner(lift.clone(), value);
            }
        } else {
            self.insert_inner(key, value);
        }
    }

    fn insert_inner<V: Any>(&self, key: Cow<'static, str>, value: V) {
        assert!(
            self.items
                .borrow_mut()
                .insert(key, Box::new(value))
                .is_none()
        );
    }

    fn get<V: Any + Clone>(&self, key: Cow<'static, str>) -> V {
        if let Some(lift) = self.lifts.borrow().get(&key) {
            if let Some(parent) = self.parent.upgrade() {
                parent.get(lift.clone())
            } else {
                self.get_inner(lift.clone())
            }
        } else {
            self.get_inner(key)
        }
    }

    fn get_inner<V: Any + Clone>(&self, key: Cow<'static, str>) -> V {
        let this = self.items.borrow();
        let item: &Box<dyn Any> = this
            .get(&key)
            .unwrap_or_else(|| panic!("bypass: key not present: {:?}", key));
        (*item)
            .downcast_ref::<V>()
            .expect("bypass: type not as expected")
            .clone()
    }

    fn remove<V: Any>(&self, key: Cow<'static, str>) -> V {
        if let Some(lift) = self.lifts.borrow().get(&key) {
            if let Some(parent) = self.parent.upgrade() {
                parent.remove(lift.clone())
            } else {
                self.remove_inner(lift.clone())
            }
        } else {
            self.remove_inner(key)
        }
    }

    fn remove_inner<V: Any>(&self, key: Cow<'static, str>) -> V {
        let mut this = self.items.borrow_mut();
        let item: Box<dyn Any> = this
            .remove(&key)
            .unwrap_or_else(|| panic!("bypass: key not present: {:?}", key));
        *item.downcast::<V>().expect("bypass: type not as expected")
    }
}

/// Reference to a scope instance.
///
/// Provides a reference to a scope. Can only be created and fetched using
/// [name].
///
/// # Examples #
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     by::name("this-scope");
///
///     let scope: by::Scope = by::get("this-scope");
///     scope.insert("x", 123);
///
///     let value: i32 = by::get("x");
///     assert_eq!(value, 123);
/// });
/// ```
pub struct Scope {
    store: Weak<Store>,
}

impl Scope {
    fn new(store: Weak<Store>) -> Self {
        Self { store }
    }

    /// Inserts an item into this scope, effectively [crate::insert] but on this
    /// specific scope.
    pub fn insert<K: Into<Cow<'static, str>>, V: Any + Clone>(&self, key: K, value: V) {
        let key = key.into();
        let Some(store) = self.store.upgrade() else {
            panic!("scope no longer exists");
        };
        store.insert(key, value)
    }

    /// Gets an item from this scope, effectively [crate::get] but on this
    /// specific scope.
    pub fn get<K: Into<Cow<'static, str>>, V: Any + Clone>(&self, key: K) -> V {
        let key = key.into();
        let Some(store) = self.store.upgrade() else {
            panic!("scope no longer exists");
        };
        store.get(key)
    }

    /// Removes an item from this scope, effectively [crate::get] but on this
    /// specific scope.
    pub fn remove<K: Into<Cow<'static, str>>, V: Any>(&self, key: K) -> V {
        let key = key.into();
        let Some(store) = self.store.upgrade() else {
            panic!("scope no longer exists");
        };
        store.remove(key)
    }
}

impl Clone for Scope {
    fn clone(&self) -> Self {
        Self {
            store: self.store.clone(),
        }
    }
}

/// Creates a new scope.
///
/// A scope is a completely isolated key-value store. Subsequent [insert]s,
/// [get]s, and [remove]s will use this new scope unless [lift]ed to the parent
/// scope.
///
/// Upon returning from `work` all stored items are dropped and the previous
/// scope (if any) will be restored.
///
/// # Examples #
///
/// ```
/// use bypass as by;
/// by::scope(|| {});
/// ```
#[track_caller]
pub fn scope<F, R>(work: F) -> R
where
    F: FnOnce() -> R,
{
    let location = Location::caller();
    let info = Log::Scope {
        location,
        begin: true,
    };

    LOGGER.with_borrow(move |log| {
        log(info);
    });

    struct Defer(&'static Location<'static>);

    impl Drop for Defer {
        fn drop(&mut self) {
            let info = Log::Scope {
                location: self.0,
                begin: false,
            };

            LOGGER.with_borrow(move |log| {
                log(info);
            });
        }
    }

    let defer = Defer(location);

    let parent = if SCOPE.is_set() {
        SCOPE.with(Rc::downgrade)
    } else {
        Weak::new()
    };

    let store = Rc::new(Store::new(parent));
    let result = SCOPE.set(&store, work);

    drop(defer);

    result
}

/// Sets the thread-local logger.
///
/// It's possible to set a logging function for this crate. Each operation will
/// invoke the log function with a [Log].
///
/// If no logger is specified then the default logger is used.
///
/// # Rationale #
///
/// When we perform an operation such as `bypass::insert(format!("{}", 3 - 2),
/// ())`, it will be hard to use code searching tools to figure out where the
/// key "1" was inserted. As such, logging provides us with the code location
/// and the actual key so we can easily track down where a certain key was
/// set.
///
/// # Examples #
///
/// This is the default logger.
///
/// ```
/// use bypass::Log;
/// use std::cell::Cell;
///
/// bypass::debug({
///     let nesting = Cell::new(0);
///     Box::new(move |log: Log<'_>| match log {
///         Log::Scope { location, begin } => {
///             if begin {
///                 eprintln!(
///                     "{:>width$}[bypass] => enter scope depth={} ({})",
///                     "",
///                     nesting.get(),
///                     location,
///                     width = nesting.get() * 2
///                 );
///                 nesting.set(nesting.get() + 1);
///             } else {
///                 nesting.set(nesting.get() - 1);
///                 eprintln!(
///                     "{:>width$}[bypass] <= exit scope depth={} ({})",
///                     "",
///                     nesting.get(),
///                     location,
///                     width = nesting.get() * 2
///                 );
///             }
///         }
///         Log::Operation {
///             location,
///             operation,
///             key,
///             r#type,
///         } => {
///             eprintln!(
///                 "{:>width$}[bypass] {}: key={:?} type={:?} ({})",
///                 "",
///                 operation,
///                 key,
///                 r#type,
///                 location,
///                 width = nesting.get() * 2
///             );
///         }
///     })
/// });
/// ```
pub fn debug<F: Fn(Log) + 'static>(logger: F) {
    LOGGER.with_borrow_mut(|x| *x = Box::new(logger));
}

/// Allows setting a translation on a [lift].
///
/// # Examples #
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     let lift: by::Lift = by::lift("x");
///     lift.to("y");
///
///     // Typically written as:
///     by::lift("a").to("b");
/// });
pub struct Lift(Cow<'static, str>);

impl Lift {
    fn new(name: Cow<'static, str>) -> Self {
        Self(name)
    }

    /// Map a lift to anohter name.
    pub fn to<T: Into<Cow<'static, str>>>(self, to: T) {
        let to = to.into();
        SCOPE.with(|store| {
            store.lift_to(self.0.clone(), to);
        });
    }
}

/// Puts the scope into the scope itself.
///
/// This is useful if we want to expose the entirety of this scope to a more
/// deeply nested scope.
///
/// # Examples #
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     by::name("my-scope-name");
///     by::insert("input", 123);
///
///     by::scope(|| {
///         by::lift("my-scope-name");
///         let scope: by::Scope = by::get("my-scope-name");
///
///         let input: i32 = scope.get("input");
///         assert_eq!(input, 123);
///
///         scope.insert("output", 456);
///     });
///
///     let output: i32 = by::get("output");
///     assert_eq!(output, 456);
/// });
/// ```
///
/// ## Bypassing middleware #
///
/// Naming scopes is particularly useful when we need to access many variables
/// through middleware. We could [lift] each variable, but if there are many of
/// them, then that will quickly become cumbersome.
///
/// The following example shows how we can do this by wrapping our middleware in
/// a scope that lifts a specific name to the top-level scope. The handler again
/// scopes itself, and lifts through the middleware. This allows us to access
/// the top-level scope.
///
/// The only requirement at each scope is that we `lift` appropriately.
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     by::name("my-scope-name");
///     by::insert("some-value", 123);
///
///     by::scope(|| {
///         by::lift("something-not-used-by-middleware").to("my-scope-name");
///         middleware(handler);
///     });
///
///     let output: &str = by::get("output-some-value");
///     assert_eq!(output, "lorem ipsum");
/// });
///
/// fn middleware(handler: fn()) {
///     // Used by middleware only, these are not visible to the other scopes because they are not
///     // lifted.
///     by::insert("my-scope-name", 8);
///     by::insert("some-value", 456);
///     by::insert("output-some-value", "only used by middleware");
///     (handler)();
/// }
///
/// fn handler() {
///     by::scope(|| {
///         by::lift("my-scope-name").to("something-not-used-by-middleware");
///         let scope: by::Scope = by::get("my-scope-name");
///         let value: i32 = scope.get("some-value");
///         assert_eq!(value, 123);
///
///         scope.insert("output-some-value", "lorem ipsum");
///     });
/// }
/// ```
///
/// If we update our middleware and it now uses
/// `something-not-used-by-middleware`, then we just need to change the string
/// to something that doesn't collide. In any case, we will be notified
/// of a panic due to mismatching types. If the types do happen to coincide,
/// then it's exceedingly likely that a panic occurs due to some unexpected
/// value not being present, or some kind of double-insert.
///
/// You can still share other values into the middleware as well by [lift]ing
/// these manually.
pub fn name<A: Into<Cow<'static, str>>>(name: A) {
    SCOPE.with(|store| {
        insert(name, Scope::new(Rc::downgrade(store)));
    });
}

/// Declares a key to refer to the parent scope instead.
///
/// Each [scope] on its own is completely isolated from other scopes, unless a
/// key is lifted. Lifting makes it so that any operations ([insert], [get], and
/// [remove]) will translate their keys according to [lift] into the parent
/// scope.
///
/// # Panics #
///
/// Panics if a lift of the same name is already present.
///
/// # Examples #
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     by::insert("x", 123);
///
///     by::scope(|| {
///         by::lift("x");
///         by::lift("y");
///
///         let x: i32 = by::get("x");
///         assert_eq!(x, 123);
///
///         by::insert("y", 456);
///     });
///
///     let y: i32 = by::get("y");
///     assert_eq!(y, 456);
/// });
/// ```
///
/// Lifts can also be used to translate the keys when accessing the parent scope
/// using [Lift::to].
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     by::insert("x", 123);
///
///     by::scope(|| {
///         by::lift("y").to("x");
///
///         let y: i32 = by::get("y");
///         assert_eq!(y, 123);
///     });
/// });
/// ```
///
/// If we lift in the the top-level scope for the thread, then the key is
/// inserted into the current scope since there is no parent scope. Wrapping
/// this in a parent scope later on will not change the behavior from the
/// perspective of this scope.
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     by::lift("x");
///     by::insert("x", 123);
///     let x: i32 = by::get("x");
///     assert_eq!(x, 123);
/// });
///
/// by::scope(|| {
///     // This scope is effectively functionally identical, all operations work as expected.
///     // The only error that can occur is if the parent scope introduces "x" as well; we will
///     // then get a panic.
///     by::scope(|| {
///         by::lift("x");
///         by::insert("x", 123);
///         let x: i32 = by::get("x");
///         assert_eq!(x, 123);
///     });
/// });
/// ```
pub fn lift<A: Into<Cow<'static, str>>>(from: A) -> Lift {
    SCOPE.with(|store| {
        let from = from.into();
        store.lift(from.clone());
        Lift::new(from)
    })
}

/// Inserts a key and value into the current scope.
///
/// If a [lift] of the same key has been defined, the parent scope will be used
/// instead.
///
/// # Panics #
///
/// Panics if not called from within a [scope].
/// Panics if a key already exists then this function panics.
///
/// # Examples #
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     by::insert("x", 123);
///     by::insert(format!("abc/{}", 10), String::new());
/// });
/// ```
#[track_caller]
pub fn insert<K: Into<Cow<'static, str>>, V: Any>(key: K, value: V) {
    let key = key.into();

    let info = Log::Operation {
        key: &key,
        operation: OperationType::Insert,
        location: Location::caller(),
        r#type: type_name::<V>(),
    };

    LOGGER.with_borrow(move |log| {
        log(info);
    });

    assert!(SCOPE.is_set(), "bypass: scope has not been created");

    SCOPE.with(|store| {
        store.insert(key, value);
    });
}

/// Gets a clone of a value associated with a key from the current scope.
///
/// If a [lift] of the same key has been defined, the parent scope will be used
/// instead.
///
/// # Panics #
///
/// Panics if the key does not exist or if the value is not of the same type
/// that was stored.
///
/// # Examples #
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     by::insert("x", 123);
///
///     let value: i32 = by::get("x");
///     assert_eq!(value, 123);
/// });
/// ```
#[track_caller]
pub fn get<V: Any + Clone, K: Into<Cow<'static, str>>>(key: K) -> V {
    let key = key.into();

    let info = Log::Operation {
        key: &key,
        operation: OperationType::Get,
        location: Location::caller(),
        r#type: type_name::<V>(),
    };

    LOGGER.with_borrow(move |log| {
        log(info);
    });

    assert!(SCOPE.is_set(), "bypass: scope has not been created");

    SCOPE.with(|store| store.get(key))
}

/// Removes a value associated with a key and returns it from the current scope.
///
/// If a [lift] of the same key has been defined, the parent scope will be used
/// instead.
///
/// # Panics #
///
/// Panics if the key does not exist or if the value is not of the same type
/// that was stored.
///
/// # Examples #
///
/// ```
/// use bypass as by;
///
/// by::scope(|| {
///     by::insert("x", 123);
///
///     let value: i32 = by::remove("x");
///     assert_eq!(value, 123);
/// });
/// ```
#[track_caller]
pub fn remove<V: Any, K: Into<Cow<'static, str>>>(key: K) -> V {
    let key = key.into();

    let info = Log::Operation {
        key: &key,
        operation: OperationType::Remove,
        location: Location::caller(),
        r#type: type_name::<V>(),
    };

    LOGGER.with_borrow(move |log| {
        log(info);
    });

    assert!(SCOPE.is_set(), "bypass: scope has not been created");

    SCOPE.with(|store| store.remove(key))
}

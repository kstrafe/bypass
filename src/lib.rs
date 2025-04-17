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
//! [set_logger]. This logger is local to the current thread.
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
    collections::BTreeMap,
    fmt,
    panic::Location,
};

scoped_thread_local! {
    static SCOPE: Store
}

type LoggerFn = Box<dyn Fn(Log)>;

thread_local! {
    static LOGGER: RefCell<LoggerFn> = RefCell::new({
        let nesting = Cell::new(0);
        Box::new(move |log| {
            match log {
                Log::Scope { location, begin } => {
                    if begin {
                        eprintln!("{:>width$}{} [bypass] => enter scope depth={}", "", location, nesting.get(), width = nesting.get() * 2);
                        nesting.set(nesting.get() + 1);
                    } else {
                        nesting.set(nesting.get() - 1);
                        eprintln!("{:>width$}{} [bypass] <= exit scope depth={}", "", location, nesting.get(), width = nesting.get() * 2);
                    }

                }
                Log::Operation { location, operation, key, r#type } => {
                    eprintln!("{:>width$}{} [bypass] {}: key={:?} type={:?}", "", location, operation, key, r#type, width = nesting.get() * 2);
                }
            }
        })})
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
}

impl Store {
    fn new() -> Self {
        Self {
            items: RefCell::new(BTreeMap::new()),
        }
    }

    fn insert<V: Any>(&self, key: Cow<'static, str>, value: V) {
        self.items.borrow_mut().insert(key, Box::new(value));
    }

    fn get<V: Any + Clone>(&self, key: Cow<'static, str>) -> V {
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
        let mut this = self.items.borrow_mut();
        let item: Box<dyn Any> = this
            .remove(&key)
            .unwrap_or_else(|| panic!("bypass: key not present: {:?}", key));
        *item.downcast::<V>().expect("bypass: type not as expected")
    }
}

/// Creates a new scope.
///
/// A scope is a completely isolated key-value store. Subsequent [insert]s,
/// [get]s, and [remove]s will use this new scope.
///
/// Upon returning from `work` all stored items are dropped and the previous
/// scope (if any) will be restored.
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

    let store = Store::new();
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
/// bypass::set_logger({
///     let nesting = Cell::new(0);
///     move |log| match log {
///         Log::Scope { location, begin } => {
///             if begin {
///                 eprintln!(
///                     "{:>width$}{} [bypass] => enter scope depth={}",
///                     "",
///                     location,
///                     nesting.get(),
///                     width = nesting.get() * 2
///                 );
///                 nesting.set(nesting.get() + 1);
///             } else {
///                 nesting.set(nesting.get() - 1);
///                 eprintln!(
///                     "{:>width$}{} [bypass] <= exit scope depth={}",
///                     "",
///                     location,
///                     nesting.get(),
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
///                 "{:>width$}{} [bypass] {}: key={:?} type={:?}",
///                 "",
///                 location,
///                 operation,
///                 key,
///                 r#type,
///                 width = nesting.get() * 2
///             );
///         }
///     }
/// });
/// ```
pub fn set_logger<F: Fn(Log) + 'static>(logger: F) {
    LOGGER.with_borrow_mut(|x| *x = Box::new(logger));
}

/// Inserts an key and value into the current scope.
///
/// If a key already exists then it will overwrite the value in that key.
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

/// Gets a clone of a value associated with a key.
///
/// # Panics #
///
/// Panics if the key does not exist or if the value is not of the same type
/// that was stored.
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

/// Removes a value associated with a key and returns it.
///
/// # Panics #
///
/// Panics if the key does not exist or if the value is not of the same type
/// that was stored.
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

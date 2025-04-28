use bypass::{Log, Scope, debug, get, insert, lift, name, remove, scope};
use std::{cell::RefCell, panic, rc::Rc};

#[test]
fn logger_invocation() {
    let capture = Rc::new(RefCell::new(String::new()));
    let capture_clone = capture.clone();

    debug(move |log| {
        let mut string = capture_clone.borrow_mut();
        match log {
            Log::Scope { location, begin } => {
                *string += &format!("scope({}{})", location, begin);
            }
            Log::Operation {
                location,
                operation,
                key,
                r#type,
            } => {
                *string += &format!("oper({}{}{:?}{:?})", location, operation, key, r#type);
            }
        }
    });

    scope(|| {
        insert("a", 123);
        scope(|| {
            insert("a", 456);
            let _: i32 = get("a");
            let _: i32 = remove("a");
        });
        insert("b", "lorem ipsum");
        insert("c", 789);
    });

    assert_eq!(
        *capture.borrow(),
        "scope(tests/test.rs:26:5true)oper(tests/test.rs:27:9insert\"a\"\"i32\")scope(tests/test.rs:28:9true)oper(tests/test.rs:29:13insert\"a\"\"i32\")oper(tests/test.rs:30:26get\"a\"\"i32\")oper(tests/test.rs:31:26remove\"a\"\"i32\")scope(tests/test.rs:28:9false)oper(tests/test.rs:33:9insert\"b\"\"&str\")oper(tests/test.rs:34:9insert\"c\"\"i32\")scope(tests/test.rs:26:5false)"
    );
}

#[test]
#[should_panic(expected = "bypass: scope has not been created")]
fn no_scope_insert() {
    insert("", ());
}

#[test]
#[should_panic(expected = "bypass: scope has not been created")]
fn no_scope_get() {
    let _: () = get("");
}

#[test]
#[should_panic(expected = "bypass: scope has not been created")]
fn no_scope_remove() {
    let _: () = remove("");
}

#[test]
#[should_panic(expected = "bypass: key not present: \"\"")]
fn get_nonexistent() {
    scope(|| {
        let _: () = get("");
    });
}

#[test]
#[should_panic(expected = "bypass: key not present: \"\"")]
fn remove_nonexistent() {
    scope(|| {
        let _: () = remove("");
    });
}

#[test]
#[should_panic(expected = "bypass: type not as expected")]
fn get_type_mismatch() {
    scope(|| {
        insert("", 0i32);
        let _: u32 = get("");
    });
}

#[test]
#[should_panic(expected = "bypass: type not as expected")]
fn remove_type_mismatch() {
    scope(|| {
        insert("", 0i32);
        let _: u32 = remove("");
    });
}

#[test]
fn insert_and_get() {
    scope(|| {
        insert("a", 123);
        let a: i32 = get("a");
        assert_eq!(a, 123);

        let a2: i32 = get("a");
        assert_eq!(a2, 123);
    });
}

#[test]
fn insert_and_remove() {
    scope(|| {
        insert("a", 123);
        let a: i32 = remove("a");
        assert_eq!(a, 123);
    });
}

#[test]
#[should_panic(expected = "bypass: key not present: \"a\"")]
fn insert_and_remove_twice() {
    scope(|| {
        insert("a", 123);
        let a: i32 = remove("a");
        assert_eq!(a, 123);

        let _: i32 = remove("a");
    });
}

#[test]
fn non_clone() {
    scope(|| {
        insert("abc", String::from("lorem ipsum"));
        let string: String = remove("abc");

        assert_eq!(string, "lorem ipsum");
    });
}

#[test]
fn drop_order() {
    struct Dropper(i32, Rc<RefCell<Vec<i32>>>);

    impl Drop for Dropper {
        fn drop(&mut self) {
            self.1.borrow_mut().push(self.0);
        }
    }

    let order = Rc::new(RefCell::new(Vec::new()));

    scope(|| {
        insert("longer name", Dropper(4, order.clone()));
        insert("b", Dropper(2, order.clone()));
        insert("c", Dropper(3, order.clone()));
        insert("a", Dropper(1, order.clone()));
    });

    assert!(order.borrow().len() == 4);
    assert!(order.borrow().is_sorted());
}

#[test]
fn logger_invoked_during_panic() {
    let capture = Rc::new(RefCell::new(String::new()));
    let capture_clone = capture.clone();

    debug(move |log| {
        let mut string = capture_clone.borrow_mut();
        match log {
            Log::Scope { begin, .. } => {
                *string += if begin { "begin" } else { "end" };
            }
            Log::Operation { operation, .. } => {
                *string += &format!("-{}-", operation);
            }
        }
    });

    let result = panic::catch_unwind(|| {
        scope(|| {
            let _: u32 = remove("");
        });
    });

    let Err(error) = result else {
        panic!("Expected panic");
    };

    assert_eq!(
        *error.downcast::<String>().unwrap(),
        "bypass: key not present: \"\""
    );
    assert_eq!(*capture.borrow(), "begin-remove-end");
}

#[test]
fn scope_lift() {
    scope(|| {
        scope(|| {
            lift("x");
            insert("x", 123);
        });

        let value: i32 = get("x");
        assert_eq!(value, 123);
    });
}

#[test]
fn scope_lift_middle() {
    scope(|| {
        scope(|| {
            lift("scarecrow:intermediate").to("x");
            insert("x", "ignore");

            let value: &str = get("x");
            assert_eq!(value, "ignore");

            scope(|| {
                lift("x").to("scarecrow:intermediate");
                insert("x", 123);
            });
        });

        let value: i32 = get("x");
        assert_eq!(value, 123);
    });
}

#[test]
fn middleware_circumnavigation() {
    scope(|| {
        name("top-level");
        insert("input", "top-level string");

        scope(|| {
            lift("top-level");
            scope(|| {
                lift("top-level");
                let sc: Scope = get("top-level");
                sc.insert("x", 123);

                let string: &str = sc.get("input");
                assert_eq!(string, "top-level string");
            });
        });

        let value: i32 = get("x");
        assert_eq!(value, 123);
    });
}

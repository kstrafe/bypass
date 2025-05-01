use bypass::scope;
use std::{cell::RefCell, panic, rc::Rc};

scope!(static X);

#[test]
fn logger_invocation() {
    let capture = Rc::new(RefCell::new(String::new()));
    let capture_clone = capture.clone();

    X.debug(move |log| {
        let mut string = capture_clone.borrow_mut();
        *string += &format!("{}\n", log);
    });

    X.scope(|| {
        X.insert("a", 123);
        X.scope(|| {
            X.insert("a", 456);
            let _: i32 = X.get("a");
            let _: i32 = X.remove("a");
        });
        X.insert("b", "lorem ipsum");
        X.insert("c", 789);
    });

    assert_eq!(
        *capture.borrow(),
        concat!(
            r#"bypass: get "a" | tests/test.rs:20:28 <--- tests/test.rs:19:15"#,
            "\n",
            r#"bypass: remove "a" | tests/test.rs:21:28 <--- tests/test.rs:19:15"#,
            "\n",
        )
    );
}

#[test]
#[should_panic(expected = "bypass: scope has not been created")]
fn no_scope_insert() {
    X.insert("", ());
}

#[test]
#[should_panic(expected = "bypass: scope has not been created")]
fn no_scope_get() {
    let _: () = X.get("");
}

#[test]
#[should_panic(expected = "bypass: scope has not been created")]
fn no_scope_remove() {
    let _: () = X.remove("");
}

#[test]
#[should_panic(expected = "bypass: key not present: \"\"")]
fn get_nonexistent() {
    X.scope(|| {
        let _: () = X.get("");
    });
}

#[test]
#[should_panic(expected = "bypass: key not present: \"\"")]
fn remove_nonexistent() {
    X.scope(|| {
        let _: () = X.remove("");
    });
}

#[test]
#[should_panic(expected = "bypass: type not as expected")]
fn get_type_mismatch() {
    X.scope(|| {
        X.insert("", 0i32);
        let _: u32 = X.get("");
    });
}

#[test]
#[should_panic(expected = "bypass: type not as expected")]
fn remove_type_mismatch() {
    X.scope(|| {
        X.insert("", 0i32);
        let _: u32 = X.remove("");
    });
}

#[test]
fn insert_and_get() {
    X.scope(|| {
        X.insert("a", 123);
        let a: i32 = X.get("a");
        assert_eq!(a, 123);

        let a: i32 = X.get("a");
        assert_eq!(a, 123);
    });
}

#[test]
fn insert_and_remove() {
    X.scope(|| {
        X.insert("a", 123);
        let a: i32 = X.remove("a");
        assert_eq!(a, 123);
    });
}

#[test]
#[should_panic(expected = "bypass: key not present: \"a\"")]
fn insert_and_remove_twice() {
    X.scope(|| {
        X.insert("a", 123);
        let a: i32 = X.remove("a");
        assert_eq!(a, 123);

        let _: i32 = X.remove("a");
    });
}

#[test]
fn non_clone() {
    X.scope(|| {
        X.insert("abc", String::from("lorem ipsum"));
        let string: String = X.remove("abc");

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

    X.scope(|| {
        X.insert("longer name", Dropper(4, order.clone()));
        X.insert("b", Dropper(2, order.clone()));
        X.insert("c", Dropper(3, order.clone()));
        X.insert("a", Dropper(1, order.clone()));
    });

    assert!(order.borrow().len() == 4);
    assert!(order.borrow().is_sorted());
}

#[test]
fn scope_lift() {
    X.scope(|| {
        X.scope(|| {
            X.lift("x");
            X.insert("x", 123);
        });

        let value: i32 = X.get("x");
        assert_eq!(value, 123);
    });
}

#[test]
fn scope_lift_middle() {
    X.scope(|| {
        X.scope(|| {
            X.lift("scarecrow:intermediate").to("x");
            X.insert("x", "ignore");

            let value: &str = X.get("x");
            assert_eq!(value, "ignore");

            X.scope(|| {
                X.lift("x").to("scarecrow:intermediate");
                X.insert("x", 123);
            });
        });

        let value: i32 = X.get("x");
        assert_eq!(value, 123);
    });
}

#[test]
fn panic_across_scope() {
    X.scope(|| {
        X.insert("a", 1);
        let result = panic::catch_unwind(|| {
            X.scope(|| {
                X.insert("a", 2);
                panic!("error");
            });
        });

        let Err(error) = result else {
            panic!("not caught");
        };
        assert_eq!(*error.downcast_ref::<&str>().unwrap(), "error");

        let value: i32 = X.get("a");
        assert_eq!(value, 1);
    });
}

use crate::{
    hir::{
        def_collector::{dc_crate::CompilationError, errors::DefCollectorErrorKind},
        resolution::{errors::ResolverError, import::PathResolutionError},
    },
    tests::{assert_no_errors, get_program_errors},
};

#[test]
fn errors_once_on_unused_import_that_is_not_accessible() {
    // Tests that we don't get an "unused import" here given that the import is not accessible
    let src = r#"
        mod moo {
            struct Foo {}
        }
        use moo::Foo;
        fn main() {
            let _ = Foo {};
        }
    "#;

    let errors = get_program_errors(src);
    assert_eq!(errors.len(), 1);
    assert!(matches!(
        errors[0].0,
        CompilationError::DefinitionError(DefCollectorErrorKind::PathResolutionError(
            PathResolutionError::Private { .. }
        ))
    ));
}
#[test]
fn errors_if_type_alias_aliases_more_private_type() {
    let src = r#"
    struct Foo {}
    pub type Bar = Foo;
    pub fn no_unused_warnings(_b: Bar) {
        let _ = Foo {};
    }
    fn main() {}
    "#;

    let errors = get_program_errors(src);
    assert_eq!(errors.len(), 1);

    let CompilationError::ResolverError(ResolverError::TypeIsMorePrivateThenItem {
        typ, item, ..
    }) = &errors[0].0
    else {
        panic!("Expected an unused item error");
    };

    assert_eq!(typ, "Foo");
    assert_eq!(item, "Bar");
}

#[test]
fn errors_if_type_alias_aliases_more_private_type_in_generic() {
    let src = r#"
    pub struct Generic<T> { value: T }
    struct Foo {}
    pub type Bar = Generic<Foo>;
    pub fn no_unused_warnings(_b: Bar) {
        let _ = Foo {};
        let _ = Generic { value: 1 };
    }
    fn main() {}
    "#;

    let errors = get_program_errors(src);
    assert_eq!(errors.len(), 1);

    let CompilationError::ResolverError(ResolverError::TypeIsMorePrivateThenItem {
        typ, item, ..
    }) = &errors[0].0
    else {
        panic!("Expected an unused item error");
    };

    assert_eq!(typ, "Foo");
    assert_eq!(item, "Bar");
}

#[test]
fn errors_if_trying_to_access_public_function_inside_private_module() {
    let src = r#"
    mod foo {
        mod bar {
            pub fn baz() {}
        }
    }
    fn main() {
        foo::bar::baz()
    }
    "#;

    let errors = get_program_errors(src);
    assert_eq!(errors.len(), 1);

    let CompilationError::ResolverError(ResolverError::PathResolutionError(
        PathResolutionError::Private(ident),
    )) = &errors[0].0
    else {
        panic!("Expected a private error");
    };

    assert_eq!(ident.to_string(), "bar");
}

#[test]
fn does_not_error_if_calling_private_struct_function_from_same_struct() {
    let src = r#"
    struct Foo {

    }

    impl Foo {
        fn foo() {
            Foo::bar()
        }

        fn bar() {}
    }

    fn main() {
        let _ = Foo {};
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn does_not_error_if_calling_private_struct_function_from_same_module() {
    let src = r#"
    struct Foo;

    impl Foo {
        fn bar() -> Field {
            0
        }
    }

    fn main() {
        let _ = Foo {};
        assert_eq(Foo::bar(), 0);
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn error_when_accessing_private_struct_field() {
    let src = r#"
    mod moo {
        pub struct Foo {
            x: Field
        }
    }

    fn foo(foo: moo::Foo) -> Field {
        foo.x
    }

    fn main() {}
    "#;

    let errors = get_program_errors(src);
    assert_eq!(errors.len(), 1);

    let CompilationError::ResolverError(ResolverError::PathResolutionError(
        PathResolutionError::Private(ident),
    )) = &errors[0].0
    else {
        panic!("Expected a private error");
    };

    assert_eq!(ident.to_string(), "x");
}

#[test]
fn does_not_error_when_accessing_private_struct_field_from_nested_module() {
    let src = r#"
    struct Foo {
        x: Field
    }

    mod nested {
        fn foo(foo: super::Foo) -> Field {
            foo.x
        }
    }

    fn main() {
        let _ = Foo { x: 1 };
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn does_not_error_when_accessing_pub_crate_struct_field_from_nested_module() {
    let src = r#"
    mod moo {
        pub(crate) struct Foo {
            pub(crate) x: Field
        }
    }

    fn foo(foo: moo::Foo) -> Field {
        foo.x
    }

    fn main() {
        let _ = moo::Foo { x: 1 };
    }
    "#;
    assert_no_errors(src);
}

#[test]
fn error_when_using_private_struct_field_in_constructor() {
    let src = r#"
    mod moo {
        pub struct Foo {
            x: Field
        }
    }

    fn main() {
        let _ = moo::Foo { x: 1 };
    }
    "#;

    let errors = get_program_errors(src);
    assert_eq!(errors.len(), 1);

    let CompilationError::ResolverError(ResolverError::PathResolutionError(
        PathResolutionError::Private(ident),
    )) = &errors[0].0
    else {
        panic!("Expected a private error");
    };

    assert_eq!(ident.to_string(), "x");
}

#[test]
fn error_when_using_private_struct_field_in_struct_pattern() {
    let src = r#"
    mod moo {
        pub struct Foo {
            x: Field
        }
    }

    fn foo(foo: moo::Foo) -> Field {
        let moo::Foo { x } = foo;
        x
    }

    fn main() {
    }
    "#;

    let errors = get_program_errors(src);
    assert_eq!(errors.len(), 1);

    let CompilationError::ResolverError(ResolverError::PathResolutionError(
        PathResolutionError::Private(ident),
    )) = &errors[0].0
    else {
        panic!("Expected a private error");
    };

    assert_eq!(ident.to_string(), "x");
}

#[test]
fn does_not_error_if_referring_to_top_level_private_module_via_crate() {
    let src = r#"
    mod foo {
        pub fn bar() {}
    }

    use crate::foo::bar;

    fn main() {
        bar()
    }
    "#;
    assert_no_errors(src);
}
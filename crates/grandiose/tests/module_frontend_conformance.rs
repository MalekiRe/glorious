use grandiose::{
    ast::{ImportTree, ModuleKind, Visibility},
    lexer, parser,
};

fn parse(source: &str) -> grandiose::ast::Program {
    let tokens = lexer::lex(source).expect("module fixture lexes");
    let (program, diagnostics) = parser::parse_recovering(tokens);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    program
}

#[test]
fn external_and_inline_modules_are_structural_and_flatten_their_items() {
    let program = parse(
        r#"
        pub mod network;
        mod syntax {
            pub mod tokens;
            parse() -> i64 { 1 }
        }
        main() -> { () }
        "#,
    );

    assert_eq!(program.modules.len(), 3);
    assert_eq!(program.modules[0].name, "network");
    assert_eq!(program.modules[0].visibility, Visibility::Public);
    assert!(matches!(program.modules[0].kind, ModuleKind::External));

    assert_eq!(program.modules[1].name, "syntax");
    let ModuleKind::Inline { body } = program.modules[1].kind else {
        panic!("syntax must be an inline module")
    };
    assert!(body.start < body.end);

    assert_eq!(program.modules[2].name, "tokens");
    assert_eq!(program.modules[2].visibility, Visibility::Public);
    assert!(matches!(program.modules[2].kind, ModuleKind::External));
    assert!(body.start <= program.modules[2].span.start);
    assert!(program.modules[2].span.end <= body.end);

    // Inline bodies remain in the ordinary declaration vectors so the module
    // resolver can assign structured identities before the normalized backend.
    assert_eq!(
        program
            .functions
            .iter()
            .map(|function| function.name.as_str())
            .collect::<Vec<_>>(),
        ["parse", "main"]
    );
    let parse = &program.functions[0];
    assert_eq!(program.visibility(parse.span), Visibility::Private);
    assert_eq!(
        program.visibility(program.functions[1].span),
        Visibility::Private
    );
}

#[test]
fn use_trees_preserve_groups_globs_aliases_and_self_imports() {
    let program = parse(
        r#"
        pub use crate::syntax::{self as syntax_module, Ast, Token as Lexeme, nested::{Thing, *}};
        use super::support::helper;
        main() -> { () }
        "#,
    );

    assert_eq!(program.imports.len(), 2);
    assert_eq!(program.imports[0].visibility, Visibility::Public);
    assert_eq!(program.imports[1].visibility, Visibility::Private);

    let ImportTree::Path { segment, tree } = &program.imports[0].tree else {
        panic!("expected crate prefix")
    };
    assert_eq!(segment.name, "crate");
    let ImportTree::Path { segment, tree } = tree.as_ref() else {
        panic!("expected syntax prefix")
    };
    assert_eq!(segment.name, "syntax");
    let ImportTree::Group { items, .. } = tree.as_ref() else {
        panic!("expected grouped import")
    };
    assert_eq!(items.len(), 4);
    assert!(matches!(
        &items[0],
        ImportTree::SelfValue { alias: Some(alias), .. } if alias.name == "syntax_module"
    ));
    assert!(matches!(
        &items[1],
        ImportTree::Name { name, alias: None } if name.name == "Ast"
    ));
    assert!(matches!(
        &items[2],
        ImportTree::Name { name, alias: Some(alias) }
            if name.name == "Token" && alias.name == "Lexeme"
    ));
    assert!(matches!(
        &items[3],
        ImportTree::Path { segment, tree }
            if segment.name == "nested"
                && matches!(tree.as_ref(), ImportTree::Group { items, .. }
                    if matches!(&items[1], ImportTree::Glob { .. }))
    ));

    let ImportTree::Path { segment, .. } = &program.imports[1].tree else {
        panic!("expected super prefix")
    };
    assert_eq!(segment.name, "super");
}

#[test]
fn pub_is_contextual_and_applies_to_every_supported_item_header() {
    let program = parse(
        r#"
        pub type Count = i64;
        pub struct Pair { left: i64, right: i64 }
        pub enum Choice { One, Two }
        pub effect Signal { ping() -> i64; }
        pub trait Marker {}
        pub value() -> i64 { 1 }
        main() -> { () }
        "#,
    );

    for span in [
        program.type_aliases[0].span,
        program.structs[0].span,
        program.enums[0].span,
        program.effects[0].span,
        program.traits[0].span,
        program.functions[0].span,
    ] {
        assert_eq!(program.visibility(span), Visibility::Public);
    }
    assert_eq!(
        program.visibility(program.functions[1].span),
        Visibility::Private
    );
}

#[test]
fn malformed_module_and_use_items_recover_to_following_declarations() {
    let source = r#"
        mod missing
        use crate::{Thing as, *};
        main() -> { () }
    "#;
    let tokens = lexer::lex(source).unwrap();
    let (program, diagnostics) = parser::parse_recovering(tokens);
    assert!(diagnostics.len() >= 2, "{diagnostics:#?}");
    assert!(
        program
            .functions
            .iter()
            .any(|function| function.name == "main")
    );
}

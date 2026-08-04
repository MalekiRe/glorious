use grandiose::{
    ast::{ConstKind, GenericParamKind, GoalArgument},
    compile_source_to_bytecode, compile_source_to_phases, lexer, parser,
};
use grandiose_vm::{Value, Vm, verify};

#[test]
fn parser_preserves_ordered_supertrait_refs_arguments_bindings_and_spans() {
    let source = "trait Child<T,const Q:Quantity,const N:u32>: Parent<T,Item=T> + Quota<Q> + Index<N> {} main()->{()}";
    let program = parser::parse(lexer::lex(source).unwrap()).unwrap();
    let child = &program.traits[0];
    assert_eq!(child.supertraits.len(), 3);
    assert_eq!(
        child
            .generics
            .as_ref()
            .unwrap()
            .params
            .iter()
            .map(|parameter| parameter.kind)
            .collect::<Vec<_>>(),
        [
            GenericParamKind::Type,
            GenericParamKind::Const(ConstKind::Quantity),
            GenericParamKind::Const(ConstKind::U32),
        ]
    );
    assert_eq!(
        child
            .supertraits
            .iter()
            .map(|parent| parent.path[0].name.as_str())
            .collect::<Vec<_>>(),
        ["Parent", "Quota", "Index"]
    );
    assert_eq!(
        &source[child.supertraits[0].span.range()],
        "Parent<T,Item=T>"
    );
    assert_eq!(&source[child.supertraits[1].span.range()], "Quota<Q>");
    assert_eq!(&source[child.supertraits[2].span.range()], "Index<N>");
    assert_eq!(child.supertraits[0].bindings[0].name, "Item");
    for (parent, name) in child.supertraits.iter().zip(["T", "Q", "N"]) {
        let GoalArgument::Type(argument) = &parent.arguments[0] else {
            panic!("bare binder references remain identifier syntax in the parser AST");
        };
        assert_eq!(argument.simple_name(), Some(name));
    }
}

#[test]
fn transitive_diamond_bounds_imply_every_parent_and_execute() {
    let source = r#"
        trait Root<T> {}
        trait Left<T>: Root<T> {}
        trait Right<T>: Root<T> {}
        trait Diamond<T>: Left<T> + Right<T> {}
        struct Token { marker:i64 }
        impl Root<Text> for Token {}
        impl Left<Text> for Token {}
        impl Right<Text> for Token {}
        impl Diamond<Text> for Token {}
        root<T>(value:T)->i64 where T:Root<Text>{value;42}
        via_diamond<T>(value:T)->i64 where T:Diamond<Text>{root(value)}
        answer()->i64{via_diamond(Token{marker:1})}
        main()->{()}
    "#;
    let artifact = compile_source_to_bytecode("supertrait-diamond.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn positive_impls_require_all_parents_even_when_unreachable() {
    let cases = [
        (
            "missing-direct-parent",
            "trait Parent{} trait Child:Parent{} struct Dead{} impl Child for Dead{} main()->{()}",
        ),
        (
            "missing-diamond-parent",
            "trait Root{} trait Left:Root{} trait Right:Root{} trait Diamond:Left+Right{} struct Dead{} impl Root for Dead{} impl Left for Dead{} impl Diamond for Dead{} main()->{()}",
        ),
        (
            "missing-generic-condition",
            "trait Mark{} trait Parent<T>{} trait Child<T>:Parent<T>{} struct Box<T>{value:T} impl<T> Parent<T> for Box<T> where T:Mark{} impl<T> Child<T> for Box<T>{} main()->{()}",
        ),
    ];
    for (name, source) in cases {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G1TR001")
                    && error.span.is_some()
                    && error.message.to_ascii_lowercase().contains("supertrait")
            }),
            "{name}: {errors:#?}"
        );
    }

    let accepted = r#"
        trait Mark{}
        trait Parent<T>{}
        trait Child<T>:Parent<T>{}
        struct Token{marker:i64}
        struct Box<T>{value:T}
        struct Conditional<T>{marker:i64}
        impl Mark for Token{}
        impl<T> Parent<T> for Box<T> where T:Mark{}
        impl<T> Child<T> for Box<T> where T:Mark{}
        impl<T> Child<T> for Conditional<T> where Conditional<T>:Parent<T>{}
        main()->{()}
    "#;
    compile_source_to_bytecode("provided-supertrait.glorious", accepted).unwrap();
}

#[test]
fn type_quantity_and_u32_arguments_substitute_through_supertraits() {
    let accepted = r#"
        trait Parent<T,const Q:Quantity,const N:u32>{}
        trait Child<T,const Q:Quantity,const N:u32>:Parent<T,Q,N>{}
        struct Box<T>{value:T}
        impl<T,const Q:Quantity,const N:u32> Parent<T,Q,N> for Box<T>{}
        impl<T,const Q:Quantity,const N:u32> Child<T,Q,N> for Box<T>{}
        parent<X>(value:X)->i64 where X:Parent<Text,[0,1],4294967295>{value;42}
        child<X>(value:X)->i64 where X:Child<Text,[0,1],4294967295>{parent(value)}
        answer()->i64{child(Box{value:"ok"})}
        main()->{()}
    "#;
    let artifact =
        compile_source_to_bytecode("supertrait-const-substitution.glorious", accepted).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );

    let mismatched = r#"
        trait Parent<T,const Q:Quantity,const N:u32>{}
        trait Child<T,const Q:Quantity,const N:u32>:Parent<T,Q,N>{}
        struct Token{marker:i64}
        impl Parent<Text,[0,2],7> for Token{}
        impl Child<Text,[0,1],7> for Token{}
        main()->{()}
    "#;
    let errors =
        compile_source_to_bytecode("supertrait-const-mismatch.glorious", mismatched).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1TR001")
                && error.span.is_some()
                && error.message.to_ascii_lowercase().contains("supertrait")
        }),
        "{errors:#?}"
    );
}

#[test]
fn associated_equalities_are_required_and_lexically_implied() {
    let accepted = r#"
        trait Value<T>{type Item;}
        trait Child<T>:Value<T,Item=T>{}
        struct Good{marker:i64}
        impl Value<Text> for Good{type Item=Text;}
        impl Child<Text> for Good{}
        parent<X>(value:X)->i64 where X:Value<Text,Item=Text>{value;42}
        child<X>(value:X)->i64 where X:Child<Text>{parent(value)}
        answer()->i64{child(Good{marker:1})}
        main()->{()}
    "#;
    compile_source_to_bytecode("supertrait-associated.glorious", accepted).unwrap();

    let mismatched = r#"
        trait Value<T>{type Item;}
        trait Child<T>:Value<T,Item=T>{}
        struct Bad{marker:i64}
        impl Value<Text> for Bad{type Item=i64;}
        impl Child<Text> for Bad{}
        main()->{()}
    "#;
    let errors = compile_source_to_bytecode("supertrait-associated-mismatch.glorious", mismatched)
        .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1TR001")
                && error.span.is_some()
                && error.message.to_ascii_lowercase().contains("supertrait")
        }),
        "{errors:#?}"
    );
}

#[test]
fn implication_is_positive_forward_only_and_negative_impls_need_no_parent() {
    let accepted = r#"
        trait Parent{}
        trait Child:Parent{}
        struct No{marker:i64}
        impl !Child for No{}
        parent<T>(value:T)->T where T:Parent{value}
        child<T>(value:T)->T where T:Child{parent(value)}
        main()->{()}
    "#;
    compile_source_to_bytecode("supertrait-direction.glorious", accepted).unwrap();

    for (name, source) in [
        (
            "no-backward-positive",
            "trait Parent{} trait Child:Parent{} need<T>(v:T)->T where T:Child{v} have<T>(v:T)->T where T:Parent{need(v)} main()->{()}",
        ),
        (
            "no-forward-negative",
            "trait Parent{} trait Child:Parent{} need<T>(v:T)->T where T:!Parent{v} have<T>(v:T)->T where T:!Child{need(v)} main()->{()}",
        ),
        (
            "no-backward-negative",
            "trait Parent{} trait Child:Parent{} need<T>(v:T)->T where T:!Child{v} have<T>(v:T)->T where T:!Parent{need(v)} main()->{()}",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.span.is_some()
                    && (error.message.contains("evidence")
                        || error.message.contains("matching implementation"))
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn global_supertrait_polarity_rejects_negative_parent_but_not_negative_child() {
    let rejected = r#"
        trait Parent{}
        trait Child:Parent{}
        struct No{marker:i64}
        impl !Parent for No{}
        impl Child for No{}
        main()->{()}
    "#;
    let errors = compile_source_to_bytecode("negative-parent-of-positive-child.glorious", rejected)
        .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1TR001")
                && error.span.is_some()
                && error.message.to_ascii_lowercase().contains("supertrait")
        }),
        "{errors:#?}"
    );

    let accepted = r#"
        trait Parent{}
        trait Child:Parent{}
        struct Yes{marker:i64}
        impl Parent for Yes{}
        impl !Child for Yes{}
        main()->{()}
    "#;
    compile_source_to_bytecode("positive-parent-negative-child.glorious", accepted).unwrap();
}

#[test]
fn cycles_are_structured_and_order_independent() {
    for (name, source) in [
        ("self", "trait A:A{} main()->{()}"),
        ("mutual", "trait A:B{} trait B:A{} main()->{()}"),
        (
            "transitive",
            "trait A:B{} trait B:C{} trait C:A{} main()->{()}",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G1TR001")
                    && error.span.is_some()
                    && error.message.to_ascii_lowercase().contains("cycle")
            }),
            "{name}: {errors:#?}"
        );
    }

    let signature = |source: &str| {
        let mut errors = compile_source_to_bytecode("cycle-order.glorious", source)
            .unwrap_err()
            .into_iter()
            .map(|error| (error.code, error.title, error.message))
            .collect::<Vec<_>>();
        errors.sort();
        errors
    };
    assert_eq!(
        signature("trait A:B{} trait B:C{} trait C:A{} main()->{()}"),
        signature("main()->{()} trait C:A{} trait B:C{} trait A:B{}")
    );
}

#[test]
fn declaration_order_is_canonical_and_overlap_remains_incoherent() {
    let first = r#"
        trait Parent{}
        trait Child:Parent{}
        struct Token{marker:i64}
        impl Parent for Token{}
        impl Child for Token{}
        parent<T>(value:T)->i64 where T:Parent{value;42}
        child<T>(value:T)->i64 where T:Child{parent(value)}
        answer()->i64{child(Token{marker:1})}
        main()->{()}
    "#;
    let reordered = r#"
        main()->{()}
        answer()->i64{child(Token{marker:1})}
        child<T>(value:T)->i64 where T:Child{parent(value)}
        parent<T>(value:T)->i64 where T:Parent{value;42}
        impl Child for Token{}
        impl Parent for Token{}
        struct Token{marker:i64}
        trait Child:Parent{}
        trait Parent{}
    "#;
    let first = compile_source_to_phases("supertrait-order-a.glorious", first).unwrap();
    let reordered = compile_source_to_phases("supertrait-order-b.glorious", reordered).unwrap();
    assert_eq!(first.artifact.encode(), reordered.artifact.encode());

    let overlap = "trait Parent{} trait Child:Parent{} struct Token{} impl Parent for Token{} impl Child for Token{} impl Child for Token{} main()->{()}";
    let errors = compile_source_to_bytecode("supertrait-overlap.glorious", overlap).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.span.is_some()
                && (error.message.contains("overlap") || error.message.contains("duplicate"))
        }),
        "{errors:#?}"
    );
}

#[test]
fn intrinsic_drop_containment_accepts_zero_use_and_rejects_must_move_principals() {
    let source = r#"
        struct Erased{marker:i64}
        struct Affine{marker:i64}
        struct Unrestricted{marker:i64}
        impl Use<[0,0]> for Erased{}
        impl Use<[0,1]> for Affine{}
        impl Drop for Erased{drop(&mut self)->{self.marker;()}}
        impl Drop for Affine{drop(&mut self)->{self.marker;()}}
        impl Drop for Unrestricted{drop(&mut self)->{self.marker;()}}
        erased(value:Erased)->{()}
        affine(value:Affine)->Affine{value}
        unrestricted(value:Unrestricted)->Unrestricted{value}
        main()->{
            let erased=Erased{marker:1};
            let affine=Affine{marker:2};
            let unrestricted=Unrestricted{marker:3};
            ()
        }
    "#;
    let phases = compile_source_to_phases("drop-supertrait-containment.glorious", source).unwrap();
    let mut user_drop_glue = phases
        .artifact
        .drop_glue
        .iter()
        .filter_map(|glue| {
            let name = phases.artifact.functions[glue.function as usize]
                .name
                .as_str();
            matches!(name, "$drop$Affine" | "$drop$Erased" | "$drop$Unrestricted").then_some(name)
        })
        .collect::<Vec<_>>();
    user_drop_glue.sort_unstable();
    assert_eq!(
        user_drop_glue,
        ["$drop$Affine", "$drop$Erased", "$drop$Unrestricted"],
    );
    let parameter = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    let erased = parameter("erased");
    let affine = parameter("affine");
    let unrestricted = parameter("unrestricted");
    assert!(!phases.artifact.types[erased as usize].claimed_duplicable());
    assert!(phases.artifact.types[erased as usize].claimed_zero_use_allowed());
    assert!(!phases.artifact.types[affine as usize].claimed_duplicable());
    assert!(phases.artifact.types[affine as usize].claimed_zero_use_allowed());
    assert!(phases.artifact.types[unrestricted as usize].claimed_duplicable());
    assert!(phases.artifact.types[unrestricted as usize].claimed_zero_use_allowed());
    verify(phases.artifact).unwrap();

    for (name, interval) in [("linear-drop", "[1,1]"), ("relevant-drop", "[1,infinity]")] {
        let source = format!(
            "struct MustMove{{marker:i64}} impl Use<{interval}> for MustMove{{}} impl Drop for MustMove{{drop(&mut self)->{{()}}}} main()->{{()}}"
        );
        let errors = compile_source_to_bytecode(name, &source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G1BC002")
                    && error.span.is_some()
                    && error.message.contains("support `[0,0]`")
            }),
            "{name}: {errors:#?}"
        );
    }

    for (name, source) in [
        ("source-use-parent", "trait Bad:Use<[0,1]>{} main()->{()}"),
        ("source-drop-parent", "trait Bad:Drop{} main()->{()}"),
    ] {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G1TR001")
                    && error.span.is_some()
                    && (error.message.contains("intrinsic")
                        || error.message.contains("unsupported")
                        || error.message.contains("supertrait"))
            }),
            "{name}: {errors:#?}"
        );
    }
}

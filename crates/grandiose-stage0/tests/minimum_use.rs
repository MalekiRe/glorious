use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};
use std::collections::BTreeMap;

const TOKEN: &str = "#![no_std]\nenum Flag { Yes, No } struct Token {} impl Use<[1,1]> for Token {} fn consume(value: Token) -> i64 { let Token {} = value; 42 } ";

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("minimum-use@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"minimum-use")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), optimization.into())]),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn accepts(body: &str) {
    let source = format!("{TOKEN}{body}");
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new()
            .compile(request(&source, optimization))
            .unwrap_or_else(|error| panic!("{source}\n{error:#?}"))
            .artifact
            .unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(
            decode_and_verify_program(&artifact.canonical_bytes())
                .unwrap()
                .run_i64()
                .unwrap(),
            42
        );
    }
}

fn rejects(body: &str) {
    let source = format!("{TOKEN}{body}");
    for optimization in ["0", "2"] {
        let failure = StageZeroCompiler::new()
            .compile(request(&source, optimization))
            .expect_err(&source);
        assert!(
            failure
                .diagnostics()
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, "G5024" | "G5001" | "G5003" | "G4223")),
            "{source}\n{failure:#?}"
        );
    }
}

#[test]
fn local_labels_rejoin_bottom_typed_completion_arms() {
    for flag in ["Yes", "No"] {
        accepts(&format!("fn select(value: Token, flag: Flag) -> i64 {{
            let answer = @done: i64 {{
                handle flag {{ Flag::Yes => @done(42), Flag::No => @done(42) }}
            }};
            consume(value); answer
        }} pub fn main() -> i64 {{ select(Token {{}}, Flag::{flag}) }}"));
        accepts(&format!("fn pair(value: Token, answer: i64) -> i64 {{ consume(value); answer }}
        pub fn main() -> i64 {{
            pair(Token {{}}, @done: i64 {{
                handle Flag::{flag} {{ Flag::Yes => @done(42), Flag::No => @done(42) }}
            }})
        }}"));
        accepts(&format!("fn select(value: Token, flag: Flag) -> i64 {{
            @inner: () {{
                handle flag {{
                    Flag::Yes => @select(consume(value)),
                    Flag::No => @inner(())
                }}
            }};
            consume(value)
        }} pub fn main() -> i64 {{ select(Token {{}}, Flag::{flag}) }}"));
    }
}

#[test]
fn rejoined_bottom_typed_arms_do_not_hide_later_double_use() {
    let source = format!("{TOKEN}fn select(value: Token, flag: Flag) -> i64 {{
        @done: () {{
            handle flag {{
                Flag::Yes => {{ consume(value); @done(()) }},
                Flag::No => @done(())
            }}
        }};
        consume(value)
    }} pub fn main() -> i64 {{ select(Token {{}}, Flag::Yes) }}");
    for optimization in ["0", "2"] {
        let error = match StageZeroCompiler::new().compile(request(&source, optimization)) {
            Err(error) => error,
            Ok(_) => panic!("a rejoined completion arm must retain its move before the suffix"),
        };
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5003"), "{error:#?}");
    }
}

#[test]
fn transfer_operands_rejoin_before_the_enclosing_transfer_can_run() {
    accepts("pub fn main() -> i64 {
        let value = Token {};
        @outer: () {
            @inner: () { @outer(@inner(())) };
            consume(value);
            @outer(())
        };
        42
    }");
    accepts("fn pair(value: Token, result: i64) -> i64 { consume(value); result }
        pub fn main() -> i64 {
            pair(Token {}, @outer: i64 {
                @inner: () { @outer(@inner(())) };
                42
            })
        }");
    rejects("pub fn main() -> i64 {
        let value = Token {};
        @outer: () {
            @inner: () { @outer(@inner(())) };
            consume(value);
            @outer(())
        };
        consume(value)
    }");
}

#[test]
fn conditional_transfer_payloads_preserve_both_label_continuations() {
    for flag in ["Yes", "No"] {
        accepts(&format!("fn select(value: Token, flag: Flag) -> i64 {{
            @outer: () {{
                @inner: () {{
                    @outer(handle flag {{
                        Flag::Yes => @inner(()),
                        Flag::No => {{ consume(value); () }}
                    }})
                }};
                consume(value);
                @outer(())
            }};
            42
        }} pub fn main() -> i64 {{ select(Token {{}}, Flag::{flag}) }}"));
    }
}

#[test]
fn conditional_transfer_payloads_cannot_hide_double_use_after_rejoin() {
    let source = format!("{TOKEN}fn select(value: Token, flag: Flag) -> i64 {{
        @outer: () {{
            @inner: () {{
                @outer(handle flag {{
                    Flag::Yes => {{ consume(value); @inner(()) }},
                    Flag::No => {{ consume(value); () }}
                }})
            }};
            consume(value);
            @outer(())
        }};
        42
    }} pub fn main() -> i64 {{ select(Token {{}}, Flag::Yes) }}");
    for optimization in ["0", "2"] {
        let error = match StageZeroCompiler::new().compile(request(&source, optimization)) {
            Err(error) => error,
            Ok(_) => panic!("a conditional payload transfer must retain the moved state at its rejoin"),
        };
        assert!(error.diagnostics().iter().any(|error| error.code == "G5003"), "{error:#?}");
    }
}

#[test]
fn direct_label_continuations_keep_their_own_move_and_minimum_use_states() {
    accepts("effect Ask { ask() -> (); }
        fn select(value:Token) -> Token {
            handle Ask::ask() { Ask::ask() => @select(value) }; value
        } pub fn main() -> i64 { consume(select(Token {})) }");
    for flag in ["Yes", "No"] {
        accepts(&format!("fn select(value:Token, flag:Flag) -> Token {{
            handle flag {{ Flag::Yes => @select(value), Flag::No => () }}; value
        }} pub fn main() -> i64 {{ consume(select(Token {{}}, Flag::{flag})) }}"));
        accepts(&format!("pub fn main() -> i64 {{ let value = Token {{}};
            consume(@done: Token {{
                handle Flag::{flag} {{ Flag::Yes => @done(value), Flag::No => () }}; value
            }})
        }}"));
    }
    for (body, code) in [
        ("fn select(value:Token, flag:Flag) -> i64 {
            handle flag { Flag::Yes => @select(42), Flag::No => () }; consume(value)
        } pub fn main() -> i64 { select(Token {},Flag::Yes) }", "G5024"),
        ("fn select(value:Token, flag:Flag) -> i64 {
            @done: () { handle flag {
                Flag::Yes => { consume(value); @done(()) }, Flag::No => ()
            }; }; consume(value)
        } pub fn main() -> i64 { select(Token {},Flag::Yes) }", "G5003"),
        ("pub fn main() -> i64 { @done: i64 {
            let abandoned = Token {}; @done(42)
        }}", "G5024"),
        ("effect Ask { ask() -> (); }
        fn select(value:Token) -> i64 {
            handle Ask::ask() { Ask::ask() => @select(42) }; consume(value)
        } pub fn main() -> i64 { select(Token {}) }", "G5024"),
        ("fn pair(value:Token, number:i64) -> i64 { consume(value) + number }
        pub fn main() -> i64 { pair(Token {}, @main(42)) }", "G5024"),
    ] {
        let source = format!("{TOKEN}{body}");
        for optimization in ["0", "2"] {
            let error = match StageZeroCompiler::new().compile(request(&source, optimization)) {
                Err(error) => error,
                Ok(_) => panic!("label exit lost its ownership state: {source}"),
            };
            assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == code), "{source}\n{error:#?}");
        }
    }
}

#[test]
fn helper_label_exits_keep_their_own_move_and_minimum_use_states() {
    for flag in ["Yes", "No"] {
        accepts(&format!("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> {{ target(value) }}
            fn select(value:Token, flag:Flag) -> Token {{
                handle flag {{ Flag::Yes => leave(value,@select), Flag::No => () }};
                value
            }} pub fn main() -> i64 {{ consume(select(Token {{}},Flag::{flag})) }}"));
        accepts(&format!("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> {{ target(value) }}
            fn select(value:Token, flag:Flag) -> i64 {{
                @done: () {{
                    handle flag {{ Flag::Yes => leave((),@done), Flag::No => () }}
                }};
                consume(value)
            }} pub fn main() -> i64 {{ select(Token {{}},Flag::{flag}) }}"));
    }
    for (declaration, invocation) in [
        ("trait Leave { fn leave<T,L>(receiver:i64, value:T, target:L) -> ! where L:Label<T>; } impl Leave for i64 { fn leave<T,L>(receiver:i64, value:T, target:L) -> ! where L:Label<T> { target(value) } }", "Leave::leave(0,value,@select)"),
        ("trait Leave<U> { fn leave<T,L>(receiver:i64, value:T, target:L) -> ! where L:Label<T>; } impl<U> Leave<U> for i64 { fn leave<T,L>(receiver:i64, value:T, target:L) -> ! where L:Label<T> { target(value) } }", "Leave<i64>::leave(0,value,@select)"),
    ] {
        for flag in ["Yes", "No"] {
            accepts(&format!("{declaration} fn select(value:Token, flag:Flag) -> Token {{
                handle flag {{ Flag::Yes => {invocation}, Flag::No => () }}; value
            }} pub fn main() -> i64 {{ consume(select(Token {{}},Flag::{flag})) }}"));
        }
    }
    for flag in ["Yes", "No"] {
        accepts(&format!("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> {{ target(value) }}
            fn select<F>(value:Token, flag:Flag, observe:F) -> Token where F:Fn<(),Output=()> {{
                observe();
                handle flag {{ Flag::Yes => leave(value,@select), Flag::No => () }}; value
            }} pub fn main() -> i64 {{ consume(select(Token {{}},Flag::{flag},() -> () {{ () }})) }}"));
    }
}

#[test]
fn higher_order_captured_outer_label_exits_preserve_ownership() {
    for flag in ["Yes", "No"] {
        accepts(&format!("fn invoke<F>(task:F) -> ! where F:Fn<(),Output = ! > {{ task() }}
            fn select(value:Token, flag:Flag) -> Token {{
                handle flag {{ Flag::Yes => invoke(() -> ! {{ @select(value) }}), Flag::No => () }}; value
            }} pub fn main() -> i64 {{ consume(select(Token {{}},Flag::{flag})) }}"));
    }
}

#[test]
fn unfused_closure_label_values_are_rejected_before_lowering() {
    for body in [
        "pub fn main() -> i64 { @done: i64 { let task = () -> ! { leave(42,@done) }; task() } }",
        "fn ignore<T>(value:T) -> () {} pub fn main() -> i64 { @done: i64 { let task = () -> i64 { ignore(@done); 42 }; task() } }",
        "pub fn make() -> () -> i64 { () -> i64 { let label = @make; 42 } } pub fn main() -> i64 { 42 }",
    ] {
        let source = format!("{TOKEN} fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> {{ target(value) }} {body}");
        for optimization in ["0", "2"] {
            let failure = StageZeroCompiler::new().compile(request(&source, optimization))
                .expect_err("an unfused callable cannot retain an outer label value");
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4179"), "{source}\n{failure:#?}");
            assert!(!failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G6001"), "label lifetime must be checked before CFG lowering: {failure:#?}");
        }
    }
    accepts("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
        pub fn main() -> i64 { let task = () -> i64 { @done: i64 { leave(42,@done) } }; task() }");
}

#[test]
fn owned_label_aliases_cannot_escape_in_callable_environments() {
    for initializer in ["@make", "(@make,)", "keep(@make)", "Carrier { label: @make }"] {
        let source = format!("{TOKEN}
            struct Carrier<T> {{ label: T }}
            fn keep<T>(value:T) -> T {{ value }}
            pub fn make() -> () -> i64 {{
                let target = {initializer};
                move (target) {{ let retained = target; 42 }}
            }}
            pub fn main() -> i64 {{ 42 }}");
        for optimization in ["0", "2"] {
            let failure = match StageZeroCompiler::new().compile(request(&source, optimization)) {
                Err(failure) => failure,
                Ok(_) => panic!("an exported callable cannot carry its factory's expired label: {source}"),
            };
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4179"), "{source}\n{failure:#?}");
        }
    }
    accepts("fn keep<T>(value:T) -> T { value }
        fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
        pub fn main() -> i64 { @done: i64 { let target=keep(@done); leave(42,target) } }");
    accepts("pub fn make() -> () -> i64 {
        let target = () -> i64 { 42 }; move (target) { target() }
    } pub fn main() -> i64 { make()() }");
    accepts("pub fn main() -> i64 {
        let task = @done: () -> i64 { let discarded = @done; () -> i64 { 42 } }; task()
    }");
}

#[test]
fn unknown_callback_prefix_preserves_later_label_capture_dependencies() {
    let source = format!("{TOKEN}
        pub fn make<F>(observe:F) -> () -> i64 where F:Fn<(),Output=()> {{
            observe(); let target = @make;
            move (target) {{ let retained = target; 42 }}
        }} pub fn main() -> i64 {{ 42 }}");
    for optimization in ["0", "2"] {
        let failure = match StageZeroCompiler::new().compile(request(&source, optimization)) {
            Err(failure) => failure,
            Ok(_) => panic!("an unknown prefix cannot erase a subsequently formed label capture"),
        };
        assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4179"), "{failure:#?}");
    }
}

#[test]
fn label_alias_captures_cannot_cross_a_local_or_outer_rejoin() {
    for body in [
        "let task = @inner: () -> i64 {
            let target = @inner; move (target) { let retained = target; 42 }
        }; task()",
        "let task = @outer: () -> i64 {
            @inner: () { let target = @inner;
                @outer(move (target) { let retained = target; 42 })
            }; () -> i64 { 42 }
        }; task()",
    ] {
        let source = format!("{TOKEN} pub fn main() -> i64 {{ {body} }}");
        for optimization in ["0", "2"] {
            let failure = match StageZeroCompiler::new().compile(request(&source, optimization)) {
                Err(failure) => failure,
                Ok(_) => panic!("a callable cannot rejoin beyond a captured label's scope: {source}"),
            };
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4179"), "{source}\n{failure:#?}");
        }
    }
}

#[test]
fn labels_returned_from_captured_inputs_keep_their_scope_dependency() {
  for returned in ["target", "(target,)"] {
    let source = format!("{TOKEN}
        pub fn make() -> () -> i64 {{
            let target = @make;
            let read = move (target) {{ {returned} }};
            let alias = read();
            move (alias) {{ let retained = alias; 42 }}
        }} pub fn main() -> i64 {{ 42 }}");
    for optimization in ["0", "2"] {
        let failure = match StageZeroCompiler::new().compile(request(&source, optimization)) {
            Err(failure) => failure,
            Ok(_) => panic!("returning an owned captured input cannot erase its label scope"),
        };
        assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4179"), "{failure:#?}");
    }
  }
  accepts("pub fn main() -> i64 {
      let target = () -> i64 { 42 };
      let read = move (target) { target }; let task = read(); task()
  }");
}

#[test]
fn unknown_prefix_cannot_erase_a_later_captured_label_return() {
  for returned in ["target", "(target,)"] {
    let source = format!("{TOKEN}
        pub fn make<F>(observe:F) -> () -> i64 where F:Fn<(),Output=()> {{
            observe();
            let target = @make;
            let read = move (target) {{ {returned} }};
            let alias = read();
            move (alias) {{ let retained = alias; 42 }}
        }} pub fn main() -> i64 {{ 42 }}");
    for optimization in ["0", "2"] {
        let failure = match StageZeroCompiler::new().compile(request(&source, optimization)) {
            Err(failure) => failure,
            Ok(_) => panic!("an unresolved prefix cannot erase a later captured return's label scope"),
        };
        assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4179"), "{failure:#?}");
    }
  }
  accepts("fn observe() {}
      fn make<F>(observe:F) -> () -> i64 where F:Fn<(),Output=()> {
          observe(); let target = () -> i64 { 42 };
          let read = move (target) { target }; read()
      }
      pub fn main() -> i64 { make(observe)() }");
}

#[test]
fn ordinary_bottom_returning_functions_do_not_have_generative_label_authority() {
    let source = format!("{TOKEN}
        fn halt(value:i64) -> ! {{ halt(value) }}
        fn require_label<L>(target:L) -> i64 where L:Label<i64> {{ 42 }}
        pub fn main() -> i64 {{ require_label(halt) }}");
    for optimization in ["0", "2"] {
        let failure = match StageZeroCompiler::new().compile(request(&source, optimization)) {
            Err(failure) => failure,
            Ok(_) => panic!("a bottom-returning function is not a generative lexical label"),
        };
        assert!(failure.diagnostics().iter().any(|diagnostic|
            diagnostic.code == "G4143"), "{failure:#?}");
    }
    accepts("fn require_label<L>(target:L) -> i64 where L:Label<i64> { 42 }
        pub fn main() -> i64 { require_label(@main) }");
}

#[test]
fn distinct_label_brands_cannot_satisfy_one_invariant_generic_type() {
    let source = format!("{TOKEN}
        fn same<L>(a:L,b:L) -> i64 where L:Label<i64> {{ 42 }}
        pub fn main() -> i64 {{ @outer: i64 {{ @inner: i64 {{ same(@outer,@inner) }} }} }}");
    for optimization in ["0", "2"] {
        let failure = match StageZeroCompiler::new().compile(request(&source, optimization)) {
            Err(failure) => failure,
            Ok(_) => panic!("different lexical brands cannot become the same L merely because their payload types agree"),
        };
        assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4107"), "{failure:#?}");
    }
    accepts("fn keep<T>(value:T) -> T { value }
        fn same<L>(a:L,b:L) -> i64 where L:Label<i64> { 42 }
        fn duplicate<L>(target:L) -> i64 where L:Label<i64> { same(target,target) }
        pub fn main() -> i64 { let target = keep(@main); duplicate(target) }");
}

#[test]
fn generative_labels_are_not_addressable_values() {
    for borrowed in ["&target", "&mut target"] {
      for program in [
        format!("pub fn main() -> i64 {{ let mut target = @main; let reference = {borrowed}; 42 }}"),
        format!("fn borrow<T>(value:T) -> T {{ let mut target = value; {{ let reference = {borrowed}; }}; target }}
            pub fn main() -> i64 {{ let target = borrow(@main); 42 }}"),
      ] {
        let source = format!("{TOKEN} {program}");
        for optimization in ["0", "2"] {
            let failure = match StageZeroCompiler::new().compile(request(&source, optimization)) {
                Err(failure) => failure,
                Ok(_) => panic!("a proof-only generative label has no addressable resident: {source}"),
            };
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4179"), "{failure:#?}");
        }
      }
      accepts(&format!("fn borrow<T>(value:T) -> T {{ let mut target = value; {{ let reference = {borrowed}; }}; target }}
          pub fn main() -> i64 {{ borrow(42) }}"));
    }
}

#[test]
fn structural_callable_parameters_cannot_erase_label_addressability() {
    for borrowed in ["&target", "&mut target"] {
      for invocation in ["borrow(@main)", "let destination = keep(@main); borrow(destination)",
          "let destination = @main; let relay = move (destination) { borrow(destination) }; relay()"] {
        let source = format!("{TOKEN}
            fn keep<T>(value:T) -> T {{ value }}
            fn borrow(value:(i64) -> !) -> ! {{ let mut target = value; {{ let reference = {borrowed}; }}; target(42) }}
            pub fn main() -> i64 {{ {invocation} }}");
        for optimization in ["0", "2"] {
            let failure = match StageZeroCompiler::new().compile(request(&source, optimization)) {
                Err(failure) => failure,
                Ok(_) => panic!("a structural Fn parameter cannot give a generative label a resident address: {source}"),
            };
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4179"), "{failure:#?}");
        }
      }
      accepts(&format!("fn borrow(value:(i64) -> !) -> ! {{ let mut target = value; {{ let reference = {borrowed}; }}; target(42) }}
          pub fn main() -> i64 {{ 42 }}"));
      let source = format!("{TOKEN}
          fn borrow(value:(i64) -> !) -> ! {{ let mut target = value; {{ let reference = {borrowed}; }}; target(42) }}
          pub fn caller<F>(observe:F) -> i64 where F:Fn<(),Output=()> {{ observe(); borrow(@caller) }}
          pub fn main() -> i64 {{ 42 }}");
      for optimization in ["0", "2"] {
          let failure = StageZeroCompiler::new().compile(request(&source, optimization))
              .expect_err("unknown prefixes cannot erase a later observed label address");
          assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4179"), "{failure:#?}");
      }
    }
    accepts("fn invoke(value:(i64) -> !) -> ! { value(42) }
        pub fn main() -> i64 { invoke(@main) }");
}

#[test]
fn resolved_local_label_aliases_execute_without_indirect_label_calls() {
    for invocation in ["let destination = @main; destination(42)",
        "keep(@main)(42)", "let (destination,) = (@main,); destination(42)"] {
        let source = format!("{TOKEN} fn keep<T>(value:T) -> T {{ value }}
            pub fn main() -> i64 {{ {invocation} }}");
        for optimization in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(request(&source, optimization))
                .unwrap_or_else(|error| panic!("{source}: {error:#?}")).artifact.unwrap();
            let candidate = grandiose_stage0::decode_program(&artifact.canonical_bytes()).unwrap();
            assert!(!candidate.functions.values().flat_map(|function| &function.instructions)
                .any(|instruction| matches!(instruction, grandiose_stage0::VmInstruction::CallIndirectOwned { .. })),
                "a resolved local label invocation must use a direct transfer: {source}");
            assert!(!candidate.functions.values().flat_map(|function| &function.instructions)
                .any(|instruction| matches!(instruction, grandiose_stage0::VmInstruction::MakeLabel { .. })),
                "resolved label proof carriers must erase before emission: {source}");
            assert_eq!(artifact.run_i64().unwrap_or_else(|error| panic!("{source}: {error:?}\n{candidate:#?}")), 42);
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        }
    }
}

#[test]
fn erased_label_products_preserve_resident_values_and_forwarding_abis() {
    for body in [
        "let ((destination,), value) = keep(((@main,),42)); destination(value)",
        "let destination = handle Flag::Yes { Flag::Yes => keep(@main), Flag::No => @main }; destination(42)",
        "let value = 42; let reader = move (value) { value }; let (destination, callback) = keep((@main,reader)); destination(callback())",
        "let (destination, token) = keep((@main,Token {})); destination(consume(token))",
        "let [destination] = fixed([@main]); destination(42)",
        "@outer:i64 { let value = @inner:i64 { let (outer,inner) = keep((@outer,@inner)); outer(42) }; 0 }",
    ] {
        let source = format!("{TOKEN} fn keep<T>(value:T) -> T {{ value }}
            fn fixed<T>(value:[T;1]) -> [T;1] {{ value }}
            pub fn main() -> i64 {{ {body} }}");
        for optimization in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(request(&source, optimization))
                .unwrap_or_else(|error| panic!("{source}: {error:#?}")).artifact.unwrap();
            let candidate = grandiose_stage0::decode_program(&artifact.canonical_bytes()).unwrap();
            assert!(!candidate.functions.values().flat_map(|function| &function.instructions)
                .any(|instruction| matches!(instruction, grandiose_stage0::VmInstruction::MakeLabel { .. })), "{source}");
            assert_eq!(artifact.run_i64().unwrap_or_else(|error| panic!("{source}: {error:#?}")), 42);
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        }
    }
}

#[test]
fn erased_label_products_keep_resident_cleanup_before_rejoin() {
    accepts("struct Probe<'a> { count: &'a mut i64 }
        impl<'a> Use<[0,1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = 1; } }
        fn keep<T>(value:T) -> T { value }
        pub fn main() -> i64 {
            let mut count:i64 = 0;
            let answer = @done:i64 {
                let (destination, probe) = keep((@done,Probe { count: &mut count }));
                destination(42)
            };
            handle count { 1 => answer, _ => 0 }
        }");
}

#[test]
fn helper_label_rejoins_cannot_hide_double_use() {
    let source = format!("{TOKEN}
        fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> {{ target(value) }}
        fn select(value:Token, flag:Flag) -> i64 {{
            @done: () {{ handle flag {{
                Flag::Yes => {{ consume(value); leave((),@done) }}, Flag::No => ()
            }} }};
            consume(value)
        }} pub fn main() -> i64 {{ select(Token {{}},Flag::Yes) }}");
    for optimization in ["0", "2"] {
        let error = StageZeroCompiler::new().compile(request(&source, optimization))
            .expect_err("a helper's rejoined move must reach the suffix");
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5003"), "{error:#?}");
    }
}

#[test]
fn helper_label_exits_preserve_protected_operands_and_reference_payloads() {
    accepts("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
        fn pair(value:Token, result:i64) -> i64 { consume(value); result }
        pub fn main() -> i64 { pair(Token {}, @done: i64 { leave(42,@done) }) }");
    rejects("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
        fn pair(value:Token, result:i64) -> i64 { consume(value); result }
        pub fn main() -> i64 { pair(Token {}, leave(42,@main)) }");
    accepts("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
        fn forward<'a>(value:&'a i64) -> &'a i64 { leave(value,@forward) }
        pub fn main() -> i64 { let value:i64=42; *forward(&value) }");
}

#[test]
fn helper_label_exits_cannot_return_a_local_reference_payload() {
  for main in ["*bad()", "42"] {
    let source = format!("{TOKEN}
        fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> {{ target(value) }}
        pub fn bad() -> &i64 {{ let value:i64=42; leave(&value,@bad) }}
        pub fn main() -> i64 {{ {main} }}");
    for optimization in ["0", "2"] {
        let error = match StageZeroCompiler::new().compile(request(&source, optimization)) {
            Err(error) => error,
            Ok(_) => panic!("a helper cannot erase an escaping local reference: main={main}"),
        };
        assert!(error.diagnostics().iter().any(|diagnostic|
            matches!(diagnostic.code, "G5013" | "G5014" | "G5017" | "G5022" | "G5023")), "{error:#?}");
    }
  }
}

#[test]
fn rejoined_helper_reference_payloads_keep_their_backing_loan() {
    let source = format!("{TOKEN}
        fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> {{ target(value) }}
        pub fn main() -> i64 {{ let mut value:i64=41;
            let reference = @done: &i64 {{ leave(&value,@done) }};
            value=42; *reference
        }}");
    for optimization in ["0", "2"] {
        let error = match StageZeroCompiler::new().compile(request(&source, optimization)) {
            Err(error) => error,
            Ok(_) => panic!("a rejoined reference must retain its source loan"),
        };
        assert!(error.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5007" | "G5013" | "G5017" | "G5022" | "G5023")), "{error:#?}");
    }
}

#[test]
fn rejoined_helper_reference_payloads_allow_valid_uses() {
    for exit in ["leave(&value,@done)", "@done(&value)"] {
        accepts(&format!("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> {{ target(value) }}
            pub fn main() -> i64 {{ let mut value:i64=41;
                {{ let reference = @done: &i64 {{ {exit} }}; *reference; }};
                value=42; value
            }}"));
    }
    accepts("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
        pub fn main() -> i64 { let mut value:i64=41;
            { let reference = @done: &mut i64 { leave(&mut value,@done) }; *reference=42; };
            value
        }");
    accepts("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
        pub fn main() -> i64 { let value:i64=42;
            let (reference,number) = @done: (&i64,i64) { leave((&value,2),@done) };
            number; *reference
        }");
    for flag in ["Yes", "No"] {
        accepts(&format!("fn leave<T,L>(value:T, target:L) -> ! where L:Label<T> {{ target(value) }}
            pub fn main() -> i64 {{ let value:i64=42;
                let reference = @done: &i64 {{ handle Flag::{flag} {{
                    Flag::Yes => leave(&value,@done), Flag::No => &value
                }} }}; *reference
            }}"));
    }
}

#[test]
fn named_linear_owners_transfer_or_deconstruct_without_byte_residents() {
    accepts("pub fn main() -> i64 { let value = Token {}; consume(value) }");
    accepts(
        "fn forward<T>(value: T) -> T { value } pub fn main() -> i64 { let value = forward(Token {}); consume(value) }",
    );
    accepts(
        "struct Wrapper { value: i64 } impl Use<[1,1]> for Wrapper {} pub fn main() -> i64 { let owner = Wrapper { value: 42 }; let Wrapper { value: result } = owner; result }",
    );
    accepts(
        "pub fn main() -> i64 { let value = Token {}; { let value = Token {}; consume(value); }; consume(value) }",
    );
    accepts(
        "pub fn main() -> i64 { let [left,right]: [Token;2] = [Token {},Token {}]; consume(left); consume(right) }",
    );
    accepts(
        "enum Maybe { None, Some(Token) } fn finish(value: Maybe) -> i64 { handle value { Maybe::None => 42, Maybe::Some(value) => consume(value) } } pub fn main() -> i64 { finish(Maybe::None) }",
    );
}

#[test]
fn returned_generic_closures_transfer_their_owned_captures() {
    accepts(
        "fn capture<T>(value: T) -> () -> T { () -> T { value } } pub fn main() -> i64 { consume(capture(Token {})()) }",
    );
    accepts(
        "fn capture<T>(value: T) -> () -> () -> T { () -> () -> T { () -> T { value } } } pub fn main() -> i64 { consume(capture(Token {})()()) }",
    );
    accepts(
        "trait Family { type Item; } impl Family for i64 { type Item = Token; } fn capture<T>(value: <T as Family>::Item) -> () -> <T as Family>::Item where T: Family { () -> <T as Family>::Item { value } } pub fn main() -> i64 { consume(capture<i64>(Token {})()) }",
    );
    accepts(
        "trait Fn {} impl Fn for Token {} fn capture<T>(value: T) -> () -> T where T: Fn { () -> T { value } } pub fn main() -> i64 { consume(capture(Token {})()) }",
    );
    rejects(
        "fn capture<T>(value: T) -> () -> T { let take = () -> T { value }; let discarded = value; take } pub fn main() -> i64 { consume(capture(Token {})()) }",
    );
}

#[test]
fn each_scope_and_branch_retains_its_own_minimum_use_debt() {
    accepts(
        "fn choose(value: Token, flag: Flag) -> i64 { handle flag { Flag::Yes => consume(value), Flag::No => consume(value) } } pub fn main() -> i64 { choose(Token {},Flag::Yes) }",
    );
    accepts(
        "fn choose(value: Token, flag: Flag) -> i64 { handle flag { Flag::Yes => (), Flag::No => () }; consume(value) } pub fn main() -> i64 { choose(Token {},Flag::Yes) }",
    );
    rejects(
        "fn choose(value: Token, flag: Flag) -> i64 { handle flag { Flag::Yes => consume(value), Flag::No => 42 } } pub fn main() -> i64 { choose(Token {},Flag::Yes) }",
    );
    rejects(
        "pub fn main() -> i64 { let value = Token {}; { let value = Token {}; 0 }; consume(value) }",
    );
    rejects("pub fn main() -> i64 { let value = Token {}; 42 }");
    rejects("pub fn main() -> i64 { let values: [Token;2] = [Token {},Token {}]; 42 }");
}

#[test]
fn borrowed_closure_captures_do_not_duplicate_the_referents_minimum_use_debt() {
    accepts("fn observe(value: &Token) -> i64 { 42 }
        pub fn main() -> i64 { let value = Token {}; let read = () -> i64 { observe(&value) }; read(); consume(value) }");
    accepts("fn observe(value: &mut Token) -> i64 { 42 }
        pub fn main() -> i64 { let mut value = Token {}; let read = () -> i64 { observe(&mut value) }; read(); consume(value) }");
    rejects("fn observe(value: &Token) -> i64 { 42 }
        pub fn main() -> i64 { let value = Token {}; let read = () -> i64 { observe(&value) }; read() }");
    rejects("fn observe(value: &mut Token) -> i64 { 42 }
        pub fn main() -> i64 { let mut value = Token {}; let read = () -> i64 { observe(&mut value) }; read() }");
}

#[test]
fn reads_helpers_overwrites_and_wildcards_cannot_erase_linear_owners() {
    rejects("pub fn main() -> i64 { let value = Token {}; let borrowed = &value; 42 }");
    rejects("pub fn main() -> i64 { let mut value = Token {}; value = Token {}; consume(value) }");
    rejects("pub fn main() -> i64 { let value = Token {}; value; 42 }");
    rejects("fn erase<T>(value: T) -> i64 { 42 } pub fn main() -> i64 { erase(Token {}) }");
    rejects(
        "fn forward<T>(value: T) -> T { value } pub fn main() -> i64 { forward(Token {}); 42 }",
    );
    rejects("fn make() -> Token { Token {} } pub fn main() -> i64 { handle make() { _ => 42 } }");
    rejects(
        "pub fn main() -> i64 { let value = Token {}; let Token {} = value; let Token {} = value; 42 }",
    );
    rejects(
        "enum Maybe { None, Some(Token) } pub fn main() -> i64 { let value = Maybe::None; 42 }",
    );
}

#[test]
fn affine_and_proven_zero_use_generics_remain_discardable() {
    accepts(
        "struct Affine {} impl Use<[0,1]> for Affine {} pub fn main() -> i64 { let unused = Affine {}; let empty: [Token;0] = []; 42 }",
    );
    accepts(
        "fn discard<T>(value: T) -> i64 where T: Use<[0,1]> { 42 } pub fn main() -> i64 { discard(42) }",
    );
    accepts(
        "struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {} impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = 42; } } pub fn main() -> i64 { let mut count = 41; { let value = Probe { count: &mut count }; () }; count }",
    );
}

#[test]
fn partial_moves_and_constructor_shells_keep_independent_obligations() {
    accepts(
        "struct Pair { left: Token, right: Token } pub fn main() -> i64 { let pair = Pair { left: Token {}, right: Token {} }; consume(move pair.left); consume(move pair.right) }",
    );
    accepts(
        "pub fn main() -> i64 { let mut value = Token {}; consume(move value); value = Token {}; consume(value) }",
    );
    rejects(
        "struct Pair { left: Token, right: Token } pub fn main() -> i64 { let pair = Pair { left: Token {}, right: Token {} }; consume(move pair.left); 42 }",
    );
    rejects(
        "struct Wrapper { value: i64 } impl Use<[1,1]> for Wrapper {} fn finish(value: Wrapper) -> i64 { let Wrapper { value: result } = value; result } pub fn main() -> i64 { let owner = Wrapper { value: 42 }; let Wrapper { value: result } = owner; finish(owner) }",
    );
    rejects(
        "struct Pair { left: Token, right: Token } pub fn main() -> i64 { let pair = Pair { left: Token {}, right: Token {} }; handle pair { Pair { left: item, right: _ } => consume(item) } }",
    );
}

#[test]
fn cleanup_bearing_nonlocal_exits_do_not_fabricate_positive_uses() {
    accepts(
        "pub fn main() -> i64 { label done { let value = Token {}; consume(value); transfer done 42 } }",
    );
    accepts(
        "pub fn main() -> i64 { let value = Token {}; label done { transfer done 42 }; consume(value) }",
    );
    rejects("pub fn main() -> i64 { label done { let value = Token {}; transfer done 42 } }");
    rejects(
        "effect Stop { stop() -> !; } pub fn main() -> i64 { handle { let value = Token {}; Stop::stop() } { Stop::stop() => 42 } }",
    );
    accepts(
        "effect Stop { stop(value: Token) -> !; } pub fn main() -> i64 { let payload = Token {}; handle Stop::stop(payload) { Stop::stop(value) => consume(value) } }",
    );
    rejects(
        "effect Stop { stop(value: Token) -> !; } pub fn main() -> i64 { let payload = Token {}; handle Stop::stop(payload) { Stop::stop(_) => 42 } }",
    );
    rejects(
        "trait Fn {} impl Fn for Token {} fn ignore<T>(value: T) -> i64 where T: Fn { 42 } pub fn main() -> i64 { ignore(Token {}) }",
    );
    rejects(
        "trait Label {} impl Label for Token {} fn ignore<T>(value: T) -> i64 where T: Label { 42 } pub fn main() -> i64 { ignore(Token {}) }",
    );
}

#[test]
fn canceling_a_continuation_cannot_destroy_its_linear_residents() {
    rejects(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Token {}; Ask::ask(); consume(value) } { Ask::ask() with _ => 42 } }",
    );
    accepts(
        "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Token {}; Ask::ask(); consume(value) } { Ask::ask() => 0 } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { let value = Token {}; handle { Ask::ask(); consume(value) } { Ask::ask() with _ => 42 } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } fn ask() -> i64 / Ask { Ask::ask() } pub fn main() -> i64 { handle { let value = Token {}; ask(); consume(value) } { Ask::ask() with _ => 42 } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } fn pair(value: Token, answer: i64) -> i64 { consume(value) } pub fn main() -> i64 { handle { let value = Token {}; pair(value, Ask::ask()) } { Ask::ask() with _ => 42 } }",
    );
    rejects(
        "pub fn main() -> i64 { label done { let value = Token {}; let pair = (value, transfer done 42); 42 } }",
    );
    accepts(
        "effect Ask { [0,1] ask() -> i64; } fn pair(value: Token, answer: i64) -> i64 { consume(value) } pub fn main() -> i64 { pair(Token {}, handle Ask::ask() { Ask::ask() with _ => 0 }) }",
    );
    accepts(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { let value = Token {}; handle Ask::ask() { Ask::ask() with _ => consume(value) } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { let value = Token {}; let flag = Flag::No; handle { handle flag { Flag::Yes => Ask::ask(), Flag::No => 0 } } { Ask::ask() with _ => consume(value) } }",
    );
    rejects(
        "effect Ask { [0,1] ask() -> i64; } fn invoke<F>(body: F) -> i64 / Ask where F: Fn<(), Output = i64, Effects = {Ask}> { let value = Token {}; body(); consume(value) } pub fn main() -> i64 { handle invoke(() -> i64 / Ask { Ask::ask() }) { Ask::ask() with _ => 42 } }",
    );
    accepts(
        "fn invoke<F>(body: F) -> i64 where F: Fn<(), Output = i64> { let value = Token {}; body(); consume(value) } pub fn main() -> i64 { invoke(() -> i64 { 0 }) }",
    );
    accepts(
        "effect Ask { [0,1] ask(answer: i64) -> i64; } fn ask(answer: i64) -> i64 / Ask { Ask::ask(answer) } pub fn main() -> i64 { handle { let value = Token {}; label done { ask(transfer done 0) }; consume(value) } { Ask::ask(answer) with _ => 0 } }",
    );
    accepts(
        "effect Ask { [0,1] ask(answer: i64) -> i64; } pub fn main() -> i64 { handle { let value = Token {}; label done { Ask::ask(transfer done 0) }; consume(value) } { Ask::ask(answer) with _ => 0 } }",
    );
}

#[test]
fn only_manifest_bound_abort_has_a_no_cleanup_disposition() {
    let source = format!(
        "{TOKEN} pub fn halt_machine() -> !; pub fn main() -> i64 {{ let value = Token {{}}; halt_machine() }}"
    );
    for optimization in ["0", "2"] {
        let mut request = request(&source, optimization);
        request.runtime_manifest = Some(grandiose_stage0::RuntimeManifestInput {
            standard_library: request.root_package.clone(),
            host_imports: vec![],
            selectors: vec![grandiose_stage0::PrimitiveSelector {
                role: grandiose_stage0::PrimitiveRole::Abort,
                module_path: "crate".into(),
                name: "halt_machine".into(),
            }],
        });
        let artifact = StageZeroCompiler::new()
            .compile(request)
            .unwrap()
            .artifact
            .unwrap();
        assert!(matches!(
            artifact.run_i64(),
            Err(grandiose_stage0::VmArtifactError::Trap)
        ));
        assert!(matches!(
            decode_and_verify_program(&artifact.canonical_bytes())
                .unwrap()
                .run_i64(),
            Err(grandiose_stage0::VmArtifactError::Trap)
        ));
    }
    rejects(
        "fn __g1_abort() -> i64 { 42 } pub fn main() -> i64 { let value = Token {}; __g1_abort() }",
    );
}

#[test]
fn failed_library_insertion_returns_the_exact_linear_input() {
    let source = r#"use std::*;
        struct Token {} impl Use<[1,1]> for Token {}
        fn finish(value: Vec<Token>) -> i64 {
            handle Vec::finish_empty(value) {
                Result::Ok(_) => 42,
                Result::Err(value) => finish(value),
            }
        }
        pub fn main() -> i64 {
            let mut values: Vec<Token> = Vec::new();
            let result = Vec::insert(&mut values, 1, Token {});
            handle result {
                Result::Err(Rejected { value: Token {}, error: BoundsError { index: index, length: length } }) => {
                    finish(values) + as<i64>(index) + as<i64>(length) - 1
                },
                Result::Ok(_) => finish(values),
            }
        }
    "#;
    for optimization in ["0", "2"] {
        let mut request = request(source, optimization);
        let library = grandiose_stage0::service::STANDARD_LIBRARY_FRAGMENTS
            .iter()
            .filter(|(path, _)| {
                matches!(
                    *path,
                    "src/lib.glorious" | "src/foundation.glorious" | "src/memory.glorious"
                )
            })
            .map(|(_, source)| *source)
            .collect::<Vec<_>>()
            .join("\n");
        request.sources.push(SourceInput::new(
            PackageKey("std@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            library.as_bytes(),
        ));
        let artifact = StageZeroCompiler::new()
            .compile(request)
            .unwrap()
            .artifact
            .unwrap();
        // SAFETY: locally compiled library source owns its raw storage contract.
        assert_eq!(
            unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(),
            42
        );
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        assert_eq!(
            unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(),
            42
        );
    }
}

use std::{
    collections::BTreeMap,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, CompilerDatabase, Digest,
    LogicalPath, PackageKey, SourceInput, TokenKind,
    query::{
        MemoTable, Query, QueryCompleteness, QueryContext, QueryEngine, QueryExecutionKind,
        QueryFailure, QueryFrame, QueryRecomputeReason, QueryRecoveryPolicy, QueryValue,
    },
};

fn request(source: &[u8]) -> CompilationRequest {
    CompilationRequest {
        build: CompilerBuildIdentity {
            compiler: Digest::of_bytes(b"stage0-test"),
            language_generation: 1,
            query_generation: 1,
            interface_generation: 1,
            cache_generation: 1,
            bytecode_generation: 1,
            verifier_generation: 1,
        },
        mode: CompilationMode::Check,
        root_package: PackageKey("app@0.1.0".into()),
        sources: vec![SourceInput::new(
            PackageKey("app@0.1.0".into()),
            LogicalPath::parse("src/main.glorious").unwrap(),
            source,
        )],
        target: "g1-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn snapshot() -> grandiose_stage0::DatabaseSnapshot {
    let database = CompilerDatabase::new();
    let id = database
        .import(
            request(b"main() { /* nested /* note */ comment */ 12 + 3 }"),
            None,
        )
        .unwrap();
    database.open(id).unwrap()
}

#[derive(Debug)]
struct WordCount;
impl Query for WordCount {
    type Key = String;
    type Value = usize;
    type Error = ();
    const NAME: &'static str = "word_count";
    fn execute(
        &self,
        context: &mut QueryContext<'_>,
        key: Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>> {
        context.check()?;
        context.depend("source_blob", context.snapshot().world().fingerprint);
        Ok(QueryValue {
            value: key.split_whitespace().count(),
            fingerprint: Digest::of_bytes(key.as_bytes()),
            completeness: QueryCompleteness::Complete,
        })
    }
}

#[derive(Debug)]
struct NestedWordCount {
    words: QueryEngine<WordCount>,
}

/// This query's value depends solely on its typed key. It explicitly grants
/// reuse across source revisions, exercising red/green validation without
/// smuggling a source dependency through ambient state.
#[derive(Debug)]
struct KeyOnly;
impl Query for KeyOnly {
    type Key = String;
    type Value = usize;
    type Error = ();
    const NAME: &'static str = "key_only";

    fn can_reuse(
        &self,
        _key: &Self::Key,
        _parent: &grandiose_stage0::query::MemoEntry<Self::Value>,
        _from: &grandiose_stage0::DatabaseSnapshot,
        _to: &grandiose_stage0::DatabaseSnapshot,
    ) -> bool {
        true
    }

    fn execute(
        &self,
        context: &mut QueryContext<'_>,
        key: Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>> {
        context.check()?;
        Ok(QueryValue {
            value: key.len(),
            fingerprint: Digest::of_bytes(key.as_bytes()),
            completeness: QueryCompleteness::Complete,
        })
    }
}
impl Query for NestedWordCount {
    type Key = String;
    type Value = usize;
    type Error = ();
    const NAME: &'static str = "nested_word_count";
    fn execute(
        &self,
        context: &mut QueryContext<'_>,
        key: Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>> {
        let child = context.query(&self.words, key)?;
        Ok(QueryValue {
            value: child.value,
            fingerprint: Digest::of_parts([b"nested".as_slice(), &child.fingerprint.as_bytes()]),
            completeness: child.completeness,
        })
    }
}

#[derive(Debug)]
struct RecoveredLeaf;
impl Query for RecoveredLeaf {
    type Key = String;
    type Value = usize;
    type Error = ();
    const NAME: &'static str = "recovered_leaf";
    const RECOVERY_POLICY: QueryRecoveryPolicy = QueryRecoveryPolicy::Allow;

    fn execute(
        &self,
        _context: &mut QueryContext<'_>,
        key: Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>> {
        Ok(QueryValue {
            value: key.len(),
            fingerprint: Digest::of_parts([b"recovered-leaf".as_slice(), key.as_bytes()]),
            completeness: QueryCompleteness::Recovered,
        })
    }
}

#[derive(Debug)]
struct CompleteOnlyRecoveryParent {
    child: QueryEngine<RecoveredLeaf>,
}
impl Query for CompleteOnlyRecoveryParent {
    type Key = String;
    type Value = usize;
    type Error = ();
    const NAME: &'static str = "complete_only_recovery_parent";

    fn execute(
        &self,
        context: &mut QueryContext<'_>,
        key: Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>> {
        let child = context.query(&self.child, key)?;
        Ok(QueryValue {
            value: child.value,
            fingerprint: child.fingerprint,
            completeness: QueryCompleteness::Complete,
        })
    }
}

#[derive(Debug)]
struct RecoveryForwarder {
    child: QueryEngine<RecoveredLeaf>,
}
impl Query for RecoveryForwarder {
    type Key = String;
    type Value = usize;
    type Error = ();
    const NAME: &'static str = "recovery_forwarder";
    const RECOVERY_POLICY: QueryRecoveryPolicy = QueryRecoveryPolicy::Allow;

    fn execute(
        &self,
        context: &mut QueryContext<'_>,
        key: Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>> {
        let child = context.query(&self.child, key)?;
        // A faulty query author may claim completeness here. The engine must
        // retain the child's provisional status when it publishes this frame.
        Ok(QueryValue {
            value: child.value,
            fingerprint: Digest::of_parts([
                b"recovery-forwarder".as_slice(),
                child.fingerprint.as_bytes().as_slice(),
            ]),
            completeness: QueryCompleteness::Complete,
        })
    }
}

#[derive(Debug)]
struct UndeclaredRecovered;
impl Query for UndeclaredRecovered {
    type Key = String;
    type Value = usize;
    type Error = ();
    const NAME: &'static str = "undeclared_recovered";

    fn execute(
        &self,
        _context: &mut QueryContext<'_>,
        _key: Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>> {
        Ok(QueryValue {
            value: 0,
            fingerprint: Digest::of_bytes(b"undeclared-recovered"),
            completeness: QueryCompleteness::Recovered,
        })
    }
}

#[derive(Debug)]
struct PanicOnce {
    panicked: AtomicBool,
}
impl Query for PanicOnce {
    type Key = String;
    type Value = usize;
    type Error = ();
    const NAME: &'static str = "panic_once";

    fn execute(
        &self,
        _context: &mut QueryContext<'_>,
        key: Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>> {
        if !self.panicked.swap(true, Ordering::SeqCst) {
            panic!("hostile query panic before publication");
        }
        Ok(QueryValue {
            value: key.len(),
            fingerprint: Digest::of_parts([b"panic-once".as_slice(), key.as_bytes()]),
            completeness: QueryCompleteness::Complete,
        })
    }
}

#[test]
fn lossless_lexer_keeps_comments_and_terminates_nested_comments() {
    let snapshot = snapshot();
    let source = &snapshot.world().sources[0];
    let text = std::str::from_utf8(&source.bytes).unwrap();
    let lexed = grandiose_stage0::LexedFile::lex(source.key, text);
    assert!(lexed.diagnostics.is_empty());
    assert!(
        lexed
            .tokens
            .iter()
            .any(|token| token.kind == TokenKind::BlockComment)
    );
    assert_eq!(lexed.text(text, &lexed.tokens[0]), "main");
    assert_eq!(lexed.tokens.last().unwrap().kind, TokenKind::End);
    let opening_brace = lexed
        .tokens
        .iter()
        .position(|token| token.kind == TokenKind::Punctuation('{'))
        .unwrap();
    let closing_brace = lexed.delimiters.matching(opening_brace).unwrap();
    assert_eq!(
        lexed.tokens[closing_brace].kind,
        TokenKind::Punctuation('}')
    );
}

#[test]
fn delimiter_map_reports_mismatch_without_losing_the_unclosed_opener() {
    let snapshot = snapshot();
    let file = snapshot.world().sources[0].key;
    let lexed = grandiose_stage0::LexedFile::lex(file, "main(]");
    let codes = lexed
        .delimiters
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<Vec<_>>();
    assert_eq!(codes, vec!["G1007", "G1005"]);
}

#[test]
fn line_indexes_preserve_byte_spans_and_report_utf16_editor_columns() {
    let source = "first\n😀x\nlast";
    let index = grandiose_stage0::LineIndex::new(source);
    assert_eq!(index.line_count(), 3);
    assert_eq!(
        index.position(source, "first\n😀".len() as u32),
        Some(grandiose_stage0::SourcePosition {
            line: 1,
            utf16_column: 2
        })
    );
    assert!(
        index.position(source, 7).is_none(),
        "inside a UTF-8 code point is not a source boundary"
    );
}

#[test]
fn numeric_lexing_validates_radices_separators_and_float_exponents() {
    let snapshot = snapshot();
    let file = snapshot.world().sources[0].key;
    let source = "0b1010 0o7_5 0x_dead_beef 12_345 1.5_0 1e+9 2.5E-3";
    let lexed = grandiose_stage0::LexedFile::lex(file, source);
    assert!(lexed.diagnostics.is_empty(), "{:#?}", lexed.diagnostics);
    let kinds = lexed
        .tokens
        .iter()
        .filter(|token| !matches!(token.kind, TokenKind::Whitespace | TokenKind::End))
        .map(|token| token.kind.clone())
        .collect::<Vec<_>>();
    assert_eq!(
        kinds,
        vec![
            TokenKind::Integer,
            TokenKind::Integer,
            TokenKind::Integer,
            TokenKind::Integer,
            TokenKind::Float,
            TokenKind::Float,
            TokenKind::Float,
        ]
    );

    for malformed in [
        "0b102", "0x", "0x__dead", "0b__1", "1__2", "1_", "1e+", "12z",
    ] {
        let lexed = grandiose_stage0::LexedFile::lex(file, malformed);
        assert_eq!(lexed.tokens[0].kind, TokenKind::Invalid, "{malformed}");
        assert!(
            lexed
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G1008"),
            "{malformed}: {:#?}",
            lexed.diagnostics
        );
    }
}

#[test]
fn literal_recovery_rejects_unclosed_or_overwide_unicode_escapes_as_one_token() {
    let snapshot = snapshot();
    let file = snapshot.world().sources[0].key;
    for malformed in ["\"\\u{41", "'\\u{1f600'", "\"\\u{0000001}\"", "'\\u{}'"] {
        let lexed = grandiose_stage0::LexedFile::lex(file, malformed);
        assert_eq!(lexed.tokens[0].kind, TokenKind::Invalid, "{malformed}");
        assert_eq!(
            lexed.tokens.len(),
            2,
            "malformed literal must recover as one token: {malformed}"
        );
        assert!(
            lexed
                .diagnostics
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, "G1002" | "G1003" | "G1009" | "G1010")),
            "{malformed}: {:#?}",
            lexed.diagnostics
        );
    }
}

#[test]
fn scalar_literals_validate_escapes_and_character_cardinality() {
    let snapshot = snapshot();
    let file = snapshot.world().sources[0].key;
    let source = r#""line\n\x41\u{1f600}" '😀' '\''"#;
    let lexed = grandiose_stage0::LexedFile::lex(file, source);
    assert!(lexed.diagnostics.is_empty(), "{:#?}", lexed.diagnostics);
    assert_eq!(lexed.tokens[0].kind, TokenKind::String);
    assert_eq!(lexed.tokens[2].kind, TokenKind::Character);
    assert_eq!(lexed.tokens[4].kind, TokenKind::Character);

    for malformed in [r#""\q""#, r#""\u{110000}""#, "''", "'ab'", r#"'\x80'"#] {
        let lexed = grandiose_stage0::LexedFile::lex(file, malformed);
        assert_eq!(lexed.tokens[0].kind, TokenKind::Invalid, "{malformed}");
        assert!(
            lexed
                .diagnostics
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, "G1009" | "G1010")),
            "{malformed}: {:#?}",
            lexed.diagnostics
        );
    }
}

#[test]
fn lifetime_identifiers_are_not_mislexed_as_unterminated_characters() {
    let snapshot = snapshot();
    let file = snapshot.world().sources[0].key;
    let source = "fn borrow<'a, '_>(value: i64) -> i64 { value } 'x'";
    let lexed = grandiose_stage0::LexedFile::lex(file, source);
    assert!(lexed.diagnostics.is_empty(), "{:#?}", lexed.diagnostics);
    let significant = lexed
        .tokens
        .iter()
        .filter(|token| !matches!(token.kind, TokenKind::Whitespace | TokenKind::End))
        .map(|token| (token.kind.clone(), lexed.text(source, token)))
        .collect::<Vec<_>>();
    assert!(significant.contains(&(TokenKind::Identifier, "'a")));
    assert!(significant.contains(&(TokenKind::Identifier, "'_")));
    assert!(significant.contains(&(TokenKind::Character, "'x'")));
}

#[test]
fn label_sigil_is_a_lossless_operator_before_its_identifier() {
    let snapshot = snapshot();
    let file = snapshot.world().sources[0].key;
    let source = "@done: i64 { @done(42) }";
    let lexed = grandiose_stage0::LexedFile::lex(file, source);
    assert!(lexed.diagnostics.is_empty(), "{:#?}", lexed.diagnostics);
    let significant = lexed
        .tokens
        .iter()
        .filter(|token| !matches!(token.kind, TokenKind::Whitespace | TokenKind::End))
        .map(|token| (token.kind.clone(), lexed.text(source, token)))
        .collect::<Vec<_>>();
    assert!(significant.contains(&(TokenKind::Operator, "@")));
}

#[test]
fn memo_publication_is_revision_qualified_and_records_dependencies() {
    let snapshot = snapshot();
    let memo = MemoTable::<String, u32>::new();
    let mut frame = QueryFrame::new(&snapshot);
    frame.depend("source_blob", snapshot.world().fingerprint);
    memo.publish(
        &snapshot,
        "tokens".into(),
        QueryValue {
            value: 9,
            fingerprint: Digest::of_bytes(b"tokens"),
            completeness: QueryCompleteness::Complete,
        },
        frame,
    );
    let entry = memo.get(&snapshot, &"tokens".into()).unwrap();
    assert_eq!(entry.result.value, 9);
    assert_eq!(entry.dependencies.len(), 1);
    assert_eq!(entry.dependencies[0].query, "source_blob");
}

#[test]
fn engine_memoizes_typed_queries_only_after_successful_transactional_execution() {
    let snapshot = snapshot();
    let engine = QueryEngine::new(WordCount);
    let cancellation = grandiose_stage0::CancellationToken::new();
    let budget = grandiose_stage0::Budget::root("test", 4);
    let first = engine
        .execute(&snapshot, "one two".into(), &cancellation, &budget)
        .unwrap();
    let second = engine
        .execute(&snapshot, "one two".into(), &cancellation, &budget)
        .unwrap();
    assert_eq!(first.value, 2);
    assert_eq!(first.fingerprint, second.fingerprint);
    assert_eq!(budget.spent(), 1, "memo hit performs no new work charge");
}

#[test]
fn nested_query_results_record_dependencies_without_manual_parent_bookkeeping() {
    let snapshot = snapshot();
    let engine = QueryEngine::new(NestedWordCount {
        words: QueryEngine::new(WordCount),
    });
    let cancellation = grandiose_stage0::CancellationToken::new();
    let budget = grandiose_stage0::Budget::root("nested", 8);
    assert_eq!(
        engine
            .execute(&snapshot, "one two three".into(), &cancellation, &budget)
            .unwrap()
            .value,
        3
    );
    let memo = engine
        .memo()
        .get(&snapshot, &"one two three".to_owned())
        .unwrap();
    assert!(
        memo.dependencies
            .iter()
            .any(|dependency| dependency.query == WordCount::NAME)
    );
}

#[test]
fn cancelled_query_execution_never_publishes_a_memo_entry() {
    let snapshot = snapshot();
    let engine = QueryEngine::new(WordCount);
    let cancelled = grandiose_stage0::CancellationToken::new();
    cancelled.cancel();
    let budget = grandiose_stage0::Budget::root("test", 4);
    assert!(matches!(
        engine.execute(&snapshot, "one".into(), &cancelled, &budget),
        Err(QueryFailure::Cancelled)
    ));
    assert!(engine.memo().get(&snapshot, &"one".to_owned()).is_none());
    let active = grandiose_stage0::CancellationToken::new();
    assert_eq!(
        engine
            .execute(&snapshot, "one".into(), &active, &budget)
            .unwrap()
            .value,
        1
    );
    assert!(matches!(
        engine.execute(&snapshot, "one".into(), &cancelled, &budget),
        Err(QueryFailure::Cancelled)
    ));
}

#[test]
fn recovered_query_products_require_explicit_policy_and_propagate_through_parents() {
    let snapshot = snapshot();
    let cancellation = grandiose_stage0::CancellationToken::new();
    let budget = grandiose_stage0::Budget::root("recovery-policy", 16);

    let complete_only = QueryEngine::new(CompleteOnlyRecoveryParent {
        child: QueryEngine::new(RecoveredLeaf),
    });
    assert!(matches!(
        complete_only.execute(&snapshot, "editor input".into(), &cancellation, &budget),
        Err(QueryFailure::RecoveredProduct {
            query: RecoveredLeaf::NAME
        })
    ));
    assert!(
        complete_only
            .memo()
            .get(&snapshot, &"editor input".to_owned())
            .is_none(),
        "a complete-only parent must not publish after observing recovered input"
    );

    let forwarder = QueryEngine::new(RecoveryForwarder {
        child: QueryEngine::new(RecoveredLeaf),
    });
    let result = forwarder
        .execute(&snapshot, "editor input".into(), &cancellation, &budget)
        .unwrap();
    assert_eq!(result.completeness, QueryCompleteness::Recovered);
    assert_eq!(
        forwarder
            .memo()
            .get(&snapshot, &"editor input".to_owned())
            .unwrap()
            .result
            .completeness,
        QueryCompleteness::Recovered,
        "a recovery-capable parent may consume recovery but cannot erase it"
    );

    let undeclared = QueryEngine::new(UndeclaredRecovered);
    assert!(matches!(
        undeclared.execute(&snapshot, "forbidden".into(), &cancellation, &budget),
        Err(QueryFailure::RecoveredProduct {
            query: UndeclaredRecovered::NAME
        })
    ));
    assert!(
        undeclared
            .memo()
            .get(&snapshot, &"forbidden".to_owned())
            .is_none(),
        "recovery without a query-family policy must not poison the memo"
    );
}

#[test]
fn panic_before_publication_clears_running_marker_for_later_recovery() {
    let snapshot = snapshot();
    let engine = QueryEngine::new(PanicOnce {
        panicked: AtomicBool::new(false),
    });
    let cancellation = grandiose_stage0::CancellationToken::new();
    let budget = grandiose_stage0::Budget::root("panic-recovery", 8);
    let first = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        engine.execute(&snapshot, "retry".into(), &cancellation, &budget)
    }));
    assert!(
        first.is_err(),
        "hostile query must reach the panic boundary"
    );
    assert!(
        engine.memo().get(&snapshot, &"retry".to_owned()).is_none(),
        "a panicked query must not publish a partial value"
    );
    let retry = engine
        .execute(&snapshot, "retry".into(), &cancellation, &budget)
        .expect("the stale running marker must not turn retry into a cycle");
    assert_eq!(retry.value, 5);
    assert_eq!(
        budget.spent(),
        2,
        "each attempted execution is charged once"
    );
}

#[test]
fn retirement_reclaims_registered_query_products_and_provenance_at_safe_point() {
    let database = CompilerDatabase::new();
    let revision = database
        .import(request(b"pub fn main() -> i64 { 42 }"), None)
        .unwrap();
    let snapshot = database.open(revision).unwrap();
    let engine = Arc::new(QueryEngine::new(WordCount));
    // Registration is weak and idempotent: repeated host wiring must not
    // cause duplicate reclamation callbacks or retain the engine itself.
    database.register_revision_cache(&engine);
    database.register_revision_cache(&engine);
    let cancellation = grandiose_stage0::CancellationToken::new();
    let budget = grandiose_stage0::Budget::root("retention", 4);
    assert_eq!(
        engine
            .execute(&snapshot, "one two".into(), &cancellation, &budget)
            .unwrap()
            .value,
        2
    );
    assert_eq!(engine.memo().retained_entry_count(), 1);
    assert_eq!(engine.retained_execution_count(), 1);

    database.retire_revision(revision).unwrap();
    assert_eq!(database.collect_retired().retained_pinned, 1);
    assert_eq!(engine.memo().retained_entry_count(), 1);
    assert_eq!(engine.retained_execution_count(), 1);

    drop(snapshot);
    assert_eq!(database.collect_retired().collected, 1);
    assert_eq!(engine.memo().retained_entry_count(), 0);
    assert_eq!(engine.retained_execution_count(), 0);

    // Re-importing equivalent source receives a fresh revision and must
    // recompute; a collected revision cannot supply a stale cache result.
    let replacement = database
        .import(request(b"pub fn main() -> i64 { 42 }"), None)
        .unwrap();
    assert_ne!(replacement, revision);
    let replacement_snapshot = database.open(replacement).unwrap();
    engine
        .execute(
            &replacement_snapshot,
            "one two".into(),
            &cancellation,
            &budget,
        )
        .unwrap();
    assert_eq!(engine.memo().retained_entry_count(), 1);
    assert_eq!(engine.retained_execution_count(), 1);
    assert_eq!(budget.spent(), 2, "replacement world was recomputed");
}

#[test]
fn query_engine_reuses_only_query_validated_parent_entries() {
    let database = CompilerDatabase::new();
    let parent_id = database.import(request(b"main() { 1 }"), None).unwrap();
    let parent = database.open(parent_id).unwrap();
    let child_id = database
        .import(request(b"main() { 2 }"), Some(parent_id))
        .unwrap();
    let child = database.open(child_id).unwrap();
    let cancellation = grandiose_stage0::CancellationToken::new();

    let reusable = QueryEngine::new(KeyOnly);
    let reusable_budget = grandiose_stage0::Budget::root("reusable", 4);
    assert_eq!(
        reusable
            .execute(
                &parent,
                "stable key".into(),
                &cancellation,
                &reusable_budget
            )
            .unwrap()
            .value,
        10
    );
    assert_eq!(
        reusable
            .execute(&child, "stable key".into(), &cancellation, &reusable_budget)
            .unwrap()
            .value,
        10
    );
    assert_eq!(reusable_budget.spent(), 1);
    assert_eq!(
        reusable.execution_kind(&child, &"stable key".into()),
        Some(QueryExecutionKind::ReusedFromParent { parent: parent_id })
    );

    let source_sensitive = QueryEngine::new(WordCount);
    let source_budget = grandiose_stage0::Budget::root("source-sensitive", 4);
    source_sensitive
        .execute(&parent, "one two".into(), &cancellation, &source_budget)
        .unwrap();
    source_sensitive
        .execute(&child, "one two".into(), &cancellation, &source_budget)
        .unwrap();
    assert_eq!(source_budget.spent(), 2);
    assert_eq!(
        source_sensitive.why_recomputed(&child, &"one two".into()),
        Some(QueryRecomputeReason::ParentReuseRejected { parent: parent_id })
    );
}

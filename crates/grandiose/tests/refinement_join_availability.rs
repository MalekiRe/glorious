use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};

#[test]
fn disposable_local_removed_from_one_refinement_edge_is_unavailable_after_join() {
    let source = r#"
        struct Edge { value: u32 }
        struct Index { private values: Vec<Edge> }
        struct Headers { private index: Index }

        enum IndexView<'a> { Tuple(Slice<'a, Edge>), Never }
        impl<'a> Use<[0, *]> for IndexView<'a> {}

        parsed_index<'a>(value: &'a Headers) -> &'a Index { &value.index }

        index_view<'a>(value: &'a Index, id: u32) -> IndexView<'a> {
            if(id == 0) {
                IndexView::Tuple(Vec::as_slice(&value.values))
            } else {
                IndexView::Never
            }
        }

        edge_value(value: &Edge) -> u32 { value.value }

        enum ResolveError { Rejected(usize) }
        words() -> Vec<u32> { Vec::new() }

        resolve(
            headers: &Headers,
            declarations: &Vec<u32>,
            output: &mut Vec<u32>,
            type_id: u32,
            module: Option<usize>
        ) -> Result<u32, ResolveError> {
            let parsed = parsed_index(headers);
            handle index_view(parsed, type_id) {
                IndexView::Tuple(children) =>
                    if(Slice::is_empty(children)) {
                        Result::Ok(0)
                    } else {
                        let accepted_values = words();
                        try(Slice::try_for_each(children, { edge => {
                            let accepted = try(resolve(
                                headers,
                                declarations,
                                &mut *output,
                                edge_value(edge),
                                module
                            ), @resolve);
                            Vec::push(&mut accepted_values, accepted);
                            Result::Ok(())
                        }}), @resolve);
                        Result::Ok(wrapping_convert_to_u32(
                            Vec::len(&accepted_values)
                        ))
                    },
                IndexView::Never => Result::Ok(type_id)
            }
        }

        main() -> () {
            let values = Vec::new();
            let headers = Headers { index: Index { values: values } };
            let declarations = words();
            let output = Vec::new();
            resolve(
                &headers,
                &declarations,
                &mut output,
                0,
                Option::Some(7)
            );
            ()
        }
    "#;

    compile_source_to_phases_with_options(
        "refinement-join-availability.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O0,
        },
    )
    .unwrap();
}

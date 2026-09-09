// One embedding inventory shared by the stage-zero distributor and tests.
// Library behavior lives in Glorious; this file only joins source assets.
macro_rules! standard_library {
    ($($path:literal),+ $(,)?) => {
        pub const STANDARD_LIBRARY_SOURCE: &str = concat!($(include_str!($path), "\n",)+);
        pub const STANDARD_LIBRARY_FRAGMENTS: &[(&str, &str)] = &[$(($path, include_str!($path)),)+];
    };
}
standard_library!(
    "src/lib.glorious",
    "src/foundation.glorious",
    "src/algorithm.glorious",
    "src/traversal.glorious",
    "src/sorting.glorious",
    "src/heap.glorious",
    "src/iterator.glorious",
    "src/iterator_callbacks.glorious",
    "src/integer.glorious",
    "src/integer_text.glorious",
    "src/float.glorious",
    "src/float_text.glorious",
    "src/float_parse.glorious",
    "src/float_shortest.glorious",
    "src/float_math.glorious",
    "src/float_convert.glorious",
    "src/binary.glorious",
    "src/codecs.glorious",
    "src/memory.glorious",
    "src/boxed.glorious",
    "src/array.glorious",
    "src/utf8.glorious",
    "src/char_escape.glorious",
    "src/storage.glorious",
    "src/budget.glorious",
    "src/arena.glorious",
    "src/parse.glorious",
    "src/graph.glorious",
    "src/source_map.glorious",
    "src/fingerprint.glorious",
    "src/format.glorious",
    "src/time.glorious",
    "src/io.glorious",
    "src/path.glorious",
    "src/host.glorious",
    "src/ffi.glorious",
    "src/random.glorious",
    "src/generator.glorious",
    "src/task.glorious",
);

// A dependency-closed profile may omit extension families. Only exact embedded
// bytes in canonical order are admitted; this never trusts a modified library.
pub fn is_standard_library_composition(source: &[u8]) -> bool {
    let Some(mut rest) = source.strip_prefix(STANDARD_LIBRARY_FRAGMENTS[0].1.as_bytes()) else {
        return false;
    };
    for (_, fragment) in &STANDARD_LIBRARY_FRAGMENTS[1..] {
        let Some(after_separator) = rest.strip_prefix(b"\n") else { continue; };
        if let Some(after_fragment) = after_separator.strip_prefix(fragment.as_bytes()) {
            rest = after_fragment;
        }
    }
    rest.is_empty() || rest == b"\n"
}

pub fn composition_contains(source: &[u8], path: &str) -> bool {
    is_standard_library_composition(source)
        && STANDARD_LIBRARY_FRAGMENTS.iter().any(|(candidate, fragment)| {
            *candidate == path && source.windows(fragment.len()).any(|window| window == fragment.as_bytes())
        })
}

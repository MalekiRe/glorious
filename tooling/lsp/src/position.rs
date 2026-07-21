//! Byte-offset <-> LSP (line, UTF-16 character) conversion.

pub struct LineIndex {
    /// Byte offset of each line start; always begins with 0.
    starts: Vec<usize>,
}

impl LineIndex {
    pub fn new(text: &str) -> LineIndex {
        let mut starts = vec![0];
        starts.extend(
            text.bytes()
                .enumerate()
                .filter(|(_, b)| *b == b'\n')
                .map(|(i, _)| i + 1),
        );
        LineIndex { starts }
    }

    /// Clamps out-of-range offsets to the end of the text.
    pub fn position(&self, text: &str, offset: usize) -> (u32, u32) {
        let mut offset = offset.min(text.len());
        while !text.is_char_boundary(offset) {
            offset -= 1;
        }
        let line = self.starts.partition_point(|start| *start <= offset) - 1;
        let column = text[self.starts[line]..offset].encode_utf16().count();
        (line as u32, column as u32)
    }

    pub fn offset(&self, text: &str, line: u32, character: u32) -> usize {
        let Some(&start) = self.starts.get(line as usize) else {
            return text.len();
        };
        let end = self
            .starts
            .get(line as usize + 1)
            .copied()
            .unwrap_or(text.len());
        let mut units = 0u32;
        for (index, ch) in text[start..end].char_indices() {
            if units >= character {
                return start + index;
            }
            units += ch.len_utf16() as u32;
        }
        end
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_multibyte_text() {
        let text = "ab\nc\u{1F600}d\ne";
        let index = LineIndex::new(text);
        // The emoji is 4 bytes / 2 UTF-16 units; `d` sits after it.
        let d_offset = text.find('d').unwrap();
        assert_eq!(index.position(text, d_offset), (1, 3));
        assert_eq!(index.offset(text, 1, 3), d_offset);
        assert_eq!(index.position(text, 0), (0, 0));
        assert_eq!(index.offset(text, 2, 0), text.find('e').unwrap());
        // Past-the-end clamps.
        assert_eq!(index.offset(text, 9, 9), text.len());
        assert_eq!(index.position(text, 999).0, 2);
    }

    #[test]
    fn every_utf8_boundary_round_trips_across_adversarial_text() {
        let alphabet = ['a', '\n', '\r', '\0', 'é', 'λ', '\u{301}', '😀', '𐐷'];
        let mut state = 0x1234_5678_u64;
        for _case in 0..256 {
            let mut text = String::new();
            for _ in 0..64 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1);
                text.push(alphabet[(state as usize) % alphabet.len()]);
            }
            let index = LineIndex::new(&text);
            for offset in (0..=text.len()).filter(|offset| text.is_char_boundary(*offset)) {
                let (line, character) = index.position(&text, offset);
                assert_eq!(
                    index.offset(&text, line, character),
                    offset,
                    "{text:?} at {offset}"
                );
            }
            // Arbitrary byte offsets, including continuation bytes, must
            // clamp deterministically rather than panic.
            for offset in 0..=text.len() + 4 {
                let (line, character) = index.position(&text, offset);
                let recovered = index.offset(&text, line, character);
                assert!(text.is_char_boundary(recovered));
                assert!(recovered <= text.len());
            }
        }
    }

    #[test]
    fn positions_inside_surrogate_pairs_clamp_after_the_scalar() {
        let text = "a😀b";
        let index = LineIndex::new(text);
        assert_eq!(index.offset(text, 0, 1), 1);
        assert_eq!(index.offset(text, 0, 2), 5);
        assert_eq!(index.offset(text, 0, 3), 5);
        assert_eq!(index.offset(text, 0, 4), text.len());
        assert_eq!(index.position(text, 2), (0, 1));
    }
}

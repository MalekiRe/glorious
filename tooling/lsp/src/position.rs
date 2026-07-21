//! Byte-offset <-> LSP (line, UTF-16 character) conversion.

pub struct LineIndex {
    /// Byte offset of each line start; always begins with 0.
    starts: Vec<usize>,
}

impl LineIndex {
    pub fn new(text: &str) -> LineIndex {
        let mut starts = vec![0];
        starts.extend(text.bytes().enumerate().filter(|(_, b)| *b == b'\n').map(|(i, _)| i + 1));
        LineIndex { starts }
    }

    /// Clamps out-of-range offsets to the end of the text.
    pub fn position(&self, text: &str, offset: usize) -> (u32, u32) {
        let offset = offset.min(text.len());
        let line = self.starts.partition_point(|start| *start <= offset) - 1;
        let column = text[self.starts[line]..offset].encode_utf16().count();
        (line as u32, column as u32)
    }

    pub fn offset(&self, text: &str, line: u32, character: u32) -> usize {
        let Some(&start) = self.starts.get(line as usize) else { return text.len() };
        let end = self.starts.get(line as usize + 1).copied().unwrap_or(text.len());
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
}

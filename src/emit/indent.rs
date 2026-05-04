use std::fmt;

/// Indentation-aware string builder.
///
/// - Two-space indentation.
/// - Deterministic: does not depend on hash iteration.
#[derive(Clone, Debug, Default)]
pub struct IndentWriter {
    buf: String,
    indent: usize,
    at_line_start: bool,
}

impl IndentWriter {
    pub fn new() -> Self {
        Self {
            buf: String::new(),
            indent: 0,
            at_line_start: true,
        }
    }

    pub fn finish(self) -> String {
        self.buf
    }

    /// Current byte length of the buffer.
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    pub fn push_raw(&mut self, s: &str) {
        if s.is_empty() {
            return;
        }
        if self.at_line_start {
            for _ in 0..self.indent {
                self.buf.push_str("  ");
            }
            self.at_line_start = false;
        }
        self.buf.push_str(s);
    }

    pub fn newline(&mut self) {
        self.buf.push('\n');
        self.at_line_start = true;
    }

    pub fn writeln<S: AsRef<str>>(&mut self, line: S) {
        self.push_raw(line.as_ref());
        self.newline();
    }

    pub fn indent(&mut self) {
        self.indent += 1;
    }

    pub fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }
}

impl fmt::Write for IndentWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_raw(s);
        Ok(())
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Span {
    lo: u32,
    hi: u32,
}

impl Span {
    pub fn new(lo: u32, hi: u32) -> Self {
        Self { lo, hi }
    }
}

use std::convert::TryFrom;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Span {
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    pub const fn new(lo: u32, hi: u32) -> Self {
        Self { lo, hi }
    }

    pub fn with_hi(self, hi: u32) -> Self {
        Self { lo: self.lo, hi }
    }
}

impl From<(u32, u32)> for Span {
    fn from((lo, hi): (u32, u32)) -> Self {
        Self { lo, hi }
    }
}

impl From<(usize, usize)> for Span {
    fn from((lo, hi): (usize, usize)) -> Self {
        let lo = u32::try_from(lo).expect("lc doesn't support files larger than 4GB");
        let hi = u32::try_from(hi).expect("lc doesn't support files larger than 4GB");
        Self { lo, hi }
    }
}

#[macro_export]
macro_rules! S {
    ($lo:expr, $hi:expr) => {
        Span::new($lo as u32, $hi as u32)
    };
}

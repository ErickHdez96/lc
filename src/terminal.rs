use core::fmt;

#[derive(Debug, Copy, Clone)]
pub enum Color {
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    White,
    BrightBlack,
    BrightRed,
    BrightGreen,
    BrightYellow,
    BrightBlue,
    BrightMagenta,
    BrightCyan,
    BrightWhite,
}

impl Color {
    pub fn to_str(self) -> &'static str {
        match self {
            Self::Black => "30",
            Self::Red => "31",
            Self::Green => "32",
            Self::Yellow => "33",
            Self::Blue => "34",
            Self::Magenta => "35",
            Self::Cyan => "36",
            Self::White => "37",
            Self::BrightBlack => "90",
            Self::BrightRed => "91",
            Self::BrightGreen => "92",
            Self::BrightYellow => "93",
            Self::BrightBlue => "94",
            Self::BrightMagenta => "95",
            Self::BrightCyan => "96",
            Self::BrightWhite => "97",
        }
    }
}

#[derive(Debug, Default, Copy, Clone)]
pub struct Style {
    bold: bool,
    color: Option<Color>,
}

impl Style {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn bold(mut self) -> Self {
        self.bold = true;
        self
    }

    pub fn color(mut self, color: Color) -> Self {
        self.color = Some(color);
        self
    }
}

impl fmt::Display for Style {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\x1b[{}m", {
            let mut style = vec![];
            if self.bold {
                style.push("0");
            }
            if let Some(color) = self.color {
                style.push(color.to_str());
            }
            &style.join(";")
        })
    }
}

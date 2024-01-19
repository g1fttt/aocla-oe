use std::fmt;

#[derive(Debug)]
pub struct AoclaError {
    message: String,
    // TODO: Add line and column info
}

impl AoclaError {
    pub fn new(message: &str) -> Self {
        Self {
            message: message.to_owned(),
        }
    }
}

impl fmt::Display for AoclaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Error occured: {}", self.message)
    }
}

impl std::error::Error for AoclaError {}

macro_rules! error {
    ($message:expr) => {
        AoclaError::new(&$message)
    };
}

pub(crate) use error;

pub type Result<T = ()> = std::result::Result<T, AoclaError>;

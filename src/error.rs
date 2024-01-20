use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub struct AoclaError {
    message: String,
    // TODO: Add line and column info
}

impl AoclaError {
    pub fn new(message: String) -> Self {
        Self { message }
    }
}

impl fmt::Display for AoclaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Error occured: {}", self.message)
    }
}

impl Error for AoclaError {}

macro_rules! error {
    ($($arg:tt)*) => {
        AoclaError::new(format_args!($($arg)*).to_string())
    };
}

pub(crate) use error;

pub fn string_to_error(err: String) -> AoclaError {
    error!("{}", err)
}

pub fn to_error(err: impl Error) -> AoclaError {
    error!("{}", err.to_string())
}

pub type Result<T = ()> = std::result::Result<T, AoclaError>;

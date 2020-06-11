use super::Atom;
use std::{error, fmt};

/// Some error types.
#[derive(PartialEq, Clone, Debug)]
pub enum Error {
    /// For errors where the message is some arbritrary `String`.
    Str(String),
    /// For errors where the message is to involve an `Atom`.
    Atom(Atom),
}

impl Error {
    /// Create a `Box<Error>` with some arbritrary string.
    pub fn s<T: ToString>(message: T) -> Box<dyn error::Error> {
        Box::new(Self::Str(message.to_string()))
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Str(s) => s.fmt(f),
            Self::Atom(a) => a.fmt(f),
        }
    }
}

impl error::Error for Error {}

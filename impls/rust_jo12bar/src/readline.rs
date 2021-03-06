//! Methods for reading lines from the user.

use linefeed::{DefaultTerminal, Interface, ReadResult};
use std::path::PathBuf;

/// Gets the name of the history file to use.
fn get_history_file() -> PathBuf {
    let mut path = dirs::data_local_dir().unwrap();
    path.push(".mal_history");
    path
}

/// A utility struct for reading a line from the user.
pub struct Readline {
    reader: Interface<DefaultTerminal>,
}

impl Readline {
    /// Create a new `Readline` instance.
    pub fn new(prompt: &str) -> Self {
        let reader = Interface::new("mal").unwrap();
        reader.set_prompt(prompt).unwrap();
        reader
            .load_history(get_history_file().as_path())
            .unwrap_or(());

        Self { reader }
    }

    /// Get a new line.
    pub fn get(&mut self) -> Option<String> {
        self.readline()
    }

    /// Save the history to `readline::HISTORY_FILE`.
    pub fn save_history(&self) {
        self.reader
            .save_history(get_history_file().as_path())
            .unwrap_or(());
    }

    fn readline(&mut self) -> Option<String> {
        match self.reader.read_line() {
            Ok(read_result) => match read_result {
                ReadResult::Input(line) => {
                    if !line.is_empty() {
                        self.reader.add_history(line.clone());
                    }
                    Some(line)
                }
                _ => None,
            },

            Err(err) => {
                println!("Error: {:?}", err);
                None
            }
        }
    }
}

use mal_rust_jo12bar::{printer::pr_str, reader::read_line, readline::Readline};

fn main() {
    let mut readline = Readline::new("mal> ");

    while let Some(line) = readline.get() {
        // For now, just print the line back out.
        if !line.is_empty() {
            match read_line(&line.as_str()) {
                Ok(expr) => pr_str(expr),
                Err(e) => eprintln!("{}", e),
            }

            // mal_rust_jo12bar::reader::parse_line_and_print_ast(&line.as_str());
        }
    }

    // Save the history at the end.
    readline.save_history();
}

use mal_rust_jo12bar::readline::Readline;

fn main() {
    let mut readline = Readline::new("mal> ");

    while let Some(line) = readline.get() {
        // For now, just print the line back out.
        if !line.is_empty() {
            println!("{}", line);
        }
    }

    // Save the history at the end.
    readline.save_history();
}

//! Methods for outputting stuff.

use crate::types::{Atom as A, Expr};

/// Prints an AST (i.e. an `Expr`) using its default `std::fmt::Display` impl.
pub fn pr_str(expr: Expr) {
    println!("{}", expr);
}

/// Just a quick utility function for escaping strings.
fn escape_str(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            '\n' => "\\n".to_string(),
            '\r' => "\\r".to_string(),
            '\t' => "\\t".to_string(),
            '\0' => "\\0".to_string(),
            '"' => "\\\"".to_string(),
            '\\' => "\\\\".to_string(),
            _ => c.to_string(),
        })
        .collect::<Vec<_>>()
        .join("")
}

/// Prints a sequence, like a `Expr::List` or a `Expr::Vec`, to a `String`.
fn pr_seq(seq: &[Expr], print_readably: bool, start: &str, end: &str, join: &str) -> String {
    let strs: Vec<String> = seq.iter().map(|x| x.pr_str(print_readably)).collect();
    format!("{}{}{}", start, strs.join(join), end)
}

impl Expr {
    /// Formats a `Expr`. To be used for user-facing display.
    ///
    /// The `print_readably` parameter:
    ///
    /// - if `true`, doublequotes, newlines, and backslashes are translated into
    ///   their printed representations.
    /// - if `false`, then you'll get the text `"`, `\n`, or `\\`.
    pub fn pr_str(&self, print_readably: bool) -> String {
        use Expr::Constant as C;

        match self {
            // Comments:
            Expr::Comment => "".to_string(),

            // Just use the default `Atom` formatting for most `Atom` variants.
            C(atom @ A::Nil)
            | C(atom @ A::Bool(..))
            | C(atom @ A::Int(..))
            | C(atom @ A::Float(..))
            | C(atom @ A::Sym(..))
            | C(atom @ A::Keyword(..))
            | C(atom @ A::Func(..))
            | C(atom @ A::FnStar { .. })
            | C(atom @ A::Atom(..)) => format!("{}", atom),

            // Do funky string stuff:
            C(A::Str(s)) => {
                if print_readably {
                    format!("\"{}\"", escape_str(s))
                } else {
                    s.clone()
                }
            }

            // Sequences:
            Expr::List(l) => pr_seq(l, print_readably, "(", ")", " "),
            Expr::Vec(v) => pr_seq(v, print_readably, "[", "]", " "),
            Expr::HashMap(hm) => {
                let l: Vec<Expr> = hm
                    .iter()
                    .flat_map(|(k, v)| vec![C(A::from(k.clone())), v.clone()])
                    .collect();
                pr_seq(&l, print_readably, "{", "}", " ")
            }
        }
    }
}

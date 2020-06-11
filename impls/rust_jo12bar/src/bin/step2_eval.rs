use mal_rust_jo12bar::{
    printer::pr_str,
    reader::read_line,
    readline::Readline,
    types::{Atom, Error, Expr, ExprResult, HashMapKey},
};
use std::collections::HashMap;

/// This is the Lisp environment that holds all built-in functions.
type Env = HashMap<HashMapKey, Expr>;

/// This represents a two-argument `Expr::Constant(Atom::Int)` **OR**
/// `Expr::Constant(Atom::Float)` operation.
///
/// `int_op` and `float_op` will usually do the same thing, but for typing
/// reasons you may have to explicitly rewrite them twice.
fn binary_num_op(
    int_op: impl Fn(i64, i64) -> i64,
    float_op: impl Fn(f64, f64) -> f64,
    args: Vec<Expr>,
) -> ExprResult {
    if args.len() != 2 {
        return Err(Error::s(format!(
            "Wrong number of arguments given to binary integer operator.\n\
             Expected 2 arguments, found {}.",
            args.len()
        )));
    }

    match (args[0].clone(), args[1].clone()) {
        (Expr::Constant(Atom::Int(a)), Expr::Constant(Atom::Int(b))) => {
            Ok(Expr::Constant(Atom::Int(int_op(a, b))))
        }

        (Expr::Constant(Atom::Float(a)), Expr::Constant(Atom::Float(b))) => {
            Ok(Expr::Constant(Atom::Float(float_op(a, b))))
        }

        _ => Err(Error::s(
            "Arguments passed to binary numeric operator are of invalid type.".to_string(),
        )),
    }
}

/// Evaluates a single sub-section of the AST.
fn eval_ast(ast: &Expr, env: &Env) -> ExprResult {
    match ast {
        Expr::Constant(Atom::Sym(sym)) => {
            // Look up symbol in `env`, and return its associated value if found.
            // If not found, raise an error.
            if let Some(func) = env.get(&HashMapKey::Sym(sym.clone())) {
                Ok(func.clone())
            } else {
                Err(Error::s(format!("Unknown symbol: {}", sym)))
            }
        }

        Expr::List(exprs) => {
            // Return a new list that is the result of calling `eval()` on each
            // member of the original list.
            let mut evaluated_exprs = Vec::with_capacity(exprs.len());

            for expr in exprs.iter() {
                evaluated_exprs.push(eval(expr, env)?);
            }

            Ok(Expr::List(evaluated_exprs))
        }

        Expr::Vec(exprs) => {
            // Return a new vector that is the result of calling `eval()` on
            // each element of the original vector.
            let mut evaluated_exprs = Vec::with_capacity(exprs.len());

            for expr in exprs.iter() {
                evaluated_exprs.push(eval(expr, env)?);
            }

            Ok(Expr::Vec(evaluated_exprs))
        }

        Expr::HashMap(hmap) => {
            // Return a new hash-map, where:
            //
            // - Each each key is the same key as from the original hash-map
            // - Each value is the result of calling `eval()` on the original
            //   hash-map's corresponding value.
            let mut new_hashmap = HashMap::with_capacity(hmap.len());

            for (k, v) in hmap.iter() {
                new_hashmap.insert(k.clone(), eval(v, env)?);
            }

            Ok(Expr::HashMap(new_hashmap))
        }

        _ => Ok(ast.clone()),
    }
}

/// Evaluates an expression.
fn eval(ast: &Expr, env: &Env) -> ExprResult {
    match ast {
        // If `ast` is a list, then we evaluate it.
        Expr::List(exprs) => {
            // If the list is empty, just return `ast` unchanged.
            if exprs.is_empty() {
                Ok(ast.clone())
            } else {
                // Otherwise, call `eval_ast` to get a new evaluated list.
                match eval_ast(ast, env)? {
                    Expr::List(new_exprs) => {
                        let func = new_exprs.first().unwrap().clone();
                        func.apply(new_exprs[1..].to_vec())
                    }

                    other => Err(Error::s(format!(
                        "Expected a list when evaluating a list.\nGot {}",
                        other
                    ))),
                }
            }
        }

        // If `ast` is *not* a `Expr::List`, then return the result of calling
        // `eval_ast` on it.
        other_expr => eval_ast(other_expr, env),
    }
}

/// The main REPL.
fn repl(env: &Env) {
    let mut readline = Readline::new("mal> ");

    while let Some(line) = readline.get() {
        // For now, just print the line back out.
        if !line.is_empty() {
            match read_line(&line.as_str()) {
                Ok(expr) => match eval(&expr, env) {
                    Ok(result) => pr_str(result),
                    Err(error) => eprintln!("{}", error),
                },
                Err(e) => eprintln!("{}", e),
            }

            // mal_rust_jo12bar::reader::parse_line_and_print_ast(&line.as_str());
        }
    }

    // Save the history at the end.
    readline.save_history();
}

fn main() {
    let mut builtin_env = Env::with_capacity(4);

    builtin_env.insert(
        HashMapKey::Sym("+".to_string()),
        Expr::func(|args| binary_num_op(|a, b| a + b, |a, b| a + b, args)),
    );

    builtin_env.insert(
        HashMapKey::Sym("-".to_string()),
        Expr::func(|args| binary_num_op(|a, b| a - b, |a, b| a - b, args)),
    );

    builtin_env.insert(
        HashMapKey::Sym("*".to_string()),
        Expr::func(|args| binary_num_op(|a, b| a * b, |a, b| a * b, args)),
    );

    builtin_env.insert(
        HashMapKey::Sym("/".to_string()),
        Expr::func(|args| binary_num_op(|a, b| a / b, |a, b| a / b, args)),
    );

    repl(&builtin_env);
}

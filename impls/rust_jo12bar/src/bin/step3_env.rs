use mal_rust_jo12bar::{
    env::{env_from_iter, env_get, env_new, env_set, Env},
    printer::pr_str,
    reader::read_line,
    readline::Readline,
    types::{Atom, Error, Expr, HashMapKey as HMK},
};
use std::collections::HashMap;
use std::convert::TryFrom;

/// This represents a two-argument `Expr::Constant(Atom::Int)` **OR**
/// `Expr::Constant(Atom::Float)` operation.
///
/// `int_op` and `float_op` will usually do the same thing, but for typing
/// reasons you may have to explicitly rewrite them twice.
fn binary_num_op(
    int_op: impl Fn(i64, i64) -> i64,
    float_op: impl Fn(f64, f64) -> f64,
    args: Vec<Expr>,
) -> Result<Expr, Error> {
    if args.len() != 2 {
        return Err(Error::Str(format!(
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

        _ => Err(Error::Str(
            "Arguments passed to binary numeric operator are of invalid type.".to_string(),
        )),
    }
}

/// Evaluates a single sub-section of the AST.
fn eval_ast(ast: Expr, env: Env) -> Result<Expr, Error> {
    match ast.clone() {
        Expr::Constant(Atom::Sym(sym)) => {
            // Look up symbol in `env`, and return its associated value if found.
            // If not found, raise an error.
            if let Some(func) = env_get(&env, &HMK::Sym(sym.clone())) {
                Ok(func)
            } else {
                Err(Error::Str(format!("Symbol \'{}\' not found", sym)))
            }
        }

        Expr::List(exprs) => {
            // Return a new list that is the result of calling `eval()` on each
            // member of the original list.
            let mut evaluated_exprs = Vec::with_capacity(exprs.len());

            for expr in exprs.iter() {
                evaluated_exprs.push(eval(expr.clone(), env.clone())?);
            }

            Ok(Expr::List(evaluated_exprs))
        }

        Expr::Vec(exprs) => {
            // Return a new vector that is the result of calling `eval()` on
            // each element of the original vector.
            let mut evaluated_exprs = Vec::with_capacity(exprs.len());

            for expr in exprs.iter() {
                evaluated_exprs.push(eval(expr.clone(), env.clone())?);
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
                new_hashmap.insert(k.clone(), eval(v.clone(), env.clone())?);
            }

            Ok(Expr::HashMap(new_hashmap))
        }

        _ => Ok(ast),
    }
}

/// Evaluates an expression.
fn eval(ast: Expr, env: Env) -> Result<Expr, Error> {
    match ast.clone() {
        // If `ast` is a list, then we evaluate it.
        Expr::List(exprs) => {
            // If the list is empty, just return `ast` unchanged.
            if exprs.is_empty() {
                Ok(ast)
            } else {
                let expr0 = &exprs[0];

                match expr0 {
                    // If the first expression in the list `expr0` is the symbol
                    // "def!", then call the set method on the current
                    // environment `env`.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "def!" => {
                        if exprs.len() != 3 {
                            return Err(Error::Str(format!(
                                "Wrong number of expressions after a \'def!\'.\nExpected 2 expressions, found {}.",
                                exprs.len() - 1,
                            )));
                        }

                        let expr1 = &exprs[1];

                        match expr1 {
                            Expr::Constant(sym @ Atom::Sym(..)) => {
                                let evaluated_expr_2 = eval(exprs[2].clone(), env.clone())?;
                                env_set(
                                    &env,
                                    HMK::try_from(sym.clone()).unwrap(),
                                    evaluated_expr_2.clone(),
                                );
                                Ok(evaluated_expr_2)
                            }

                            _ => Err(Error::Str(format!(
                                "Expected a symbol after a \'def!\', found {}",
                                expr1
                            ))),
                        }
                    }

                    // If the first expression in the list, `expr01, is the
                    // symbol "let*", then create a new environment using the
                    // current environment as the "outer" environment. The first
                    // parameter is a list of new bindings in the "let*" env.
                    // The second parameter is evaluated using the new "let*"
                    // env.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "let*" => {
                        if exprs.len() != 3 {
                            return Err(Error::Str(format!(
                                "Wrong number of expressions after a \'let*\'.\nExpected 2 expressions, found {}.",
                                exprs.len() - 1,
                            )));
                        }

                        let expr1 = &exprs[1];

                        match expr1 {
                            // There should be a even number of Expr's in
                            // expr1_vec, because they're key/value pairs.
                            Expr::List(expr1_vec) | Expr::Vec(expr1_vec) if expr1_vec.len() % 2 != 0 => Err(Error::Str(format!(
                                "Found an odd number of expressions inside the list after a \'let*\'.\n\
                                 This could mean that one of the keys is missing a value, or one of\n\
                                 the values is missing a key.\n\
                                 Relevant list: {}", Expr::List(expr1_vec.clone())
                            ))),

                            Expr::List(expr1_vec) | Expr::Vec(expr1_vec) if expr1_vec.len() % 2 == 0 => {
                                let let_env = env_new(Some(env));

                                // Iterate over the bindings list in pairs.
                                for (k, v) in expr1_vec.chunks_exact(2).map(|s| (&s[0], &s[1])) {
                                    // Evaluate the binding's value using the in-progress let_env.
                                    let evaluated_v = eval(v.clone(), let_env.clone())?;

                                    match k {
                                        // Set a new key in the let_env to the evaluated value.
                                        Expr::Constant(sym @ Atom::Sym(..)) => {
                                            env_set(&let_env, HMK::try_from(sym.clone()).unwrap(), evaluated_v);
                                        }

                                        _ => return Err(Error::Str(format!(
                                            "Expected a symbol for a binding name in a \'let*\' binding list.\n\
                                             Found {}", k
                                        ))),
                                    }
                                }

                                // Return the result of evaluating the second parameter with the new
                                // let_env:
                                eval(exprs[2].clone(), let_env)
                            }

                            _ => Err(Error::Str(format!(
                                "Expected a list after a \'let*\', found {}",
                                expr1
                            ))),
                        }
                    }

                    // Otherwise, call `eval_ast` to get a new evaluated list.
                    // The first element in the list, `expr0`, is expected to be
                    // some sort of MAL function.
                    _ => match eval_ast(ast, env)? {
                        Expr::List(new_exprs) => {
                            let func = new_exprs.first().unwrap();
                            func.apply(new_exprs[1..].to_vec())
                        }

                        other => Err(Error::Str(format!(
                            "Expected a list when evaluating a list.\nGot {}",
                            other
                        ))),
                    },
                }
            }
        }

        // If `ast` is *not* a `Expr::List`, then return the result of calling
        // `eval_ast` on it.
        other_expr => eval_ast(other_expr, env),
    }
}

/// The main REPL.
fn rep(line: String, env: Env) -> Result<Expr, Error> {
    match read_line(&line) {
        Ok(ast) => eval(ast, env),
        Err(err_string) => Err(Error::Str(err_string)),
    }
}

fn main() {
    let builtin_env = env_from_iter(
        vec![
            (
                HMK::Sym("+".to_string()),
                Expr::func(|args| binary_num_op(|a, b| a + b, |a, b| a + b, args)),
            ),
            (
                HMK::Sym("-".to_string()),
                Expr::func(|args| binary_num_op(|a, b| a - b, |a, b| a - b, args)),
            ),
            (
                HMK::Sym("*".to_string()),
                Expr::func(|args| binary_num_op(|a, b| a * b, |a, b| a * b, args)),
            ),
            (
                HMK::Sym("/".to_string()),
                Expr::func(|args| binary_num_op(|a, b| a / b, |a, b| a / b, args)),
            ),
        ],
        None,
    );

    let mut readline = Readline::new("mal> ");

    while let Some(line) = readline.get() {
        if !line.is_empty() {
            readline.save_history();

            match rep(line, builtin_env.clone()) {
                Ok(out) => pr_str(out),
                Err(e) => eprintln!("Error: {}", e),
            }
        }
    }
}

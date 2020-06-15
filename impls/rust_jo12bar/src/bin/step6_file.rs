use mal_rust_jo12bar::{
    core,
    env::Env,
    mal_arg_length_check,
    reader::read_line,
    readline::Readline,
    types::{Atom, Error, Expr, ExprResult, HashMapKey as HMK},
};
use std::{
    collections::HashMap,
    convert::TryFrom,
    iter::FromIterator,
    sync::{Arc, Weak},
};

/// Evaluates a single sub-section of the AST.
fn eval_ast(ast: Expr, env: &Arc<Env>) -> ExprResult {
    match ast.clone() {
        Expr::Constant(Atom::Sym(sym)) => {
            // Look up symbol in `env`, and return its associated value if found.
            // If not found, raise an error.
            if let Some(func) = env.get(&HMK::Sym(sym.clone())) {
                Ok(func.as_ref().clone())
            } else {
                Err(Error::s(format!("Symbol \'{}\' not found", sym)))
            }
        }

        Expr::List(exprs) => {
            // Return a new list that is the result of calling `eval()` on each
            // member of the original list.
            let mut evaluated_exprs = Vec::with_capacity(exprs.len());

            for expr in exprs.iter() {
                evaluated_exprs.push(eval(expr.clone(), env)?);
            }

            Ok(Expr::List(evaluated_exprs))
        }

        Expr::Vec(exprs) => {
            // Return a new vector that is the result of calling `eval()` on
            // each element of the original vector.
            let mut evaluated_exprs = Vec::with_capacity(exprs.len());

            for expr in exprs.iter() {
                evaluated_exprs.push(eval(expr.clone(), env)?);
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
                new_hashmap.insert(k.clone(), eval(v.clone(), env)?);
            }

            Ok(Expr::HashMap(new_hashmap))
        }

        _ => Ok(ast),
    }
}

/// Evaluates an expression.
fn eval(ast: Expr, env: &Arc<Env>) -> ExprResult {
    let mut ast = ast;
    let mut env = env.clone();

    // The below vector helps with keeping Arc<Env>'s alive in the case of
    // tail-call optimization. The value of `env` could be set to completely
    // different Arc<Env>'s on each loop below (notably in fn* evaluation),
    // which could lead to Arc<Env>'s getting a strong_count of 0 and being
    // completely dropped! This would lead to premature allocation, and errors
    // when using Weak::upgrade() on some child Weak<Env>'s.
    //
    // So, before changing the value of `env` above, push a clone of the Arc<Env>
    // to this vector!
    let mut arc_env_keeper: Vec<Arc<Env>> = vec![];

    loop {
        match ast.clone() {
            // If `ast` is an *empty* list, just return `ast` unchanged.
            Expr::List(exprs) if exprs.is_empty() => return Ok(ast),

            // If `ast` is a *non-empty* list, then we evaluate it.
            Expr::List(exprs) => {
                let expr0 = &exprs[0];

                match expr0 {
                    // If the first expression in the list `expr0` is the symbol
                    // "def!", then call the set method on the current
                    // environment `env`.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "def!" => {
                        return eval_def_bang(exprs, &env)
                    }

                    // If the first expression in the list, `expr01`, is the
                    // symbol "let*", then create a new environment using the
                    // current environment as the "outer" environment. The first
                    // parameter is a list of new bindings in the "let*" env.
                    // The second parameter is evaluated using the new "let*"
                    // env.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "let*" => {
                        let env_ast = eval_let_star(exprs, &env)?;
                        arc_env_keeper.push(env.clone());
                        ast = env_ast.0;
                        env = env_ast.1;
                    }

                    // If the first symbol is the symbol "do", then evaluate
                    // all elements of a list passed to the "do" and return the
                    // final evaluated element.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "do" => {
                        ast = eval_do(exprs, &env)?;
                    }

                    // If the first symbol is "if", then evaluate the first
                    // parameter. If it is anything other than `Nil` or `false`,
                    // then evaluate and return the 2nd parameter. Otherwise,
                    // evaluate and return the 3rd parameter. If there is no 3rd
                    // parameter, just return `Nil`.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "if" => {
                        ast = eval_if(exprs, &env)?;
                    }

                    // If the first symbol is "fn*", then return a new function closure.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "fn*" => {
                        return eval_fn_star(exprs, &env)
                    }

                    // Otherwise, call `eval_ast` to get a new evaluated list.
                    // The first element in the list, `expr0`, is expected to be
                    // some sort of MAL function.
                    _ => match eval_ast(ast, &env)? {
                        Expr::List(new_exprs) => {
                            let func = &new_exprs[0];
                            let args = new_exprs[1..].to_vec();
                            match func {
                                // For simple functions:
                                Expr::Constant(Atom::Func(_)) => return func.apply(args),

                                // For functions that support tail call optimization:
                                Expr::Constant(Atom::FnStar {
                                    body,
                                    env: fenv,
                                    params,
                                    is_variadic,
                                    ..
                                }) => {
                                    let fenv = Weak::upgrade(fenv).expect(
                                        "Error getting reference to fn* env in apply stage!",
                                    );

                                    // Bind the function's env, and set ast to the function body.
                                    // The function will then be evaluated on the next loop.
                                    let apply_env =
                                        Arc::new(Env::bind(params.clone(), args, *is_variadic)?);

                                    Env::add_child(&fenv, &apply_env);
                                    arc_env_keeper.push(env.clone());

                                    env = apply_env;
                                    ast = body.as_ref().clone();
                                }

                                _ => return Err(Error::s("Attempt to call a non-function!")),
                            }
                        }

                        other => {
                            return Err(Error::s(format!(
                                "Expected a list when evaluating a list.\nGot {}",
                                other
                            )))
                        }
                    },
                }
            }

            // If `ast` is *not* a `Expr::List`, then return the result of calling
            // `eval_ast` on it.
            other_expr => return eval_ast(other_expr, &env),
        }
    }
}

/// Defines a new symbol in the current environment.
fn eval_def_bang(exprs: Vec<Expr>, env: &Arc<Env>) -> ExprResult {
    if exprs.len() != 3 {
        return Err(Error::s(format!(
            "Wrong number of expressions after a \'def!\'.\n\
             Expected 2 expressions, found {}.",
            exprs.len() - 1,
        )));
    }

    match &exprs[1] {
        Expr::Constant(sym @ Atom::Sym(..)) => {
            let evaluated_expr_2 = eval(exprs[2].clone(), env)?;
            env.insert(
                HMK::try_from(sym.clone())?,
                Arc::new(evaluated_expr_2.clone()),
            );
            Ok(evaluated_expr_2)
        }

        expr1 => Err(Error::s(format!(
            "Expected a symbol after a \'def!\', found {}",
            expr1
        ))),
    }
}

/// Defines a bunch of symbols in a new child `Env`, and then evaluates a
/// parameter within the child `Env`.
///
/// Returns the new `Env` and the `Expr` to be evaluated with it.
fn eval_let_star(
    exprs: Vec<Expr>,
    env: &Arc<Env>,
) -> Result<(Expr, Arc<Env>), Box<dyn std::error::Error>> {
    if exprs.len() != 3 {
        return Err(Error::s(format!(
            "Wrong number of expressions after a \'let*\'.\nExpected 2 expressions, found {}.",
            exprs.len() - 1,
        )));
    }

    match &exprs[1] {
        // There should be a even number of Expr's in
        // expr1_vec, because they're key/value pairs.
        Expr::List(expr1_vec) | Expr::Vec(expr1_vec) if expr1_vec.len() % 2 != 0 => {
            Err(Error::s(format!(
                "Found an odd number of expressions inside the list after a \'let*\'.\n\
                 This could mean that one of the keys is missing a value, or one of\n\
                 the values is missing a key.\n\
                 Relevant list: {}",
                Expr::List(expr1_vec.clone()),
            )))
        }

        Expr::List(expr1_vec) | Expr::Vec(expr1_vec) if expr1_vec.len() % 2 == 0 => {
            let let_env = Arc::new(Env::new());
            Env::add_child(&env, &let_env);

            // Iterate over the bindings list in pairs.
            for (k, v) in expr1_vec.chunks_exact(2).map(|s| (&s[0], &s[1])) {
                // Evaluate the binding's value using the in-progress let_env.
                let evaluated_v = eval(v.clone(), &let_env)?;

                match k {
                    // Set a new key in the let_env to the evaluated value.
                    Expr::Constant(sym @ Atom::Sym(..)) => {
                        let_env.insert(HMK::try_from(sym.clone())?, Arc::new(evaluated_v));
                    }

                    _ => {
                        return Err(Error::s(format!(
                            "Expected a symbol for a binding name in a \'let*\' binding list.\n\
                                             Found {}",
                            k
                        )))
                    }
                }
            }

            // Return the second parameter and the new let_env.
            // This should be evaluated by `eval()`.
            Ok((exprs[2].clone(), let_env))
        }

        expr1 => Err(Error::s(format!(
            "Expected a list after a \'let*\', found {}",
            expr1
        ))),
    }
}

/// Evaluates all the parameters *except the last one*, and returns the last
/// parameter (to be `eval()`'ed).
fn eval_do(exprs: Vec<Expr>, env: &Arc<Env>) -> ExprResult {
    // Get rid of the initial "do" sym:
    let params = &exprs[1..];

    // Get the position of the last parameter, which should allow us to slice up
    // to the second-to-last paramter.
    let len_to_second_last = match params.len() {
        0 | 1 => 0,
        len => len - 1,
    };

    match eval_ast(Expr::List(params[..len_to_second_last].to_vec()), env)? {
        Expr::List(_) => Ok(params.last().unwrap_or(&Expr::Constant(Atom::Nil)).clone()),

        _ => Err(Error::s("Invalid \'do\' form.".to_string())),
    }
}

/// An if-else statement. Returns the expression to be evaluated, based on the
/// conditional given.
fn eval_if(exprs: Vec<Expr>, env: &Arc<Env>) -> ExprResult {
    // The length should be *at least* 3, for the symbol "if", the conditional,
    // and the "true" branch.
    if exprs.len() < 3 {
        return Err(Error::s(format!(
            "Expected at least 2 expressions after an \'if\':\n\n\
             \t(if <condition> <true branch> [false branch])\n\n\
             Found {} expressions.",
            exprs.len() - 1,
        )));
    } else if exprs.len() > 4 {
        return Err(Error::s(format!(
            "Too many expressions after an \'if\'.\n\
             Expected 2 to 3 expressions, found {}",
            exprs.len() - 1,
        )));
    }

    let condition = &exprs[1];
    let true_branch = &exprs[2];

    // Evaluate condition:
    match eval(condition.clone(), env)? {
        // False branch:
        Expr::Constant(Atom::Bool(false)) | Expr::Constant(Atom::Nil) => {
            match exprs.get(3) {
                // If the false branch was given, evaluate and return:
                Some(false_branch) => Ok(false_branch.clone()),
                // Otherwise, just return `Nil`:
                None => Ok(Expr::Constant(Atom::Nil)),
            }
        }

        // True branch:
        _ => Ok(true_branch.clone()),
    }
}

/// A function closure (often called a lamba function in lisps.)
fn eval_fn_star(exprs: Vec<Expr>, env: &Arc<Env>) -> ExprResult {
    Expr::fn_star(exprs, &env, eval)
}

/// print
fn print(ast: &Expr) -> String {
    ast.pr_str(true)
}

/// The main REPL.
fn rep(line: impl ToString, env: &Arc<Env>) -> Result<String, Box<dyn std::error::Error>> {
    match read_line(&line.to_string()) {
        Ok(ast) => Ok(print(&eval(ast, env)?)),
        Err(err_string) => Err(Error::s(err_string)),
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // ==> core.rs: Namespace defined by Rust.
    let builtin_env = Arc::new(Env::from_iter(core::get_ns()));

    // Add a method to eval any ast from within MAL itself. This allows us to
    // treat mal data as a mal program.
    let weak_builtin_env = Arc::downgrade(&builtin_env);
    builtin_env.insert(
        HMK::Sym("eval".to_string()),
        Arc::new(Expr::func(move |args| {
            mal_arg_length_check!("eval", 1, args);
            eval(
                args[0].clone(),
                &Weak::upgrade(&weak_builtin_env)
                    .expect("Could not upgrade Weak reference to builtin_env in eval call."),
            )
        })),
    );

    // ==> core.mal: Namespace defined by MAL.
    // Define the `not` function:
    rep("(def! not (fn* (a) (if a false true)))", &builtin_env)?;

    // Define a function for loading from another file. It:
    // 1. Calls `slurp` to read the file in by name.
    // 2. Wraps the contents with `(do ...)` so the whole file is treated as a
    //    single program AST.
    // 3. Calls `read-string` to parse it into mal data.
    // 4. Calls `eval` to evaluate/run it.
    rep(
        r#"(def! load-file (fn* (f) (
                eval (read-string (
                    str "(do " (slurp f) "\nnil)")))))"#,
        &builtin_env,
    )?;

    let mut readline = Readline::new("mal> ");

    while let Some(line) = readline.get() {
        if !line.is_empty() {
            readline.save_history();

            match rep(line, &builtin_env) {
                Ok(out) => println!("{}", out),
                Err(e) => eprintln!("Error: {}", e),
            }
        }
    }

    Ok(())
}

use clap::{
    app_from_crate, crate_authors, crate_description, crate_name, crate_version, AppSettings, Arg,
};
use mal_rust_jo12bar::{
    core,
    env::Env,
    mal_arg_length_check,
    reader::read_line,
    readline::Readline,
    types::{Atom, Error, Expr, ExprResult, HashMapKey as HMK},
};
use std::{
    borrow::Cow,
    collections::HashMap,
    convert::TryFrom,
    iter::FromIterator,
    sync::{Arc, Weak},
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli_matches = app_from_crate!()
        .setting(AppSettings::TrailingVarArg)
        .arg(Arg::with_name("SCRIPT")
            .help(
                "The MAL script to run. If this is not provided, then MAL will run in REPL mode.",
            )
            .index(1)
            .required(false)
        )
        .arg(Arg::with_name("SCRIPT_ARGV")
            .help(
                "Arguments to pass to the script. Will be bound to the symbol *ARGV* as a list of \
                strings. If not provided, or if MAL is running in REPL mode, then *ARGV* will just \
                be the empty list `()`."
            )
            .index(2)
            .required(false)
            .multiple(true)
        )
        .get_matches();

    let builtin_env = get_builtin_env()?;

    if cli_matches.is_present("SCRIPT") {
        let filename = cli_matches.value_of_lossy("SCRIPT").unwrap();

        let argv = Expr::List(if cli_matches.is_present("SCRIPT_ARGV") {
            cli_matches
                .values_of_lossy("SCRIPT_ARGV")
                .unwrap()
                .into_iter()
                .map(|s| Expr::Constant(Atom::Str(s)))
                .collect()
        } else {
            vec![]
        });

        // Run in "script mode."
        run_script(&builtin_env, filename, argv)
    } else {
        // Run in "REPL mode."
        repl(&builtin_env)
    }
}

/// Gets the built-in environment.
fn get_builtin_env() -> Result<Arc<Env>, Box<dyn std::error::Error>> {
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

    Ok(builtin_env)
}

/// Script mode.
fn run_script(
    env: &Arc<Env>,
    filename: Cow<'_, str>,
    argv: Expr,
) -> Result<(), Box<dyn std::error::Error>> {
    // Bind *ARGV*:
    env.insert(HMK::Sym("*ARGV*".to_string()), Arc::new(argv));

    // Run the script by using the MAL load-file function.
    rep(format!("(load-file \"{}\")", filename), env)?;

    Ok(())
}

/// The main REPL.
fn repl(env: &Arc<Env>) -> Result<(), Box<dyn std::error::Error>> {
    // In REPL mode, the symbol *ARGV* is hardcoded to just be an empty Expr::List.
    env.insert(HMK::Sym("*ARGV*".to_string()), Arc::new(Expr::List(vec![])));

    let mut readline = Readline::new("mal> ");

    while let Some(line) = readline.get() {
        if !line.is_empty() {
            readline.save_history();

            match rep(line, env) {
                Ok(out) => {
                    if out != "".to_string() {
                        println!("{}", out)
                    }
                }
                Err(e) => eprintln!("Error: {}", e),
            }
        }
    }

    Ok(())
}

/// The main REP function.
fn rep(line: impl ToString, env: &Arc<Env>) -> Result<String, Box<dyn std::error::Error>> {
    match read_line(&line.to_string()) {
        Ok(ast) => Ok(print(&eval(ast, env)?)),
        Err(err_string) => Err(Error::s(err_string)),
    }
}

/// print
fn print(ast: &Expr) -> String {
    ast.pr_str(true)
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

    'tco: loop {
        match ast.clone() {
            // If `ast` is an *empty* list, just return `ast` unchanged.
            Expr::List(exprs) if exprs.is_empty() => return Ok(ast),

            // If `ast` is a *non-empty* list, then we evaluate it.
            Expr::List(exprs) => {
                let expr0 = &exprs[0];

                // Perform macro expansion. If the macro was expanded and we got
                // a successful result, then set ast to the result and skip past
                // the rest of the loop (i.e. perform TCO). If there's an error,
                // return it. Otherwise, just continue on to the rest of the
                // special forms below.
                match macroexpand(&ast, &env) {
                    (true, Ok(new_ast)) => {
                        ast = new_ast;
                        continue 'tco;
                    }
                    (_, Err(e)) => return Err(e),
                    _ => (),
                }

                match expr0 {
                    // If the first expression in the list `expr0` is the symbol
                    // "def!", then call the set method on the current
                    // environment `env`.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "def!" => {
                        return eval_def_bang(exprs, &env)
                    }

                    // If the first expression in the list is "defmacro!", then
                    // define a new macro in the current environment.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "defmacro!" => {
                        return eval_defmacro_bang(&exprs, &env)
                    }

                    // If the first expression in the list is "macroexpand", then expand the macro
                    // using the macroexpand() function. Return the result.
                    //
                    // This allows a mal program to perform explicit macro expansion without
                    // applying the result, which is useful for debugging macro expansion.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "macroexpand" => {
                        return eval_macroexpand(&exprs, &env)
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

                    // If the first symbol is "quote", then "turn off" evaluation by just returning
                    // the ast.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "quote" => {
                        return eval_quote(exprs)
                    }

                    // If the first symbol is "quasiquote", then interpret as a quoted list that has
                    // internal elements that can be temporarily unquoted (i.e. evaluated.)
                    // We evaluate the quoting structure, and then perform TCO and loop.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "quasiquote" => {
                        ast = eval_quasiquote(&exprs)?;
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

                                    // Drop any children that already exist in the fenv to avoid
                                    // accumulating a bunch of Arc's. This is fine as the children
                                    // can still access their parents, and will be kept alive in
                                    // arc_env_keeper for as long as they are needed.
                                    while let Some(_) = fenv.pop_child() {}

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

/// Defines a new *macro* in the current environment.
fn eval_defmacro_bang(exprs: &[Expr], env: &Arc<Env>) -> ExprResult {
    if exprs.len() != 3 {
        return Err(Error::s(format!(
            "defmacro!: Expected 2 expressions, found {}",
            exprs.len() - 1,
        )));
    }

    match &exprs[1] {
        Expr::Constant(sym @ Atom::Sym(..)) => {
            let evaluated_expr_2 = eval(exprs[2].clone(), env)?;

            // Only mal functions can become macros!
            match evaluated_expr_2 {
                Expr::Constant(Atom::FnStar {
                    body,
                    params,
                    eval,
                    env: fenv,
                    is_variadic,
                    is_macro: _is_macro,
                }) => {
                    let macro_f = Expr::Constant(Atom::FnStar {
                        body,
                        params,
                        eval,
                        env: fenv,
                        is_variadic,
                        is_macro: true,
                    });

                    env.insert(HMK::try_from(sym.clone())?, Arc::new(macro_f.clone()));

                    Ok(macro_f)
                }

                e => Err(Error::s(format!("defmacro!: Expected a fn*, found {}", e))),
            }
        }

        expr1 => Err(Error::s(format!(
            "defmacro!: Expected a symbol, found {}",
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

/// "Turns off" evaluation by just returning the second expression.
fn eval_quote(exprs: Vec<Expr>) -> ExprResult {
    if exprs.len() == 2 {
        Ok(exprs[1].clone())
    } else {
        Err(Error::s(format!(
            "quote: Expected 1 argument, found {}",
            exprs.len() - 1
        )))
    }
}

/// Allows a quoted list to have internal elements that are temporarily unquoted.
fn eval_quasiquote(exprs: &[Expr]) -> ExprResult {
    if exprs.len() == 2 {
        quasiquote(&exprs[1])
    } else {
        Err(Error::s(format!(
            "quasiquote: Expected 1 argument, found {}",
            exprs.len() - 1
        )))
    }
}

/// To be used within `eval_quasiquote`. Evaluates the quoting structure through
/// recursion.
fn quasiquote(ast: &Expr) -> ExprResult {
    match ast {
        // If ast is a non-empty list or vec:
        Expr::List(v) | Expr::Vec(v) if !v.is_empty() => match &v[0] {
            // If the ast is (unquote ARG), return ARG.
            Expr::Constant(Atom::Sym(s)) if s == "unquote" => {
                if v.len() == 2 {
                    Ok(v[1].clone())
                } else {
                    Err(Error::s(format!(
                        "unquote: Expected 1 argument, found {}",
                        v.len() - 1
                    )))
                }
            }

            // Otherwise, check the first element:
            a0 => match a0 {
                // If a0 is a non-empty list or vec:
                Expr::List(a0_v) | Expr::Vec(a0_v) if !a0_v.is_empty() => match &a0_v[0] {
                    // If the first element of a0 is "splice-unquote", return
                    // (concat AST[0][1] (quasiquote AST[1..]))
                    Expr::Constant(Atom::Sym(s)) if s == "splice-unquote" => {
                        if a0_v.len() == 2 {
                            Ok(Expr::List(vec![
                                Expr::Constant(Atom::Sym("concat".to_string())),
                                a0_v[1].clone(),
                                quasiquote(&Expr::List(v[1..].to_vec()))
                                    .map_err(|e| Error::s(format!("splice-unquote: {}", e)))?,
                            ]))
                        } else {
                            Err(Error::s(format!(
                                "splice-unquote: Expected 1 argument, found {}",
                                a0_v.len() - 1
                            )))
                        }
                    }

                    // Otherwise, return (cons (quasiquote AST[0]) (quasiquote AST[1..]))
                    _ => Ok(Expr::List(vec![
                        Expr::Constant(Atom::Sym("cons".to_string())),
                        quasiquote(&v[0]).map_err(|e| Error::s(format!("quasiquote: {}", e)))?,
                        quasiquote(&Expr::List(v[1..].to_vec()))
                            .map_err(|e| Error::s(format!("quasiquote: {}", e)))?,
                    ])),
                },

                // Otherwise, return (cons (quasiquote AST[0]) (quasiquote AST[1..]))
                _ => Ok(Expr::List(vec![
                    Expr::Constant(Atom::Sym("cons".to_string())),
                    quasiquote(&v[0]).map_err(|e| Error::s(format!("quasiquote: {}", e)))?,
                    quasiquote(&Expr::List(v[1..].to_vec()))
                        .map_err(|e| Error::s(format!("quasiquote: {}", e)))?,
                ])),
            },
        },

        // If ast is not a non-empty list or vec, return (quote AST)
        _ => Ok(Expr::List(vec![
            Expr::Constant(Atom::Sym("quote".to_string())),
            ast.clone(),
        ])),
    }
}

/// This function takes arguments `ast` and `env`. It returns:
///
/// - `Some(..)` if `ast` is a list that contains a symbol as its first element,
///   **and** that symbol refers to a function in the `env` that has `is_macro`
///   set to `true`.
///   - Specifically, a `Some((Arc<Expr>, Vec<Expr>))` is returned. The `Arc<Expr>`
///     is the macro to execute, and the `Vec<Expr>` are the arguments to pass to
///     it.
/// - `None` otherwise.
fn is_macro_call(ast: &Expr, env: &Arc<Env>) -> Option<(Arc<Expr>, Vec<Expr>)> {
    match ast {
        Expr::List(v) if !v.is_empty() => match &v[0] {
            Expr::Constant(sym @ Atom::Sym(..)) => {
                if let Some(val) = env.get(&HMK::try_from(sym.clone()).unwrap()) {
                    if val.is_macro_call() {
                        return Some((val, v[1..].to_vec()));
                    }
                }

                None
            }

            _ => None,
        },

        _ => None,
    }
}

/// Expands a macro by calling it with arguments. If the result of calling the macro is also a
/// macro, then that is expanded too.
fn macroexpand(ast: &Expr, env: &Arc<Env>) -> (bool, ExprResult) {
    let mut ast = ast.clone();
    let mut was_expanded = false;

    while let Some((mac, args)) = is_macro_call(&ast, env) {
        ast = match mac.apply(args) {
            Err(e) => return (false, Err(e)),
            Ok(expr) => expr,
        };

        was_expanded = true;
    }

    (was_expanded, Ok(ast))
}

fn eval_macroexpand(exprs: &[Expr], env: &Arc<Env>) -> ExprResult {
    if exprs.len() != 2 {
        return Err(Error::s(format!(
            "macroexpand: Expected 1 expression, found {}",
            exprs.len() - 1
        )));
    }

    match macroexpand(&exprs[1], &env) {
        (_, Ok(new_ast)) => Ok(new_ast),
        (_, Err(e)) => Err(e),
    }
}

use mal_rust_jo12bar::{
    core::NS,
    env::{env_from_iter, env_get, env_new, env_set, Env},
    reader::read_line,
    readline::Readline,
    types::{Atom, Error, Expr, HashMapKey as HMK},
};
use std::collections::HashMap;
use std::convert::TryFrom;

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
                        eval_def_bang(exprs, env)
                    }

                    // If the first expression in the list, `expr01`, is the
                    // symbol "let*", then create a new environment using the
                    // current environment as the "outer" environment. The first
                    // parameter is a list of new bindings in the "let*" env.
                    // The second parameter is evaluated using the new "let*"
                    // env.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "let*" => {
                        eval_let_star(exprs, env)
                    }

                    // If the first symbol is the symbol "do", then evaluate
                    // all elements of a list passed to the "do" and return the
                    // final evaluated element.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "do" => eval_do(exprs, env),

                    // If the first symbol is "if", then evaluate the first
                    // parameter. If it is anything other than `Nil` or `false`,
                    // then evaluate and return the 2nd parameter. Otherwise,
                    // evaluate and return the 3rd parameter. If there is no 3rd
                    // parameter, just return `Nil`.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "if" => eval_if(exprs, env),

                    // If the first symbol is "fn*", then return a new function closure.
                    Expr::Constant(Atom::Sym(ref a0sym)) if a0sym == "fn*" => {
                        eval_fn_star(exprs, env)
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

/// Defines a new symbol in the current environment.
fn eval_def_bang(exprs: Vec<Expr>, env: Env) -> Result<Expr, Error> {
    if exprs.len() != 3 {
        return Err(Error::Str(format!(
            "Wrong number of expressions after a \'def!\'.\n\
             Expected 2 expressions, found {}.",
            exprs.len() - 1,
        )));
    }

    match &exprs[1] {
        Expr::Constant(sym @ Atom::Sym(..)) => {
            let evaluated_expr_2 = eval(exprs[2].clone(), env.clone())?;
            env_set(
                &env,
                HMK::try_from(sym.clone()).unwrap(),
                evaluated_expr_2.clone(),
            );
            Ok(evaluated_expr_2)
        }

        expr1 => Err(Error::Str(format!(
            "Expected a symbol after a \'def!\', found {}",
            expr1
        ))),
    }
}

/// Defines a bunch of symbols in a new child `Env`, and then evaluates a
/// parameter within the child `Env`.
fn eval_let_star(exprs: Vec<Expr>, env: Env) -> Result<Expr, Error> {
    if exprs.len() != 3 {
        return Err(Error::Str(format!(
            "Wrong number of expressions after a \'let*\'.\nExpected 2 expressions, found {}.",
            exprs.len() - 1,
        )));
    }

    match &exprs[1] {
        // There should be a even number of Expr's in
        // expr1_vec, because they're key/value pairs.
        Expr::List(expr1_vec) | Expr::Vec(expr1_vec) if expr1_vec.len() % 2 != 0 => {
            Err(Error::Str(format!(
                "Found an odd number of expressions inside the list after a \'let*\'.\n\
                 This could mean that one of the keys is missing a value, or one of\n\
                 the values is missing a key.\n\
                 Relevant list: {}",
                Expr::List(expr1_vec.clone()),
            )))
        }

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

                    _ => {
                        return Err(Error::Str(format!(
                            "Expected a symbol for a binding name in a \'let*\' binding list.\n\
                                             Found {}",
                            k
                        )))
                    }
                }
            }

            // Return the result of evaluating the second parameter with the new
            // let_env:
            eval(exprs[2].clone(), let_env)
        }

        expr1 => Err(Error::Str(format!(
            "Expected a list after a \'let*\', found {}",
            expr1
        ))),
    }
}

/// Evaluates all the parameters, and returns the value of the last one.
fn eval_do(exprs: Vec<Expr>, env: Env) -> Result<Expr, Error> {
    match eval_ast(Expr::List(exprs[1..].to_vec()), env)? {
        Expr::List(evaluated_exprs) => Ok(evaluated_exprs
            .last()
            .unwrap_or(&Expr::Constant(Atom::Nil))
            .clone()),

        _ => Err(Error::Str("Invalid \'do\' form.".to_string())),
    }
}

/// An if-else statement.
fn eval_if(exprs: Vec<Expr>, env: Env) -> Result<Expr, Error> {
    // The length should be *at least* 3, for the symbol "if", the conditional,
    // and the "true" branch.
    if exprs.len() < 3 {
        return Err(Error::Str(format!(
            "Expected at least 2 expressions after an \'if\':\n\n\
             \t(if <condition> <true branch> [false branch])\n\n\
             Found {} expressions.",
            exprs.len() - 1,
        )));
    } else if exprs.len() > 4 {
        return Err(Error::Str(format!(
            "Too many expressions after an \'if\'.\n\
             Expected 2 to 3 expressions, found {}",
            exprs.len() - 1,
        )));
    }

    let condition = &exprs[1];
    let true_branch = &exprs[2];

    // Evaluate condition:
    match eval(condition.clone(), env.clone())? {
        // False branch:
        Expr::Constant(Atom::Bool(false)) | Expr::Constant(Atom::Nil) => {
            match exprs.get(3) {
                // If the false branch was given, evaluate and return:
                Some(false_branch) => eval(false_branch.clone(), env),
                // Otherwise, just return `Nil`:
                None => Ok(Expr::Constant(Atom::Nil)),
            }
        }

        // True branch:
        _ => eval(true_branch.clone(), env),
    }
}

/// A function closure (often called a lamba function in lisps.)
fn eval_fn_star(exprs: Vec<Expr>, env: Env) -> Result<Expr, Error> {
    // There should be two expressions after a "fn*": the arguments list and the
    // function body.
    if exprs.len() != 3 {
        return Err(Error::Str(format!(
            "Expected 2 expressions after a \'fn*\': the arguments list and the function body.\n\
             Found {}",
            exprs.len() - 1,
        )));
    }

    let fn_argument_list = &exprs[1];
    let fn_body = exprs[2].clone();

    // fn_argument_list should literally be a `Expr::List` of symbols.
    let fn_argument_vec = match fn_argument_list {
        Expr::Vec(exprs) | Expr::List(exprs) => exprs,

        _ => {
            return Err(Error::Str(format!(
                "Expected a list of symbols as an argument list after a \'fn*\'.\n\
                 Found {}",
                fn_argument_list,
            )));
        }
    };

    let fn_arg_names = fn_argument_vec
        .iter()
        // Each expression should be a Expr::Constant(Atom::Sym):
        .map(|expr| match expr {
            Expr::Constant(sym @ Atom::Sym(..)) => Ok(sym),
            _ => Err(format!(
                "Expected a symbol in a fn* argument list, found {}",
                expr
            )),
        });

    // If there were any non-symbols in the argument list, error out.
    if fn_arg_names.clone().any(|name| name.is_err()) {
        return Err(Error::Str(
            fn_arg_names
                .filter_map(|name| name.err())
                .collect::<Vec<String>>()
                .join("\n"),
        ));
    }

    // If there is a `&` symbol, then:
    // - There should only be one symbol after it
    // - That one symbol will be bound to all the rest of the arguments passed
    //   to the function that don't match up with preceding symbols.
    let has_var_arg = fn_arg_names
        .clone()
        .filter_map(|name| name.ok())
        .any(|name| name == &Atom::Sym("&".to_string()));

    // Pre-convert argument names to `HashMapKey`'s.
    let fn_arg_keys: Vec<HMK> = fn_arg_names
        .filter_map(|name| name.ok())
        .map(|sym| HMK::try_from(sym.clone()).unwrap())
        .collect();

    if has_var_arg {
        // There must only be one item after the '&':
        let ampersand_index = fn_arg_keys
            .iter()
            .position(|r| r == &HMK::Sym("&".to_string()))
            .unwrap();

        if fn_arg_keys[fn_arg_keys.len() - 2] != fn_arg_keys[ampersand_index] {
            return Err(Error::Str(format!(
                "Expected one symbol after the & in a fn* argument list, found {}",
                fn_arg_keys[(ampersand_index)..].len() - 1
            )));
        }
    }

    // At this point, all preliminary validation has passed. So, return a closure:
    Ok(Expr::func(move |args| {
        let n_positional_args = if has_var_arg {
            fn_arg_keys.len() - 2
        } else {
            fn_arg_keys.len()
        };

        // First, argument length check.
        if !has_var_arg && (args.len() != n_positional_args) {
            return Err(Error::Str(format!(
                "Expected {} arguments passed to fn*, found {}",
                n_positional_args,
                args.len(),
            )));
        } else if has_var_arg && (args.len() < n_positional_args) {
            return Err(Error::Str(format!(
                "Expected at least {} arguments passed to fn*, found {}",
                n_positional_args,
                args.len(),
            )));
        }

        // Then, create a new `Env` with the closed-over `env` as the parent:
        let fn_env = env_new(Some(env.clone()));

        // We loop through the non-var_args first:
        // Bind each non-var_arg argument in `args` to each key in `fn_arg_keys`,
        // in succession:
        for i in 0..n_positional_args {
            env_set(&fn_env, fn_arg_keys[i].clone(), args[i].clone());
        }

        // If this function has a final var_arg:
        if has_var_arg {
            // ...then bind all the rest of the args to it in a Expr::List.
            env_set(
                &fn_env,
                fn_arg_keys.last().unwrap().clone(),
                Expr::List(args[n_positional_args..].to_vec()),
            );
        }

        // Return the result of evaluating the function body in the fn_env.
        eval(fn_body.clone(), fn_env)
    }))
}

/// print
fn print(ast: Expr) -> String {
    ast.pr_str(true)
}

/// The main REPL.
fn rep(line: String, env: Env) -> Result<String, Error> {
    match read_line(&line) {
        Ok(ast) => Ok(print(eval(ast, env)?)),
        Err(err_string) => Err(Error::Str(err_string)),
    }
}

fn main() {
    // ==> core.rs: Namespace defined by Rust.
    let builtin_env = env_from_iter(NS.clone(), None);

    // ==> core.mal: Namespace defined by MAL.
    // Define the `not` function:
    rep(
        "(def! not (fn* (a) (if a false true)))".to_string(),
        builtin_env.clone(),
    )
    .unwrap();

    let mut readline = Readline::new("mal> ");

    while let Some(line) = readline.get() {
        if !line.is_empty() {
            readline.save_history();

            match rep(line, builtin_env.clone()) {
                Ok(out) => println!("{}", out),
                Err(e) => eprintln!("Error: {}", e),
            }
        }
    }
}

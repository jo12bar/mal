//! For parsing input via `nom`.

use crate::types::{Atom, Expr, HashMapKey};

use nom::{
    branch::alt,
    bytes::complete::{escaped_transform, tag, take_while1},
    character::complete::{char, digit1, none_of},
    combinator::{cut, map, map_res, not, opt, value},
    error::{context, convert_error, ParseError, VerboseError},
    multi::{many0, many1},
    number::complete::double,
    sequence::{delimited, preceded, terminated, tuple},
    AsChar, Err, IResult, InputTakeAtPosition,
};

use std::{collections::HashMap, convert::TryFrom, str};

/// Parses `nil`.
fn parse_nil<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Atom, E> {
    value(Atom::Nil, tag("nil"))(i)
}

/// Parses `true` or `false`.
fn parse_boolean<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Atom, E> {
    let parse_true = value(Atom::Bool(true), tag("true"));
    let parse_false = value(Atom::Bool(false), tag("false"));

    alt((parse_true, parse_false))(i)
}

/// Parses integers, like `42`, `0`, or `-1010`.
///
/// Should be used before `parse_float`.
fn parse_int<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Atom, E> {
    /// We don't want the int's to contain a decimal place. For the sake of less
    /// repetion, we create this helper function that only matches digits that
    /// are *not* immediately followed by a decimal place.
    fn sub_int_parser<'b, E: ParseError<&'b str>>(i: &'b str) -> IResult<&'b str, &'b str, E> {
        terminated(digit1, not(tag(".")))(i)
    }

    map(
        alt((
            // Match positive numbers:
            map_res(sub_int_parser, |digit_str: &str| digit_str.parse::<i64>()),
            // Match negative numbers:
            map(preceded(tag("-"), sub_int_parser), |digit_str: &str| {
                -digit_str.parse::<i64>().unwrap()
            }),
        )),
        Atom::Int,
    )(i)
}

/// Parses 64-bit floats, like `42.3`, `3.14159`, or `-1010.0154654`.
///
/// Should be used after `parse_int`.
fn parse_float<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Atom, E> {
    map(double, Atom::Float)(i)
}

/// Parses a number, which could be a 64-bit signed integer or a 64-bit float.
fn parse_number<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Atom, E> {
    alt((parse_int, parse_float))(i)
}

/// Parses a string of characters, allowing for escape chars.
fn parse_string_of_chars<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, String, E> {
    escaped_transform(take_while1(|c| c != '\\' && c != '"'), '\\', |s: &str| {
        alt((
            value("\\", tag("\\")),
            value("\"", tag("\"")),
            value("\0", tag("0")),
            value("\n", tag("n")),
            value("\r", tag("r")),
            value("\t", tag("t")),
        ))(s)
    })(i)
}

/// Parses a string, like `"foo"`.
fn parse_string<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Atom, E> {
    map(
        context(
            "string",
            preceded(
                char('\"'),
                cut(terminated(
                    map(opt(parse_string_of_chars), |o| dbg!(o.unwrap_or_default())),
                    char('\"'),
                )),
            ),
        ),
        Atom::Str,
    )(i)
}

/// Parses `Keyword`s, like `:foo` or `:1-sdf`.
fn parse_keyword<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Atom, E> {
    const CHARS_TO_AVOID: &str = "\n\r\t []{}()'\",;";

    map(
        context(
            "keyword",
            preceded(char(':'), cut(many1(none_of(CHARS_TO_AVOID)))),
        ),
        |s| Atom::Keyword(s.into_iter().collect::<String>()),
    )(i)
}

/// Parses `Sym`s, which are kinda like a last resort for unknown space-delimited
/// sequences.
fn parse_symbol<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Atom, E> {
    const CHARS_TO_AVOID: &str = "\n\r\t []{}()'\",;";

    map(many1(none_of(CHARS_TO_AVOID)), |s| {
        Atom::Sym(s.into_iter().collect::<String>())
    })(i)
}

/// Parses an `Atom`.
fn parse_atom<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Atom, E> {
    alt((
        parse_nil,
        parse_boolean,
        parse_number,
        parse_string,
        parse_keyword,
        parse_symbol,
    ))(i)
}

/// Parses an `Expr::Constant`, which is basically an expression that is just a
/// single `Atom`.
fn parse_constant<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(parse_atom, Expr::Constant)(i)
}

/// A helper function for recognizing 0 or more commas or anything that matches
/// `nom::character::complete::multispace0`.
///
/// Based on the `nom` v5.1.1 implementation of multispace0.
fn multispace0_or_commas<T, E: ParseError<T>>(i: T) -> IResult<T, T, E>
where
    T: InputTakeAtPosition,
    <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
    i.split_at_position_complete(|item| {
        let c = item.as_char();
        !(c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == ',')
    })
}

/// A helper function for recognizing 1 or more commas or anything that matches
/// `nom::character::complete::multispace1`.
///
/// Based on the `nom` v5.1.1 implementation of multispace0.
fn multispace1_or_commas<T, E: ParseError<T>>(i: T) -> IResult<T, T, E>
where
    T: InputTakeAtPosition,
    <T as InputTakeAtPosition>::Item: AsChar + Clone,
{
    i.split_at_position1_complete(
        |item| {
            let c = item.as_char();
            !(c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == ',')
        },
        nom::error::ErrorKind::MultiSpace,
    )
}

/// A helper function for parsing lists. Each list should start with a `(` and
/// end with a `)`. By putting whitespace and newline parsing here, we can avoid
/// having to worry about it throughout the rest of the parser.
///
/// Parses things like `( ...inner... )`. Anything between the brackets is
/// parsed by the passed-in parser `inner`.
///
/// Note that this functions takes a `nom` parsing function and returns a new
/// `nom` parsing function.
fn s_paren_exp<'a, O1, E: ParseError<&'a str>, F>(
    inner: F,
) -> impl Fn(&'a str) -> IResult<&'a str, O1, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O1, E>,
{
    delimited(
        char('('),
        preceded(multispace0_or_commas, inner),
        context(
            "unbalanced closing paren",
            cut(preceded(multispace0_or_commas, char(')'))),
        ),
    )
}

/// A helper function for parsing vectors. Each vector should start with a `[` and
/// end with a `]`. By putting whitespace and newline parsing here, we can avoid
/// having to worry about it throughout the rest of the parser.
///
/// Parses things like `[ ...inner... ]`. Anything between the brackets is
/// parsed by the passed-in parser `inner`.
///
/// Note that this functions takes a `nom` parsing function and returns a new
/// `nom` parsing function.
fn s_bracket_exp<'a, O1, E: ParseError<&'a str>, F>(
    inner: F,
) -> impl Fn(&'a str) -> IResult<&'a str, O1, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O1, E>,
{
    delimited(
        char('['),
        preceded(multispace0_or_commas, inner),
        context(
            "unbalanced closing bracket",
            cut(preceded(multispace0_or_commas, char(']'))),
        ),
    )
}

/// A helper function for parsing hashes. Each hash should start with a `{` and
/// end with a `}`. By putting whitespace and newline parsing here, we can avoid
/// having to worry about it throughout the rest of the parser.
///
/// Parses things like `{ ...inner... }`. Anything between the brackets is
/// parsed by the passed-in parser `inner`.
///
/// Note that this functions takes a `nom` parsing function and returns a new
/// `nom` parsing function.
fn s_brace_exp<'a, O1, E: ParseError<&'a str>, F>(
    inner: F,
) -> impl Fn(&'a str) -> IResult<&'a str, O1, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O1, E>,
{
    delimited(
        char('{'),
        preceded(multispace0_or_commas, inner),
        context(
            "unbalanced closing brace",
            cut(preceded(multispace0_or_commas, char('}'))),
        ),
    )
}

/// Parses a list.
fn parse_list<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(s_paren_exp(many0(parse_expr)), Expr::List)(i)
}

/// Parses a vector.
fn parse_vec<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(s_bracket_exp(many0(parse_expr)), Expr::Vec)(i)
}

/// Parses a hash-map key.
fn parse_hash_map_key<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, HashMapKey, E> {
    let (i, atom) = preceded(
        multispace0_or_commas,
        alt((parse_string, parse_keyword, parse_int)),
    )(i)?;

    let key = HashMapKey::try_from(atom).unwrap();

    Ok((i, key))
}

/// Parses a hash-map.
fn parse_hashmap<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(
        s_brace_exp(many0(tuple((
            parse_hash_map_key,
            multispace1_or_commas,
            parse_expr,
        )))),
        |tuples| {
            Expr::HashMap(
                tuples
                    .into_iter()
                    .map(|(key, _, value)| (key, value))
                    .collect::<HashMap<_, _>>(),
            )
        },
    )(i)
}

/// Parses an `(quote EXPR)`, like `'1` or `'(1 2 3)`.
fn parse_quote<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(
        context("quote", preceded(char('\''), cut(parse_expr))),
        Expr::reader_macro_quote,
    )(i)
}

/// Parses a `(quasiquote EXPR)`, like
///
/// ```lisp
/// `1
/// ```
///
/// or
///
/// ```lisp
/// `(1 2 3)
/// ```
fn parse_quasiquote<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(
        context(
            "reader macro quasiquote",
            preceded(char('`'), cut(parse_expr)),
        ),
        Expr::reader_macro_quasiquote,
    )(i)
}

/// Parses an `(unquote EXPR)`, like `~1` or `~(1 2 3)`.
fn parse_unquote<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(
        context("reader macro unquote", preceded(char('~'), cut(parse_expr))),
        Expr::reader_macro_unquote,
    )(i)
}

/// Parses a `(splice-unquote EXPR)`, like `~@1` or `~@(1 2 3)`.
fn parse_splice_unquote<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(
        context(
            "reader macro splice-unquote",
            preceded(tag("~@"), cut(parse_expr)),
        ),
        Expr::reader_macro_splice_unquote,
    )(i)
}

/// Parses a `(deref EXPR)`, like `@a` or `@(1 2 3)`.
fn parse_deref<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(
        context("reader macro deref", preceded(char('@'), cut(parse_expr))),
        Expr::reader_macro_deref,
    )(i)
}

/// Parses a `(with-meta EXPR2 EXPR1)`, like `^{"a" 1} [1 2 3]`.
fn parse_with_meta<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    map(
        context(
            "reader macro with-metadata",
            preceded(
                char('^'),
                cut(tuple((
                    context("expr1", parse_expr),
                    context("space", multispace0_or_commas),
                    context("expr2", parse_expr),
                ))),
            ),
        ),
        |(expr1, _, expr2)| Expr::reader_macro_with_meta(expr1, expr2),
    )(i)
}

/// Parses reader macros. These are things that just are transformed into another
/// form by the parser.
fn parse_reader_macro<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    context(
        "reader macro",
        alt((
            parse_splice_unquote,
            parse_quote,
            parse_quasiquote,
            parse_unquote,
            parse_deref,
            parse_with_meta,
        )),
    )(i)
}

/// Parses comments. Comments start with a semicolon (`;`) and go until a newline
/// character (`\n`) is reached.
fn parse_comment<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    value(Expr::Comment, preceded(char(';'), many0(none_of("\n"))))(i)
}

/// Parses an expression.
fn parse_expr<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    preceded(
        multispace0_or_commas,
        alt((
            parse_comment,
            parse_reader_macro,
            parse_list,
            parse_vec,
            parse_hashmap,
            parse_constant,
        )),
    )(i)
}

/// Prints out the parsed AST.
pub fn parse_line_and_print_ast(s: &str) {
    match parse_expr::<VerboseError<&str>>(s) {
        Err(Err::Error(e)) | Err(Err::Failure(e)) => {
            eprintln!("===== ERROR!!! =====\n\n{}", convert_error(s, e));
        }
        Ok(res) => {
            println!(
                "===== Parse Result =====\n\n{:#?}",
                IResult::<&str, Expr, VerboseError<&str>>::Ok(res)
            );
        }
        _ => {}
    }
}

/// Returns the parsed AST (i.e. an `Expr`) from a line of string input.
pub fn read_line(s: &str) -> std::result::Result<Expr, String> {
    match parse_expr::<VerboseError<&str>>(s) {
        Err(Err::Error(e)) | Err(Err::Failure(e)) => {
            std::result::Result::Err(format!("===== ERROR!!! =====\n\n{}", convert_error(s, e)))
        }
        Ok((_, expr)) => Ok(expr),
        _ => std::result::Result::Err("Unknown/incomplete error".into()),
    }
}

use nom::branch::alt;
use nom::bytes::complete::{is_not, tag};
use nom::character::complete::{char, i64, multispace0, multispace1};
use nom::combinator::{cut, map, opt, value, verify};
use nom::error::{context, ErrorKind, ParseError};
use nom::multi::{fold_many0, separated_list0};
use nom::sequence::{delimited, pair, preceded};
use nom::{IResult, InputTakeAtPosition, Parser};

pub fn parse_root(i: &str) -> Result<Object, String> {
    let s = format!("[{}]", i);
    let (_, v) = parse_list(&s).map_err(|err| err.to_string())?;
    Ok(Object::List(v))
}

fn parse_object(i: &str) -> IResult<&str, Object> {
    alt((
        map(parse_int, Object::Int),
        map(parse_list, Object::List),
        map(parse_tuple, |(v, q)| Object::Tuple(v, q)),
        map(parse_str, Object::Str),
        map(parse_bool, Object::Bool),
        map(parse_sym, |(s, q)| Object::Sym(s, q)),
    ))(i)
}

fn parse_int(i: &str) -> IResult<&str, i64> {
    i64(i)
}

fn parse_list(i: &str) -> IResult<&str, Vec<Object>> {
    delimited(
        char('['),
        whitesp(separated_list0(multispace1, parse_object)),
        context("closing list bracket", cut(char(']'))),
    )(i)
}

fn parse_tuple(i: &str) -> IResult<&str, (Vec<Object>, bool)> {
    let (s, (q, v)) = pair(
        opt(char('\'')),
        delimited(
            char('('),
            whitesp(separated_list0(multispace1, parse_object)),
            context("closing tuple paren", cut(char(')'))),
        ),
    )(i)?;
    Ok((s, (v, q.is_some())))
}

fn parse_str(i: &str) -> IResult<&str, String> {
    delimited(
        char('"'),
        fold_many0(parse_str_frag, String::new, |mut s, frag| {
            match frag {
                StringFragment::Lit(lit) => s.push_str(lit),
                StringFragment::EscChar(esc_char) => s.push(esc_char),
            }
            s
        }),
        char('"'),
    )(i)
}

fn parse_bool(i: &str) -> IResult<&str, bool> {
    alt((value(false, tag("#f")), value(true, tag("#t"))))(i)
}

fn parse_sym(i: &str) -> IResult<&str, (String, bool)> {
    let (s, (q, sym)) = pair(opt(char('\'')), map(parse_sym_lit, |s| s.to_owned()))(i)?;
    Ok((s, (sym, q.is_some())))
}

fn is_sym(i: &str) -> IResult<&str, &str> {
    let symbols = "_@$+-*/=?!%><&|~";
    i.split_at_position1_complete(
        |c| !c.is_alphanumeric() && !symbols.contains(c),
        ErrorKind::IsA,
    )
}

fn parse_sym_lit(i: &str) -> IResult<&str, &str> {
    verify(is_sym, |s: &str| !s.is_empty())(i)
}

fn parse_esc_char(i: &str) -> IResult<&str, char> {
    preceded(
        char('\\'),
        alt((
            value('\n', char('n')),
            value('\r', char('r')),
            value('\t', char('t')),
        )),
    )(i)
}

fn parse_str_lit(i: &str) -> IResult<&str, &str> {
    verify(is_not("\"\\"), |s: &str| !s.is_empty())(i)
}

fn parse_str_frag(i: &str) -> IResult<&str, StringFragment<'_>> {
    alt((
        map(parse_str_lit, StringFragment::Lit),
        map(parse_esc_char, StringFragment::EscChar),
    ))(i)
}

#[derive(Debug)]
enum StringFragment<'a> {
    Lit(&'a str),
    EscChar(char),
}

fn whitesp<'a, O, E, F>(f: F) -> impl Parser<&'a str, O, E>
where
    E: ParseError<&'a str>,
    F: Parser<&'a str, O, E>,
{
    delimited(multispace0, f, multispace0)
}

#[derive(Debug, Clone)]
pub enum Object {
    Int(i64),
    List(Vec<Object>),
    Tuple(Vec<Object>, bool),
    Str(String),
    Bool(bool),
    Sym(String, bool),
}

extern crate nom;
use crate::tecs_file::*;
use aterms::extensible::{
    parse_list_term_no_annotations, parse_recursive_term_no_annotations,
    parse_string_term_no_annotations, parse_tuple_term_no_annotations,
};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_while1},
    character::complete::{char, multispace0},
    combinator::{all_consuming, cut, map, map_res, opt, verify},
    error::ParseError,
    error::VerboseError,
    error::{context, convert_error},
    multi::{many0, many1, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, terminated, tuple},
    IResult, Parser,
};

use std::fs;
fn ws<'a, O, E: ParseError<&'a str>, F: Parser<&'a str, O, E>>(f: F) -> impl Parser<&'a str, O, E> {
    delimited(multispace0, f, multispace0)
}

fn ws_before<'a, O, E: ParseError<&'a str>, F: Parser<&'a str, O, E>>(
    f: F,
) -> impl Parser<&'a str, O, E> {
    preceded(multispace0, f)
}

fn ws_after<'a, O, E: ParseError<&'a str>, F: Parser<&'a str, O, E>>(
    f: F,
) -> impl Parser<&'a str, O, E> {
    terminated(f, multispace0)
}

#[allow(dead_code)]
fn dbg_in<'a, O, E: ParseError<&'a str>, F: Parser<&'a str, O, E>>(
    mut f: F,
) -> impl Parser<&'a str, O, E>
where
    O: std::fmt::Debug,
    E: std::fmt::Debug,
{
    move |input: &'a str| {
        println!("[dbg] {}", input);
        f.parse(input)
    }
}

#[allow(dead_code)]
fn dbg_out<'a, O, E: ParseError<&'a str>, F: Parser<&'a str, O, E>>(
    mut f: F,
) -> impl Parser<&'a str, O, E>
where
    O: std::fmt::Debug,
    E: std::fmt::Debug,
{
    move |input: &'a str| {
        let r = f.parse(input);
        println!("[dbg] {:?}", r);
        r
    }
}

type ParseResult<'a, O> = IResult<&'a str, O, VerboseError<&'a str>>;

pub fn parse_name(i: &str) -> ParseResult<String> {
    verify(
        map(
            take_while1(|c| char::is_alphanumeric(c) || c == '_'),
            |s: &str| String::from(s),
        ),
        |s: &String| {
            s != "as"
                && s != "import"
                && s != "new"
                && s != "scope"
                && s != "true"
                && s != "false"
                && s != "fact"
                && s != "forall"
        },
    )(i)
}

fn parse_fact_value(i: &str) -> ParseResult<Expr> {
    alt((
        map(ws(tag("true")), |_| Expr::True),
        map(ws(tag("false")), |_| Expr::False),
    ))(i)
}

fn parse_term(i: &str) -> ParseResult<Expr> {
    alt((
        parse_string_term_no_annotations(|s| {
            Expr::TermLiteral(aterms::base::Term::new_string_term(&s))
        }),
        parse_list_term_no_annotations(parse_expression, |args| Expr::Term(TermExpr::LTerm(args))),
        parse_recursive_term_no_annotations(parse_name, parse_expression, |con, args| {
            Expr::Term(TermExpr::RTerm(con, args))
        }),
        parse_tuple_term_no_annotations(parse_expression, |args| Expr::Term(TermExpr::TTerm(args))),
    ))(i)
}

fn parse_ters_invocation(i: &str) -> ParseResult<Expr> {
    map(
        context(
            "ters invocation",
            pair(
                preceded(ws(char('!')), cut(parse_name)),
                cut(parse_expression),
            ),
        ),
        |(strategy, arg)| Expr::InvokeTers(strategy, Box::from(arg)),
    )(i)
}

fn parse_expression(i: &str) -> ParseResult<Expr> {
    alt((
        map(pair(ws(tag("new")), ws(tag("scope"))), |_| Expr::MakeScope),
        parse_ters_invocation,
        parse_term,
        parse_fact_value,
        map(ws(parse_name), |n| Expr::Ref(n)),
    ))(i)
}

fn parse_assignment(i: &str) -> ParseResult<Clause> {
    map(
        tuple((parse_name, ws(tag(":=")), cut(parse_expression))),
        |(n, _, expr)| Clause::Let(n, expr),
    )(i)
}

fn parse_attribute_assignment(i: &str) -> ParseResult<Clause> {
    map(
        tuple((parse_name, ws(tag("+=")), cut(parse_expression))),
        |(n, _, expr)| Clause::AddAttr(n, expr),
    )(i)
}

fn parse_scope_edge(i: &str) -> ParseResult<Clause> {
    map(
        tuple((parse_expression, ws(tag("->")), cut(parse_expression))),
        |(a, _, b)| Clause::ScopeEdge(a, b),
    )(i)
}

fn parse_scope_query(i: &str) -> ParseResult<Clause> {
    map(
        tuple((parse_expression, ws(tag("-?>")), cut(parse_pattern))),
        |(a, _, b)| Clause::ScopeQuery(a, b),
    )(i)
}

fn parse_rule_invocation(i: &str) -> ParseResult<Clause> {
    map(
        tuple((ws(parse_name), many1(parse_expression))),
        |(name, params)| Clause::Invoke(name, params),
    )(i)
}

fn parse_map(i: &str) -> ParseResult<Clause> {
    map(
        context(
            "forall",
            tuple((
                ws(tag("forall")),
                delimited(ws(char('(')), parse_clause, ws(char(')'))),
                parse_expression,
            )),
        ),
        |(_, clause, expr)| Clause::ForAll(Box::from(clause), expr),
    )(i)
}

fn parse_not(i: &str) -> ParseResult<Clause> {
    map(
        preceded(
            ws(tag("not")),
            delimited(ws(char('(')), parse_clause, ws(char(')'))),
        ),
        |c| Clause::Not(Box::from(c)),
    )(i)
}

fn parse_equality(i: &str) -> ParseResult<Clause> {
    map(
        tuple((parse_expression, ws(char('=')), parse_expression)),
        |(a, _, b)| Clause::Equal(Box::from(a), Box::from(b)),
    )(i)
}

fn parse_clause(i: &str) -> ParseResult<Clause> {
    alt((
        parse_map,
        parse_not,
        parse_assignment,
        parse_attribute_assignment,
        parse_equality,
        parse_scope_edge,
        parse_scope_query,
        parse_rule_invocation,
        map(parse_expression, |e| Clause::Expr(e)),
    ))(i)
}

fn parse_message(i: &str) -> ParseResult<Message> {
    alt((
        map(
            preceded(ws(tag("error")), cut(aterms::shared::parse_string_literal)),
            |s| Message::Error(s),
        ),
        map(
            preceded(
                ws(tag("warning")),
                cut(aterms::shared::parse_string_literal),
            ),
            |s| Message::Warning(s),
        ),
    ))(i)
}

fn parse_clause_message(i: &str) -> ParseResult<Clause> {
    map(
        pair(
            parse_clause,
            opt(preceded(ws(char('|')), cut(parse_message))),
        ),
        |(c, m)| match m {
            Some(message) => Clause::WithMessage(Box::from(c), message),
            None => c,
        },
    )(i)
}

fn parse_conjunction(i: &str) -> ParseResult<Clause> {
    map(
        separated_list1(ws(char(',')), cut(parse_clause_message)),
        |clauses| Clause::Conjunction(clauses),
    )(i)
}

fn parse_pattern(i: &str) -> ParseResult<Pattern> {
    alt((
        map(
            context(
                "term pattern",
                pair(
                    ws_before(parse_name),
                    delimited(
                        ws_after(char('(')),
                        cut(separated_list0(ws(char(',')), parse_pattern)),
                        cut(ws(char(')'))),
                    ),
                ),
            ),
            |(n, ps)| Pattern::Term(n, ps),
        ),
        map(
            context(
                "array pattern",
                tuple((
                    ws_after(char('[')),
                    opt(pair(
                        parse_pattern,
                        opt(preceded(ws(char('|')), cut(parse_pattern))),
                    )),
                    cut(ws(char(']'))),
                )),
            ),
            |(_, patterns, _)| match patterns {
                Some((head, Some(tail_pattern))) => {
                    Pattern::ListCons(Box::from(head), Box::from(tail_pattern))
                }
                Some((head, None)) => Pattern::List(vec![head]),
                None => Pattern::List(vec![]),
            },
        ),
        map(
            tuple((ws(parse_name), ws(char('@')), parse_pattern)),
            |(name, _, inner)| Pattern::Bind(name, Box::from(inner)),
        ),
        map(ws(parse_name), |n| Pattern::Variable(n)),
        map(ws(aterms::shared::parse_string_literal), |s| {
            Pattern::String(s)
        }),
        map(
            delimited(
                ws_after(char('(')),
                cut(separated_list0(ws(char(',')), parse_pattern)),
                cut(ws(char(')'))),
            ),
            |ps| Pattern::Tuple(ps),
        ),
    ))(i)
}

fn parse_type_atom(i: &str) -> ParseResult<Type> {
    alt((
        map(ws(tag("scope")), |_| Type::Scope),
        map(ws(tag("fact")), |_| Type::Fact),
        map(ws(tag("term")), |_| Type::Term),
        map(ws(tag("edge")), |_| Type::Term),
    ))(i)
}

fn parse_tuple_type(i: &str) -> ParseResult<Type> {
    alt((
        map(
            delimited(
                ws(char('(')),
                separated_list0(ws(char(',')), parse_type),
                ws(char(')')),
            ),
            |ts| Type::Tuple(ts),
        ),
        parse_type_atom,
    ))(i)
}

fn parse_composite_type(i: &str) -> ParseResult<Type> {
    map(
        context(
            "type",
            pair(
                parse_tuple_type,
                opt(preceded(ws(char('*')), cut(parse_composite_type))),
            ),
        ),
        |(a, b)| match b {
            Some(t) => Type::Rule(Box::from(a), Box::from(t)),
            None => a,
        },
    )(i)
}

fn parse_type(i: &str) -> ParseResult<Type> {
    map(
        context(
            "type",
            pair(
                parse_composite_type,
                opt(preceded(ws(tag("->")), cut(parse_type))),
            ),
        ),
        |(a, b)| match b {
            Some(t) => Type::Rule(Box::from(a), Box::from(t)),
            None => a,
        },
    )(i)
}

fn parse_rule_declaration(i: &str) -> ParseResult<(String, Type)> {
    context(
        "rule declaration",
        pair(
            terminated(ws(parse_name), cut(ws(char(':')))),
            cut(parse_type),
        ),
    )(i)
}

fn parse_rule_variant(i: &str) -> ParseResult<RuleVariant> {
    map(
        context(
            "rule variant",
            tuple((
                ws(parse_name),
                many1(parse_pattern),
                opt(preceded(ws(char('=')), parse_expression)),
                opt(preceded(ws(tag(":-")), cut(parse_conjunction))),
                cut(ws(char('.'))),
            )),
        ),
        |(name, patterns, result, clause, _)| {
            RuleVariant::new_with_result(name, patterns, result, clause)
        },
    )(i)
}

fn parse_rule(i: &str) -> ParseResult<Rule> {
    map_res(
        pair(parse_rule_declaration, cut(many1(parse_rule_variant))),
        |((name, ty), variants)| {
            if !variants.iter().all(|d| d.name == name) {
                Err(nom::Err::Failure(
                    "Definitions must follow their respective declaration",
                ))
            } else {
                Ok(Rule::new(name, ty, variants))
            }
        },
    )(i)
}

fn parse_import(i: &str) -> ParseResult<String> {
    delimited(
        ws(tag("import")),
        aterms::shared::parse_string_literal,
        ws(char('.')),
    )(i)
}

pub fn parse_tecs_string(i: &str) -> Result<File, String> {
    match all_consuming(pair(opt(parse_import), many0(ws(parse_rule))))(i) {
        Ok((_, (import, rules))) => Ok(File {
            import,
            rules,
            filename: None,
        }),
        Err(nom::Err::Failure(err)) | Err(nom::Err::Error(err)) => {
            panic!("{}", convert_error(i, err));
        }
        Err(e) => {
            panic!("{}", e)
        }
    }
}

pub fn parse_tecs_file(filename: &str) -> Result<File, String> {
    let f = fs::read_to_string(filename).unwrap();
    let mut rw_file = parse_tecs_string(String::as_str(&f))?;
    rw_file.set_filename(String::from(filename));
    Ok(rw_file)
}

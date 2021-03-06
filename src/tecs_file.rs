use std::{cell::RefCell, fmt::Display, ops::Deref, rc::Rc};

use crate::interpreter::{Environment, Store};

#[derive(Debug)]
pub enum Type {
    Scope,
    Fact,
    Term,
    Rule(Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
}

pub type ScopeId = u64;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Scope(ScopeId),
    True,
    False,
    RTerm(String, Vec<ValueBox>, Vec<ValueBox>),
    LTerm(Vec<ValueBox>, Vec<ValueBox>),
    TTerm(Vec<ValueBox>, Vec<ValueBox>),
    STerm(String, Vec<ValueBox>),
    NTerm(f64, Vec<ValueBox>),
}

pub type ValueBox = Rc<RefCell<Value>>;

impl From<aterms::base::Term> for Value {
    fn from(t: aterms::base::Term) -> Self {
        match t {
            aterms::base::Term::RTerm(rterm) => Self::RTerm(
                rterm.constructor,
                rterm
                    .terms
                    .into_iter()
                    .map(|t| Value::from(t).into())
                    .collect(),
                rterm
                    .annotations
                    .elems
                    .into_iter()
                    .map(|t| Value::from(t).into())
                    .collect(),
            ),
            aterms::base::Term::STerm(sterm) => Self::STerm(
                sterm.value,
                sterm
                    .annotations
                    .elems
                    .into_iter()
                    .map(|t| Value::from(t).into())
                    .collect(),
            ),
            aterms::base::Term::NTerm(nterm) => Self::NTerm(
                nterm.value,
                nterm
                    .annotations
                    .elems
                    .into_iter()
                    .map(|t| Value::from(t).into())
                    .collect(),
            ),
            aterms::base::Term::TTerm(tterm) => Self::TTerm(
                tterm
                    .terms
                    .into_iter()
                    .map(|t| Value::from(t).into())
                    .collect(),
                tterm
                    .annotations
                    .elems
                    .into_iter()
                    .map(|t| Value::from(t).into())
                    .collect(),
            ),
            aterms::base::Term::LTerm(lterm) => Self::LTerm(
                lterm
                    .terms
                    .into_iter()
                    .map(|t| Value::from(t).into())
                    .collect(),
                lterm
                    .annotations
                    .elems
                    .into_iter()
                    .map(|t| Value::from(t).into())
                    .collect(),
            ),
        }
    }
}

impl Into<ValueBox> for Value {
    fn into(self) -> ValueBox {
        Rc::new(RefCell::from(self))
    }
}

impl From<&ValueBox> for Value {
    fn from(vb: &ValueBox) -> Value {
        Value::from(RefCell::<Value>::borrow(vb).clone())
    }
}

impl Value {
    pub fn add_attribute(&mut self, attribute: ValueBox) {
        match RefCell::borrow(&attribute).deref() {
            Value::RTerm(_, _, _) => match self {
                Value::RTerm(_, _, attr)
                | Value::LTerm(_, attr)
                | Value::TTerm(_, attr)
                | Value::STerm(_, attr)
                | Value::NTerm(_, attr) => attr.push(attribute.clone()),
                _ => panic!("Can only add attribute to term value"),
            },
            _ => panic!("Invalid attribute value - must be recursive term"),
        }
    }

    pub fn into_aterm(&self, store: &Store) -> aterms::base::Term {
        use aterms::base::Term;
        match self {
            Value::Scope(s) => Term::new_rec_term("Scope", vec![Term::new_number_term(*s as f64)]),
            Value::True => Term::new_rec_term("True", vec![]),
            Value::False => Term::new_rec_term("True", vec![]),
            Value::RTerm(con, subterms, annots) => Term::new_anot_rec_term(
                con.as_str(),
                subterms
                    .into_iter()
                    .map(|t| Value::from(t).into_aterm(store))
                    .collect(),
                aterms::base::Annotations::from(
                    annots
                        .into_iter()
                        .map(|t| Value::from(t).into_aterm(store))
                        .collect(),
                ),
            ),
            Value::LTerm(subterms, annots) => Term::new_anot_list_term(
                subterms
                    .into_iter()
                    .map(|t| Value::from(t).into_aterm(store))
                    .collect(),
                aterms::base::Annotations::from(
                    annots
                        .into_iter()
                        .map(|t| Value::from(t).into_aterm(store))
                        .collect(),
                ),
            ),
            Value::TTerm(subterms, annots) => Term::new_anot_tuple_term(
                subterms
                    .into_iter()
                    .map(|t| Value::from(t).into_aterm(store))
                    .collect(),
                aterms::base::Annotations::from(
                    annots
                        .into_iter()
                        .map(|t| Value::from(t).into_aterm(store))
                        .collect(),
                ),
            ),
            Value::STerm(s, annots) => Term::new_anot_string_term(
                s.as_str(),
                aterms::base::Annotations::from(
                    annots
                        .into_iter()
                        .map(|t| Value::from(t).into_aterm(store))
                        .collect(),
                ),
            ),
            Value::NTerm(n, annots) => Term::new_anot_number_term(
                *n,
                aterms::base::Annotations::from(
                    annots
                        .into_iter()
                        .map(|t| Value::from(t).into_aterm(store))
                        .collect(),
                ),
            ),
        }
    }

    pub fn to_string(&self, store: &Store) -> String {
        match self {
            Value::Scope(s) => format!("Scope({})", s),
            Value::True => format!("true"),
            Value::False => format!("false"),
            Value::RTerm(con, subterms, annots) => {
                let mut r = String::from(con.as_str()) + "(";
                let mut iter = subterms.iter();
                match iter.next() {
                    Some(first) => {
                        r += RefCell::borrow(first).to_string(store).as_str();
                        for subterm in iter {
                            r += ", ";
                            r += RefCell::borrow(subterm).to_string(store).as_str();
                        }
                    }
                    None => {}
                }
                r += ")";
                let mut iter = annots.iter();
                match iter.next() {
                    Some(first) => {
                        r += "{";
                        r += RefCell::borrow(first).to_string(store).as_str();
                        for subterm in iter {
                            r += ", ";
                            r += RefCell::borrow(subterm).to_string(store).as_str();
                        }
                        r += "}";
                    }
                    None => {}
                }
                r
            }
            Value::LTerm(subterms, annots) => {
                let mut r = String::from("[");
                let mut iter = subterms.iter();
                match iter.next() {
                    Some(first) => {
                        r += RefCell::borrow(first).to_string(store).as_str();
                        for subterm in iter {
                            r += ", ";
                            r += RefCell::borrow(subterm).to_string(store).as_str();
                        }
                    }
                    None => {}
                }
                r += "]";
                let mut iter = annots.iter();
                match iter.next() {
                    Some(first) => {
                        r += "{";
                        r += RefCell::borrow(first).to_string(store).as_str();
                        for subterm in iter {
                            r += ", ";
                            r += RefCell::borrow(subterm).to_string(store).as_str();
                        }
                        r += "}";
                    }
                    None => {}
                }
                r
            }
            Value::TTerm(subterms, annots) => {
                let mut r = String::from("(");
                let mut iter = subterms.iter();
                match iter.next() {
                    Some(first) => {
                        r += RefCell::borrow(first).to_string(store).as_str();
                        for subterm in iter {
                            r += ", ";
                            r += RefCell::borrow(subterm).to_string(store).as_str();
                        }
                    }
                    None => {}
                }
                r += ")";
                let mut iter = annots.iter();
                match iter.next() {
                    Some(first) => {
                        r += "{";
                        r += RefCell::borrow(first).to_string(store).as_str();
                        for subterm in iter {
                            r += ", ";
                            r += RefCell::borrow(subterm).to_string(store).as_str();
                        }
                        r += "}";
                    }
                    None => {}
                }
                r
            }
            Value::STerm(s, annots) => {
                let mut r = String::from("\"") + s + "\"";
                let mut iter = annots.iter();
                match iter.next() {
                    Some(first) => {
                        r += "{";
                        r += RefCell::borrow(first).to_string(store).as_str();
                        for subterm in iter {
                            r += ", ";
                            r += RefCell::borrow(subterm).to_string(store).as_str();
                        }
                        r += "}";
                    }
                    None => {}
                }

                r
            }
            Value::NTerm(n, annots) => {
                let mut r = n.to_string();
                let mut iter = annots.iter();
                match iter.next() {
                    Some(first) => {
                        r += "{";
                        r += RefCell::borrow(first).to_string(store).as_str();
                        for subterm in iter {
                            r += ", ";
                            r += RefCell::borrow(subterm).to_string(store).as_str();
                        }
                        r += "}";
                    }
                    None => {}
                }

                r
            }
        }
    }
}

#[derive(Debug)]
pub struct File {
    pub filename: Option<String>,
    pub import: Option<String>,
    pub rules: Vec<Rule>,
}

impl File {
    pub fn new() -> Self {
        Self {
            import: None,
            filename: None,
            rules: vec![],
        }
    }

    pub fn set_filename(&mut self, name: String) {
        self.filename = Some(name);
    }
}

#[derive(Debug)]
pub struct Rule {
    pub name: String,
    pub signature: Type,
    pub variants: Vec<RuleVariant>,
}

impl Rule {
    pub fn new(name: String, signature: Type, variants: Vec<RuleVariant>) -> Self {
        Self {
            name,
            signature,
            variants,
        }
    }
}

#[derive(Debug)]
pub struct RuleVariant {
    pub name: String,
    pub patterns: Vec<Pattern>,
    pub result: Option<Expr>,
    pub clause: Option<Clause>,
}

impl RuleVariant {
    pub fn new(name: String, patterns: Vec<Pattern>, clause: Option<Clause>) -> Self {
        Self {
            name,
            patterns,
            result: None,
            clause,
        }
    }

    pub fn new_with_result(
        name: String,
        patterns: Vec<Pattern>,
        result: Option<Expr>,
        clause: Option<Clause>,
    ) -> Self {
        Self {
            name,
            patterns,
            result,
            clause,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    MakeScope,
    True,
    False,
    Term(TermExpr),
    TermLiteral(aterms::base::Term),
    Ref(String),
    InvokeTers(String, Box<Expr>),
}

#[derive(Debug, Clone)]
pub enum TermExpr {
    RTerm(String, Vec<Expr>),
    TTerm(Vec<Expr>),
    LTerm(Vec<Expr>),
}

#[derive(Debug)]
pub enum Clause {
    All(Vec<Clause>),
    Any(Vec<Clause>),
    Let(String, Expr),
    AddAttr(String, Expr),
    Expr(Expr),
    ScopeEdge(Expr, Expr),
    LabeledScopeEdge(Expr, Expr, Expr),
    ScopeQuery(Expr, Pattern),
    AnnotScopeQuery(Expr, Expr, Pattern),
    Invoke(String, Vec<Expr>),
    ForAll(Box<Clause>, Expr),
    Not(Box<Clause>),
    Equal(Box<Expr>, Box<Expr>),
    WithMessage(Box<Clause>, Message),
}

#[derive(Debug, Clone)]
pub enum Message {
    Error(String),
    Warning(String),
    Debug(Expr),
}

impl Display for Message {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Message::Error(e) => write!(f, "Error: {}", e),
            Message::Warning(w) => write!(f, "Warning: {}", w),
            Message::Debug(d) => write!(f, "Debug: {:?}", d),
        }
    }
}

#[derive(Debug)]
pub enum Pattern {
    Term(String, Vec<Pattern>),
    Tuple(Vec<Pattern>),
    ListCons(Box<Pattern>, Box<Pattern>),
    List(Vec<Pattern>),
    Variable(String),
    String(String),
    Bind(String, Box<Pattern>),
}

impl Pattern {
    pub fn expand_to_string(&self, store: &Store, env: &Environment) -> String {
        let mut res = String::new();
        match self {
            Pattern::Term(con, subpatterns) => {
                res += format!("{}(", con).as_str();
                let mut iter = subpatterns.iter();
                match iter.next() {
                    Some(first) => {
                        res += format!("{}", first.expand_to_string(store, env)).as_str();
                        for subterm in iter {
                            res += format!(", {}", subterm.expand_to_string(store, env)).as_str();
                        }
                    }
                    None => {}
                }
                res += format!(")").as_str();
            }
            Pattern::Tuple(subpatterns) => {
                res += format!("(").as_str();
                let mut iter = subpatterns.iter();
                match iter.next() {
                    Some(first) => {
                        res += format!("{}", first.expand_to_string(store, env)).as_str();
                        for subterm in iter {
                            res += format!(", {}", subterm.expand_to_string(store, env)).as_str();
                        }
                    }
                    None => {}
                }
                res += format!(")").as_str();
            }
            Pattern::Variable(v) => {
                if let Some(value) = env.get(v) {
                    let borrowed_value = RefCell::borrow(&value);
                    res += (*borrowed_value).to_string(store).as_str();
                } else {
                    res += format!("{}", v).as_str();
                }
            }
            Pattern::String(s) => {
                res += format!("\"{}\"", s).as_str();
            }
            Pattern::Bind(v, expr) => {
                res += format!("{}@{}", v, expr.expand_to_string(store, env)).as_str();
            }
            Pattern::ListCons(head, tail) => {
                res += format!(
                    "[{}|{}]",
                    head.expand_to_string(store, env),
                    tail.expand_to_string(store, env)
                )
                .as_str();
            }
            Pattern::List(subpatterns) => {
                res += format!("[").as_str();
                let mut iter = subpatterns.iter();
                match iter.next() {
                    Some(first) => {
                        res += format!("{}", first.expand_to_string(store, env)).as_str();
                        for subterm in iter {
                            res += format!(", {}", subterm.expand_to_string(store, env)).as_str();
                        }
                    }
                    None => {}
                }
                res += format!("]").as_str();
            }
        }
        res
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Term(con, subterms) => {
                write!(f, "{}(", con)?;
                let mut iter = subterms.iter();
                match iter.next() {
                    Some(first) => {
                        write!(f, "{}", first)?;
                        for subterm in iter {
                            write!(f, ", {}", subterm)?;
                        }
                    }
                    None => {}
                }
                write!(f, ")")?;
            }
            Pattern::Tuple(subterms) => {
                write!(f, "(")?;
                let mut iter = subterms.iter();
                match iter.next() {
                    Some(first) => {
                        write!(f, "{}", first)?;
                        for subterm in iter {
                            write!(f, ", {}", subterm)?;
                        }
                    }
                    None => {}
                }
                write!(f, ")")?;
            }
            Pattern::Variable(v) => write!(f, "{}", v)?,
            Pattern::String(s) => write!(f, "\"{}\"", s)?,
            Pattern::Bind(con, inner) => write!(f, "{}@{}", con, inner)?,
            Pattern::ListCons(head, tail) => write!(f, "[{}|{}]", head, tail)?,
            Pattern::List(subpatterns) => {
                write!(f, "[")?;
                let mut iter = subpatterns.iter();
                match iter.next() {
                    Some(first) => {
                        write!(f, "{}", first)?;
                        for subterm in iter {
                            write!(f, ", {}", subterm)?;
                        }
                    }
                    None => {}
                }
                write!(f, "]")?;
            }
        }
        Ok(())
    }
}

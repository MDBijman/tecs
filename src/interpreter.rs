use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Display,
    ops::{Deref, DerefMut},
};

use crate::{
    parser::parse_tecs_file,
    parser::parse_tecs_string,
    tecs_file::{Clause, Expr, File, Message, Pattern, Rule, ScopeId, TermExpr, Value, ValueBox},
};
use aterms::base::Term;
use ters::{parse_rewrite_file, Rewriter};

#[derive(Debug, Default)]
pub struct ClauseFailure {
    messages: Vec<Message>,
}

impl ClauseFailure {
    pub fn from_error_string(message: &str) -> Self {
        Self {
            messages: vec![Message::Error(String::from(message))],
        }
    }

    pub fn from_warning_string(message: &str) -> Self {
        Self {
            messages: vec![Message::Warning(String::from(message))],
        }
    }

    pub fn from_message(message: Message) -> Self {
        Self {
            messages: vec![message],
        }
    }

    pub fn extend_with(&mut self, message: Message) {
        self.messages.push(message);
    }

    pub fn extend_with_clause_failure(&mut self, other: ClauseFailure) {
        for message in other.messages {
            self.messages.push(message);
        }
    }
}

impl Display for ClauseFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for message in &self.messages {
            write!(f, "{}\n", message)?;
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct RuleFailure {
    clause_failures: Vec<ClauseFailure>,
    message: String,
}

impl RuleFailure {
    pub fn extend_with(&mut self, cf: ClauseFailure) {
        self.clause_failures.push(cf);
    }

    pub fn from_message(message: String) -> Self {
        Self {
            clause_failures: vec![],
            message,
        }
    }

    pub fn with_message(&mut self, message: String) {
        self.message = message;
    }
}

impl Display for RuleFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)?;
        for clause_failure in &self.clause_failures {
            write!(f, "{}", clause_failure)?;
        }
        Ok(())
    }
}

impl From<ClauseFailure> for RuleFailure {
    fn from(cf: ClauseFailure) -> Self {
        let mut cl = RuleFailure::default();
        cl.extend_with(cf);
        cl
    }
}

fn print_args(store: &Store, args: Vec<ValueBox>) -> String {
    let mut res = String::new();
    res += "[";
    let mut iter = args.iter();
    match iter.next() {
        Some(first) => {
            res += RefCell::borrow(first).to_string(store).as_str();
            for val in iter {
                res += ", ";
                res += RefCell::borrow(val).to_string(store).as_str();
            }
        }
        None => {}
    }
    res += "]";
    res
}

pub struct Interpreter {
    file: File,
    ters: Option<Rewriter>,
}

impl Interpreter {
    pub fn new(tecs_file: &str) -> Self {
        let f: File = parse_tecs_file(tecs_file).unwrap();
        Self {
            ters: match &f.import {
                Some(name) => Some(Rewriter::new_with_prelude(
                    parse_rewrite_file(name.as_str()).expect("File not found"),
                )),
                None => None,
            },
            file: f,
        }
    }

    pub fn new_from_string(tecs_file: &str) -> Self {
        let f: File = parse_tecs_string(tecs_file).unwrap();
        Self {
            ters: match &f.import {
                Some(name) => Some(Rewriter::new_with_prelude(
                    parse_rewrite_file(name.as_str()).expect("File not found"),
                )),
                None => None,
            },
            file: f,
        }
    }

    fn get_rule(&self, name: &str) -> Option<&Rule> {
        self.file.rules.iter().find(|r| r.name == name)
    }

    pub fn run(&self, term: Term, rule_name: &str) -> Result<Term, RuleFailure> {
        if let Some(rule) = self.get_rule(rule_name) {
            let mut store = Store::default();
            let rc = ValueBox::from(RefCell::from(Value::from(term)));
            match self.try_rule(&mut store, rule, vec![rc.clone()]) {
                Err(e) => Err(e),
                Ok(()) => Ok(RefCell::borrow(&rc).deref().into_aterm(&store)),
            }
        } else {
            Err(RuleFailure::from_message(String::from(
                "No rule with given name",
            )))
        }
    }

    fn try_rule(
        &self,
        store: &mut Store,
        rule: &Rule,
        params: Vec<ValueBox>,
    ) -> Result<(), RuleFailure> {
        'outer: for variant in &rule.variants {
            let mut env: Environment = Environment::default();
            for (pattern, value) in variant.patterns.iter().zip(params.iter()) {
                if let Some(bindings) =
                    Interpreter::try_pattern(&env, store, &pattern, value.clone())
                {
                    env.bindings.extend(bindings);
                } else {
                    continue 'outer;
                }
            }

            match &variant.clause {
                Some(c) => {
                    return self
                        .try_clause(&mut env, store, &c)
                        .or_else(|cf| Err(cf.into()));
                }
                None => {
                    return Ok(());
                }
            }
        }

        Err(RuleFailure::from_message(format!(
            "No matching {} variant for args {}",
            rule.name,
            print_args(store, params)
        )))
    }

    fn try_pattern(
        env: &Environment,
        store: &Store,
        pat: &Pattern,
        value_ref: ValueBox,
    ) -> Option<HashMap<String, ValueBox>> {
        let value = RefCell::borrow(&value_ref);

        match pat {
            Pattern::Term(n, ps) => match value.deref() {
                Value::RTerm(constructor, terms, _) => {
                    if n == constructor && ps.len() == terms.len() {
                        let mut bindings = HashMap::new();
                        for (subpattern, subterm) in ps.iter().zip(terms.iter()) {
                            if let Some(subbindings) =
                                Interpreter::try_pattern(env, store, subpattern, subterm.clone())
                            {
                                bindings.extend(subbindings.into_iter());
                            } else {
                                return None;
                            }
                        }
                        Some(bindings)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            Pattern::Variable(n) => match env.get(n) {
                Some(matched_value) => {
                    if matched_value == value_ref {
                        return Some(HashMap::new());
                    } else {
                        return None;
                    }
                }
                None => {
                    let mut r = HashMap::new();
                    r.insert(n.clone(), value_ref.clone());
                    Some(r)
                }
            },
            Pattern::String(s) => match value.deref() {
                Value::STerm(v, _) => {
                    if v == s {
                        Some(HashMap::new())
                    } else {
                        None
                    }
                }
                _ => None,
            },
            Pattern::Tuple(subpatterns) => match value.deref() {
                Value::TTerm(terms, _) => {
                    if subpatterns.len() == terms.len() {
                        let mut bindings = HashMap::new();
                        for (subpattern, subterm) in subpatterns.iter().zip(terms.iter()) {
                            if let Some(subbindings) =
                                Interpreter::try_pattern(env, store, subpattern, subterm.clone())
                            {
                                bindings.extend(subbindings.into_iter());
                            } else {
                                return None;
                            }
                        }
                        Some(bindings)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            Pattern::Bind(name, inner) => {
                match Interpreter::try_pattern(env, store, inner, value_ref.clone()) {
                    Some(mut matched) => {
                        matched.insert(name.clone(), value_ref.clone());
                        Some(matched)
                    }
                    None => None,
                }
            }
            Pattern::ListCons(head_pattern, tail_pattern) => match value.deref() {
                Value::LTerm(terms, _) => {
                    let mut iter = terms.iter();
                    let head = iter.next()?;
                    let mut head_match =
                        Interpreter::try_pattern(env, store, head_pattern, head.clone())?;
                    let tail_match = Interpreter::try_pattern(
                        env,
                        store,
                        tail_pattern,
                        Value::LTerm(iter.map(|v| v.clone()).collect(), vec![]).into(),
                    )?;
                    head_match.extend(tail_match);
                    Some(head_match)
                }
                _ => None,
            },
            Pattern::List(subpatterns) => match value.deref() {
                Value::LTerm(terms, _) => {
                    if terms.len() != subpatterns.len() {
                        None
                    } else {
                        let mut bindings = HashMap::<String, ValueBox>::new();
                        for (subterm, subpattern) in terms.iter().zip(subpatterns.iter()) {
                            bindings.extend(Interpreter::try_pattern(
                                env,
                                store,
                                subpattern,
                                subterm.clone(),
                            )?);
                        }
                        Some(bindings)
                    }
                }
                _ => None,
            },
        }
    }

    fn try_clause(
        &self,
        env: &mut Environment,
        store: &mut Store,
        clause: &Clause,
    ) -> Result<(), ClauseFailure> {
        match clause {
            Clause::All(clauses) => {
                for clause in clauses {
                    self.try_clause(env, store, clause)?;
                }

                Ok(())
            }
            Clause::Any(clauses) => {
                let mut failure_res =
                    ClauseFailure::from_error_string("None of the clauses succeeded");

                for clause in clauses {
                    match self.try_clause(env, store, clause) {
                        Ok(()) => return Ok(()),
                        Err(cf) => {
                            failure_res.extend_with_clause_failure(cf);
                            continue;
                        }
                    }
                }

                Err(failure_res)
            }
            Clause::Let(name, expr) => {
                let v = self.interp_expr(env, store, expr).or(Err(
                    ClauseFailure::from_error_string("Failed to compute let"),
                ))?;
                env.put(name.clone(), v.into());
                Ok(())
            }
            Clause::Expr(e) => self
                .interp_expr(env, store, e)
                .and_then(|_| Ok(()))
                .or_else(|_| {
                    Err(ClauseFailure::from_error_string(
                        "Failed to compute expression",
                    ))
                }),
            Clause::ScopeEdge(l, r) => {
                let left_result = self.interp_expr(env, store, l).or_else(|_| {
                    Err(ClauseFailure::from_error_string(
                        format!("Failed to compute scope edge lhs: {:?}", l).as_str(),
                    ))
                })?;
                let right_result =
                    self.interp_expr(env, store, r)
                        .or(Err(ClauseFailure::from_error_string(
                            "Failed to compute scope edge rhs",
                        )))?;
                let x = match (
                    (*left_result).borrow().deref(),
                    (*right_result).borrow().deref(),
                ) {
                    (Value::Scope(left_id), Value::Scope(right_id)) => {
                        store.make_edge(*left_id, *right_id);
                        Ok(())
                    }
                    (Value::Scope(scope), _) => {
                        store.associate_value(*scope, right_result.clone());
                        Ok(())
                    }
                    _ => Err(ClauseFailure::from_error_string(
                        "Failed to create scope edge",
                    )),
                };
                x
            }
            Clause::LabeledScopeEdge(l, annot, r) => {
                let left_result = self.interp_expr(env, store, l).or_else(|_| {
                    Err(ClauseFailure::from_error_string(
                        format!("Failed to compute scope edge lhs: {:?}", l).as_str(),
                    ))
                })?;
                let label_result = self.interp_expr(env, store, annot).or(Err(
                    ClauseFailure::from_error_string("Failed to compute scope label"),
                ))?;
                let right_result =
                    self.interp_expr(env, store, r)
                        .or(Err(ClauseFailure::from_error_string(
                            "Failed to compute scope edge rhs",
                        )))?;
                let x = match (
                    (*left_result).borrow().deref(),
                    (*label_result).borrow().deref(),
                    (*right_result).borrow().deref(),
                ) {
                    (Value::Scope(left_id), Value::STerm(s, _), Value::Scope(right_id)) => {
                        store.make_labeled_edge(*left_id, s.clone(), *right_id);
                        Ok(())
                    }
                    (Value::Scope(_), _, _) => Err(ClauseFailure::from_error_string(
                        "Cannot create scope edge to declaration with label",
                    )),
                    _ => Err(ClauseFailure::from_error_string(
                        "Failed to create scope edge",
                    )),
                };
                x
            }
            Clause::ScopeQuery(l, r) => {
                let left_result =
                    self.interp_expr(env, store, l)
                        .or(Err(ClauseFailure::from_error_string(
                            "Failed to compute expression",
                        )))?;

                let x = match (*left_result).borrow().deref() {
                    Value::Scope(left_id) => {
                        match store.query_scope_graph(env, store, *left_id, r) {
                            Some((_, bindings)) => {
                                env.bindings.extend(bindings);
                                Ok(())
                            }
                            _ => Err(ClauseFailure::from_error_string(
                                format!(
                                    "Scope query on scope {} for {} failed\n{}",
                                    left_id,
                                    r.expand_to_string(store, env),
                                    store.scope_graph.to_string(store)
                                )
                                .as_str(),
                            )),
                        }
                    }
                    _ => Err(ClauseFailure::from_error_string(
                        "Scope query must have scope as left-hand side",
                    )),
                };
                x
            }
            Clause::AnnotScopeQuery(l, stack, r) => {
                let left_result =
                    self.interp_expr(env, store, l)
                        .or(Err(ClauseFailure::from_error_string(
                            "Failed to compute expression",
                        )))?;

                let stack_result = self.interp_expr(env, store, stack).or(Err(
                    ClauseFailure::from_error_string("Failed to compute expression"),
                ))?;

                let mut edge_labels = Vec::new();
                match stack_result.borrow().deref() {
                    Value::LTerm(elems, _) => {
                        for elem in elems.iter().rev() {
                            match elem.borrow().deref() {
                                Value::STerm(s, _) => edge_labels.push(s.clone()),
                                _ => {
                                    return Err(ClauseFailure::from_error_string(
                                        format!("Only strings are allowed as edge labels",)
                                            .as_str(),
                                    ))
                                }
                            }
                        }
                    }
                    _ => todo!(),
                };

                let x = match (*left_result).borrow().deref() {
                    Value::Scope(left_id) => {
                        match store.annotated_query_scope_graph(env, store, *left_id, r, edge_labels) {
                            Some((_, bindings)) => {
                                env.bindings.extend(bindings);
                                Ok(())
                            }
                            _ => Err(ClauseFailure::from_error_string(
                                format!(
                                    "Annotated scope query on scope {} for {} with annotations {:?} failed\n{}",
                                    left_id,
                                    r.expand_to_string(store, env),
                                    stack_result.borrow().deref(),
                                    store.scope_graph.to_string(store)
                                )
                                .as_str(),
                            )),
                        }
                    }
                    _ => Err(ClauseFailure::from_error_string(
                        "Scope query must have scope as left-hand side",
                    )),
                };
                x
            }
            Clause::Invoke(name, exprs) => {
                let rule = self
                    .get_rule(name.as_str())
                    .expect(format!("No rule {}", name).as_str());
                let mut values = Vec::new();
                for e in exprs {
                    values.push(
                        self.interp_expr(env, store, e)
                            .or(Err(ClauseFailure::from_error_string(
                                "Failed to compute expression",
                            )))?
                            .into(),
                    );
                }
                match self.try_rule(store, rule, values) {
                    Ok(r) => Ok(r),
                    Err(e) => Err(ClauseFailure::from_error_string(
                        format!("Failed to compute rule {}\n{}", rule.name, e).as_str(),
                    )),
                }
            }
            Clause::ForAll(clause, list_arg) => match clause.as_ref() {
                Clause::Invoke(name, args) => {
                    // Interp the static arguments
                    let mut values = Vec::new();
                    for e in args {
                        values.push(
                            self.interp_expr(env, store, e)
                                .or(Err(ClauseFailure::from_error_string(
                                    "Failed to compute argument",
                                )))?
                                .into(),
                        );
                    }

                    // Get the referenced rule
                    let rule = match self.get_rule(name) {
                        Some(r) => r,
                        None => {
                            return Err(ClauseFailure::from_error_string(
                                format!("No {} rule", name).as_str(),
                            ))
                        }
                    };

                    // Check that the mapped arg is a list
                    let arg_value = self.interp_expr(env, store, list_arg).or(Err(
                        ClauseFailure::from_error_string("Failed to compute expression"),
                    ))?;

                    match arg_value.clone().deref().borrow().deref() {
                        Value::LTerm(computed_terms, annots) => {
                            assert!(annots.is_empty());
                            for term in computed_terms {
                                let mut cloned = values.clone();
                                cloned.push(term.clone());

                                match self.try_rule(store, rule, cloned) {
                                    Ok(()) => {}
                                    Err(e) => {
                                        return Err(ClauseFailure::from_error_string(
                                            format!("Failed to map rule {}\n{}", rule.name, e)
                                                .as_str(),
                                        ))
                                    }
                                }
                            }

                            Ok(())
                        }
                        v => panic!("Cannot map over this type: {}", v.to_string(store)),
                    }
                }
                _ => panic!("Not a mappable rule"),
            },
            Clause::Not(c) => match self.try_clause(env, store, c) {
                Ok(()) => Err(ClauseFailure::default()),
                Err(_) => Ok(()),
            },
            Clause::Equal(lhs, rhs) => match (
                self.interp_expr(env, store, lhs)
                    .or(Err(ClauseFailure::from_error_string(
                        "Failed to compute expression",
                    )))?,
                self.interp_expr(env, store, rhs)
                    .or(Err(ClauseFailure::from_error_string(
                        "Failed to compute expression",
                    )))?,
            ) {
                (a, b) if a == b => Ok(()),
                (a, b) => {
                    let lhs_string = RefCell::borrow(&a).deref().to_string(store);
                    let rhs_string = RefCell::borrow(&b).deref().to_string(store);
                    Err(ClauseFailure::from_error_string(
                        format!("Equality not satisfied: {} = {}", lhs_string, rhs_string).as_str(),
                    ))
                }
            },
            Clause::WithMessage(inner_clause, message) => match message {
                Message::Error(_) | Message::Warning(_) => {
                    match self.try_clause(env, store, inner_clause) {
                        Ok(()) => Ok(()),
                        Err(mut f) => Err({
                            f.extend_with(message.clone());
                            f
                        }),
                    }
                }
                Message::Debug(d) => {
                    let res = self.try_clause(env, store, inner_clause);
                    match self.interp_expr(env, store, d) {
                        Ok(debug_res) => {
                            println!("{}", debug_res.deref().borrow().to_string(store))
                        }
                        Err(err) => println!("{}", err),
                    }
                    res
                }
            },
            Clause::AddAttr(var, expr) => {
                let value = self.interp_expr(env, store, expr).or(Err(
                    ClauseFailure::from_error_string("Failed to compute expression"),
                ))?;

                match env.get(&var) {
                    Some(v) => {
                        RefCell::borrow_mut(&v).deref_mut().add_attribute(value);
                    }
                    None => {
                        return Err(ClauseFailure::from_error_string(
                            format!("Undefined reference {}", var).as_str(),
                        ))
                    }
                };

                Ok(())
            }
        }
    }

    fn interp_expr(
        &self,
        env: &Environment,
        store: &mut Store,
        expr: &Expr,
    ) -> Result<ValueBox, String> {
        match expr {
            Expr::True => Ok(Value::True.into()),
            Expr::False => Ok(Value::False.into()),
            Expr::MakeScope => Ok(Value::Scope(store.make_scope()).into()),
            Expr::TermLiteral(t) => Ok(Value::from(t.clone()).into()),
            Expr::Ref(n) => match env.get(&n) {
                Some(v) => Ok(v.clone()),
                None => Err(format!("Undefined reference {}", n)),
            },
            Expr::InvokeTers(name, arg) => {
                let arg_value = self.interp_expr(env, store, arg)?;
                let ters_arg: Term = RefCell::borrow(&arg_value).into_aterm(store);
                match self
                    .ters
                    .as_ref()
                    .expect("Invoking Ters rule without imports")
                    .clone()
                    .rewrite_with_rule(ters_arg, name.as_str())
                {
                    Ok(res) => Ok(Value::from(res).into()),
                    Err(message) => Err(message),
                }
            }
            Expr::Term(TermExpr::RTerm(con, subexpressions)) => {
                let mut computed_subterms = Vec::new();
                for expr in subexpressions {
                    match self.interp_expr(env, store, expr) {
                        Ok(t) => {
                            computed_subterms.push(t);
                        }
                        Err(e) => return Err(e),
                    }
                }
                Ok(Value::RTerm(con.clone(), computed_subterms, vec![]).into())
            }
            Expr::Term(TermExpr::TTerm(subexpressions)) => {
                let mut computed_subterms = Vec::new();
                for expr in subexpressions {
                    match self.interp_expr(env, store, expr) {
                        Ok(t) => {
                            computed_subterms.push(t);
                        }
                        Err(e) => return Err(e),
                    }
                }
                Ok(Value::TTerm(computed_subterms, vec![]).into())
            }
            Expr::Term(TermExpr::LTerm(subexpressions)) => {
                let mut computed_subterms = Vec::new();
                for expr in subexpressions {
                    match self.interp_expr(env, store, expr) {
                        Ok(t) => {
                            computed_subterms.push(t);
                        }
                        Err(e) => return Err(e),
                    }
                }
                Ok(Value::LTerm(computed_subterms, vec![]).into())
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct ScopeGraph {
    scopes: Vec<ScopeId>,
    edges: HashMap<ScopeId, Vec<ScopeId>>,
    edge_labels: HashMap<(ScopeId, ScopeId), String>,
    scope_values: HashMap<ScopeId, Vec<ValueBox>>,
    next_scope: ScopeId,
}

type QueryResult<'a> = (ValueBox, HashMap<String, ValueBox>);

impl ScopeGraph {
    fn query(
        &self,
        env: &Environment,
        store: &Store,
        scope: ScopeId,
        r: &Pattern,
    ) -> Option<QueryResult> {
        let assoc_values = self.scope_values.get(&scope)?;
        for value in assoc_values {
            if let Some(bindings) = Interpreter::try_pattern(env, store, r, value.clone()) {
                return Some((value.clone(), bindings));
            }
        }

        for neighbour in self.edges.get(&scope)? {
            if let Some(value) = self.query(env, store, *neighbour, r) {
                return Some(value);
            }
        }

        None
    }

    fn query_annotated(
        &self,
        env: &Environment,
        store: &Store,
        scope: ScopeId,
        r: &Pattern,
        label_stack: Vec<&String>,
    ) -> Option<QueryResult> {
        // If there are no edge annotations left, we check the current scope
        if label_stack.len() == 0 {
            let assoc_values = self.scope_values.get(&scope)?;
            for value in assoc_values {
                if let Some(bindings) = Interpreter::try_pattern(env, store, r, value.clone()) {
                    return Some((value.clone(), bindings));
                }
            }
        }

        // Check edge labels of neighbours
        for neighbour in self.edges.get(&scope)? {
            if let Some(edge_label) = self.edge_labels.get(&(scope, *neighbour)) {
                if let Some(expected_label) = label_stack.last() {
                    if *expected_label == edge_label {
                        let mut new_labels = label_stack.clone();
                        new_labels.pop();
                        if let Some(res) =
                            self.query_annotated(env, store, *neighbour, r, new_labels)
                        {
                            return Some(res);
                        }
                    }
                }
            } else {
                if let Some(value) =
                    self.query_annotated(env, store, *neighbour, r, label_stack.clone())
                {
                    return Some(value);
                }
            }
        }

        None
    }

    fn to_string(&self, store: &Store) -> String {
        let mut res = String::new();

        for edge in &self.edges {
            for neighbour in edge.1 {
                res += format!("{} -> {}\n", edge.0, neighbour).as_str();
            }
        }

        for value_edge in &self.scope_values {
            for value in value_edge.1 {
                res += format!(
                    "{} -> {}\n",
                    value_edge.0,
                    RefCell::borrow(value).deref().to_string(store)
                )
                .as_str();
            }
        }

        res
    }
}

#[derive(Debug, Default)]
pub struct Store {
    scope_graph: ScopeGraph,
}

impl Store {
    pub fn make_scope(&mut self) -> ScopeId {
        let r = self.scope_graph.next_scope;
        self.scope_graph.scopes.push(r);
        self.scope_graph.edges.insert(r, vec![]);
        self.scope_graph.scope_values.insert(r, vec![]);
        self.scope_graph.next_scope = self.scope_graph.next_scope + 1;
        r
    }

    pub fn make_edge(&mut self, from: ScopeId, to: ScopeId) {
        self.scope_graph.edges.entry(from).or_default().push(to);
    }

    pub fn make_labeled_edge(&mut self, from: ScopeId, label: String, to: ScopeId) {
        self.scope_graph.edges.entry(from).or_default().push(to);
        self.scope_graph.edge_labels.insert((from, to), label);
    }

    pub fn associate_value(&mut self, scope: ScopeId, v: ValueBox) {
        self.scope_graph
            .scope_values
            .entry(scope)
            .or_default()
            .push(v);
    }

    fn annotated_query_scope_graph(
        &self,
        env: &Environment,
        store: &Store,
        left_id: ScopeId,
        r: &Pattern,
        v: Vec<String>,
    ) -> Option<QueryResult> {
        self.scope_graph
            .query_annotated(env, store, left_id, r, v.iter().map(|s| s).collect())
    }

    fn query_scope_graph(
        &self,
        env: &Environment,
        store: &Store,
        left_id: ScopeId,
        r: &Pattern,
    ) -> Option<QueryResult> {
        self.scope_graph.query(env, store, left_id, r)
    }
}

#[derive(Debug, Default, Clone, PartialEq)]
pub struct StoreBox {
    pub idx: usize,
}

impl Display for StoreBox {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "box({})", self.idx)
    }
}

#[derive(Debug, Default)]
pub struct Environment<'a> {
    bindings: HashMap<String, ValueBox>,
    parent: Option<&'a Environment<'a>>,
}

impl<'a> Environment<'a> {
    pub fn new_with_parent(
        bindings: HashMap<String, ValueBox>,
        parent: &'a Environment<'a>,
    ) -> Self {
        Self {
            bindings,
            parent: Some(parent),
        }
    }

    pub fn put(&mut self, name: String, value: ValueBox) {
        self.bindings.insert(name, value);
    }

    pub fn get(&self, name: &String) -> Option<ValueBox> {
        match self.bindings.get(name) {
            Some(v) => Some(v.clone()),
            None => match self.parent {
                Some(p) => p.get(name),
                None => None,
            },
        }
    }

    fn to_string(&self, store: &Store) -> String {
        let mut res = String::new();

        for (name, value) in &self.bindings {
            res += format!(
                "{} -> {}\n",
                name,
                RefCell::borrow(value).deref().to_string(store)
            )
            .as_str();
        }

        res
    }
}

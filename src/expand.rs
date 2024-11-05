use crate::{
    ast::Literal,
    continuation::Continuation,
    error::RuntimeError,
    gc::Gc,
    syntax::{Identifier, Span, Syntax},
    value::Value,
};
use proc_macros::builtin;
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

#[derive(Clone, Debug)]
pub struct Transformer {
    pub rules: Vec<SyntaxRule>,
    pub is_variable_transformer: bool,
}

impl Transformer {
    pub fn expand(&self, expr: &Syntax) -> Option<Syntax> {
        for rule in &self.rules {
            if let expansion @ Some(_) = rule.expand(expr) {
                return expansion;
            }
        }
        None
    }
}

#[derive(Clone, Debug)]
pub struct SyntaxRule {
    pub pattern: Pattern,
    pub template: Template,
}

impl SyntaxRule {
    fn expand(&self, expr: &Syntax) -> Option<Syntax> {
        let mut var_binds = HashMap::new();
        let curr_span = expr.span().clone();
        self.pattern
            .matches(expr, &mut var_binds)
            .then(|| self.template.execute(&var_binds, curr_span))
            .flatten()
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Pattern {
    Nil,
    Underscore,
    Ellipsis(Box<Pattern>),
    List(Vec<Pattern>),
    Vector(Vec<Pattern>),
    Variable(String),
    Keyword(String),
    Literal(Literal),
}

#[derive(Debug, Clone)]
enum SyntaxOrMany {
    Syntax(Syntax),
    Many(Vec<Syntax>),
}

impl Pattern {
    pub fn compile(expr: &Syntax, keywords: &HashSet<String>) -> Self {
        match expr {
            Syntax::Nil { .. } => Self::Nil,
            Syntax::Identifier { ident, .. } if ident.name == "_" => Self::Underscore,
            Syntax::Identifier { ident, .. } if keywords.contains(&ident.name) => {
                Self::Keyword(ident.name.clone())
            }
            Syntax::Identifier { ident, .. } => Self::Variable(ident.name.clone()),
            Syntax::List { list, .. } => Self::List(Self::compile_slice(list, keywords)),
            Syntax::Vector { vector, .. } => Self::Vector(Self::compile_slice(vector, keywords)),
            Syntax::Literal { literal, .. } => Self::Literal(literal.clone()),
        }
    }

    fn compile_slice(mut expr: &[Syntax], keywords: &HashSet<String>) -> Vec<Self> {
        let mut output = Vec::new();
        loop {
            match expr {
                [] => break,
                [syntax, Syntax::Identifier {
                    ident: ellipsis, ..
                }, tail @ ..]
                    if ellipsis.name == "..." =>
                {
                    output.push(Self::Ellipsis(Box::new(Self::compile(syntax, keywords))));
                    expr = tail;
                }
                [head, tail @ ..] => {
                    output.push(Self::compile(head, keywords));
                    expr = tail;
                }
            }
        }
        output
    }

    fn matches(&self, expr: &Syntax, var_binds: &mut HashMap<Pattern, SyntaxOrMany>) -> bool {
        match self {
            Self::Underscore => !expr.is_nil(),
            Self::Variable(ref name) => {
                var_binds.insert(
                    Pattern::Variable(name.clone()),
                    SyntaxOrMany::Syntax(expr.clone()),
                );
                true
            }
            Self::Keyword(ref lhs) => {
                matches!(expr, Syntax::Identifier { ident: rhs, bound: false, .. } if lhs == &rhs.name)
            }
            Self::List(list) => match_slice(list, expr, var_binds),
            Self::Vector(vec) => match_slice(vec, expr, var_binds),
            // We shouldn't ever see this outside of lists
            Self::Nil => expr.is_nil(),
            _ => todo!(),
        }
    }
}

fn match_slice(
    pattern: &[Pattern],
    expr: &Syntax,
    var_binds: &mut HashMap<Pattern, SyntaxOrMany>,
) -> bool {
    let mut expr_iter = match expr {
        Syntax::List { list, .. } => list.iter().peekable(),
        _ => return false,
    };
    let mut pattern_iter = pattern.iter().peekable();
    while let Some(item) = pattern_iter.next() {
        if let Pattern::Ellipsis(ref pattern) = item {
            let exprs = if !matches!(pattern_iter.peek(), Some(Pattern::Nil)) {
                // Match backwards
                let mut rev_expr_iter = expr_iter.rev();
                let rev_pattern_iter = pattern_iter.rev();
                for pattern in rev_pattern_iter {
                    if let Some(expr) = rev_expr_iter.next() {
                        if !pattern.matches(expr, var_binds) {
                            return false;
                        }
                    }
                }
                rev_expr_iter.rev().cloned().collect()
            } else {
                expr_iter.cloned().collect()
            };
            // Gobble up the rest
            var_binds.insert(*pattern.clone(), SyntaxOrMany::Many(exprs));
            return true;
        } else if let Some(next_expr) = expr_iter.next() {
            if !item.matches(next_expr, var_binds) {
                return false;
            }
        } else {
            return false;
        }
    }

    expr_iter.peek().is_none()
}

#[derive(Clone, Debug)]
pub enum Template {
    Nil,
    Ellipsis(Box<Template>),
    List(Vec<Template>),
    Vector(Vec<Template>),
    Identifier(Identifier),
    Literal(Literal),
}

impl Template {
    pub fn compile(expr: &Syntax) -> Self {
        match expr {
            Syntax::Nil { .. } => Self::Nil,
            Syntax::List { list, .. } => Self::List(Self::compile_slice(list)),
            Syntax::Vector { vector, .. } => Self::Vector(Self::compile_slice(vector)),
            Syntax::Literal { literal, .. } => Self::Literal(literal.clone()),
            Syntax::Identifier { ident, .. } => Self::Identifier(ident.clone()),
        }
    }

    fn compile_slice(mut expr: &[Syntax]) -> Vec<Self> {
        let mut output = Vec::new();
        loop {
            match expr {
                [] => break,
                [syntax, Syntax::Identifier {
                    ident: ellipsis, ..
                }, tail @ ..]
                    if ellipsis.name == "..." =>
                {
                    output.push(Self::Ellipsis(Box::new(Template::compile(syntax))));
                    expr = tail;
                }
                [head, tail @ ..] => {
                    output.push(Self::compile(head));
                    expr = tail;
                }
            }
        }
        output
    }

    fn to_pattern(&self) -> Pattern {
        match self {
            Self::Nil => Pattern::Nil,
            Self::Ellipsis(ellipsis) => Pattern::Ellipsis(Box::new(ellipsis.to_pattern())),
            Self::List(list) => Pattern::List(list.iter().map(|x| x.to_pattern()).collect()),
            Self::Vector(vec) => Pattern::Vector(vec.iter().map(|x| x.to_pattern()).collect()),
            Self::Identifier(ident) => Pattern::Variable(ident.name.clone()),
            Self::Literal(lit) => Pattern::Literal(lit.clone()),
        }
    }

    fn execute(
        &self,
        var_binds: &HashMap<Pattern, SyntaxOrMany>,
        curr_span: Span,
    ) -> Option<Syntax> {
        let syntax = match self {
            Self::Nil => Syntax::new_nil(curr_span),
            Self::List(list) => {
                let output = execute_slice(list, var_binds, curr_span.clone())?;
                if output.len() == 1 {
                    Syntax::new_nil(curr_span)
                } else {
                    Syntax::new_list(output, curr_span)
                }
            }
            Self::Vector(vec) => {
                Syntax::new_vector(execute_slice(vec, var_binds, curr_span.clone())?, curr_span)
            }
            Self::Identifier(ident) => {
                match var_binds.get(&Pattern::Variable(ident.name.clone())) {
                    None => Syntax::Identifier {
                        ident: ident.clone(),
                        span: curr_span,
                        bound: false,
                    },
                    Some(SyntaxOrMany::Syntax(expr)) => expr.clone(),
                    Some(SyntaxOrMany::Many(exprs)) => Syntax::new_list(exprs.clone(), curr_span),
                }
            }
            Self::Literal(literal) => Syntax::new_literal(literal.clone(), curr_span),
            _ => unreachable!(),
        };
        Some(syntax)
    }
}

fn execute_slice(
    items: &[Template],
    var_binds: &HashMap<Pattern, SyntaxOrMany>,
    curr_span: Span,
) -> Option<Vec<Syntax>> {
    let mut output = Vec::new();
    for item in items {
        match item {
            Template::Ellipsis(template) => {
                let pattern = template.to_pattern();
                // TODO: This cloning sucks!
                let exprs = match var_binds.get(&pattern).unwrap() {
                    SyntaxOrMany::Syntax(expr) => Vec::from([expr.clone()]),
                    SyntaxOrMany::Many(exprs) => exprs.clone(),
                };
                for expr in exprs {
                    if expr.is_nil() {
                        output.push(expr)
                    } else {
                        let mut var_binds = var_binds.clone();
                        if !pattern.matches(&expr, &mut var_binds) {
                            return None;
                        }
                        let executed = template.execute(&var_binds, curr_span.clone())?;
                        output.push(executed);
                    }
                }
            }
            Template::Nil => {
                if let Some(Syntax::Nil { .. }) = output.last() {
                    continue;
                } else {
                    output.push(Syntax::new_nil(curr_span.clone()));
                }
            }
            _ => output.push(item.execute(var_binds, curr_span.clone())?),
        }
    }
    Some(output)
}

#[builtin("make-variable-transformer")]
pub async fn make_variable_transformer(
    _cont: &Option<Arc<Continuation>>,
    proc: &Gc<Value>,
) -> Result<Gc<Value>, RuntimeError> {
    let proc = proc.read().await;
    match &*proc {
        Value::Procedure(proc) => {
            let mut proc = proc.clone();
            proc.is_variable_transformer = true;
            Ok(Gc::new(Value::Procedure(proc)))
        }
        Value::Transformer(transformer) => {
            let mut transformer = transformer.clone();
            transformer.is_variable_transformer = true;
            Ok(Gc::new(Value::Transformer(transformer)))
        }
        _ => todo!(),
    }
}

use crate::{
    ast::{self, Literal},
    compile::{Compile, CompileError},
    continuation::{CatchContinuationCall, Continuation},
    env::Env,
    error::RuntimeError,
    eval::Eval,
    gc::Gc,
    lex::{InputSpan, Lexeme, Token},
    parse::ParseError,
    proc::Callable,
    value::Value,
};
use futures::future::BoxFuture;
use std::{collections::BTreeSet, fmt, sync::Arc};

#[derive(Debug, Clone, PartialEq)]
pub struct Span {
    pub line: u32,
    pub column: usize,
    pub offset: usize,
    pub file: Arc<String>,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.column)
    }
}

impl From<InputSpan<'_>> for Span {
    fn from(span: InputSpan<'_>) -> Self {
        Span {
            line: span.location_line(),
            column: span.get_column(),
            offset: span.location_offset(),
            file: span.extra.clone(),
        }
    }
}

// TODO: Wrap Vecs in ArcSlices to reduce cloning
#[derive(Clone, Debug)]
pub enum Syntax {
    /// An empty list.
    Nil {
        span: Span,
    },
    /// A nested grouping of pairs. If the expression is a proper list, then the
    /// last element of expression will be Nil. This vector is guaranteed to contain
    /// at least two elements.
    List {
        list: Vec<Syntax>,
        span: Span,
    },
    Vector {
        vector: Vec<Syntax>,
        span: Span,
    },
    Literal {
        literal: Literal,
        span: Span,
    },
    Identifier {
        ident: Identifier,
        bound: bool,
        span: Span,
    },
}

impl Syntax {
    pub fn mark(&mut self, mark: Mark) {
        match self {
            Self::List { ref mut list, .. } => {
                for item in list {
                    item.mark(mark);
                }
            }
            Self::Vector { ref mut vector, .. } => {
                for item in vector {
                    item.mark(mark);
                }
            }
            Self::Identifier { ident, .. } => ident.mark(mark),
            _ => (),
        }
    }

    pub fn strip_unused_marks<'a>(&'a mut self, env: &'a Env) -> BoxFuture<'a, ()> {
        Box::pin(async move {
            match self {
                Self::List { ref mut list, .. } => {
                    for item in list {
                        item.strip_unused_marks(env).await;
                    }
                }
                Self::Vector { ref mut vector, .. } => {
                    for item in vector {
                        item.strip_unused_marks(env).await;
                    }
                }
                Self::Identifier { ref mut ident, .. } => env.strip_unused_marks(ident).await,
                _ => (),
            }
        })
    }

    pub fn resolve_bindings<'a>(&'a mut self, env: &'a Env) -> BoxFuture<'a, ()> {
        Box::pin(async move {
            match self {
                Self::List { ref mut list, .. } => {
                    for item in list {
                        item.resolve_bindings(env).await;
                    }
                }
                Self::Vector { ref mut vector, .. } => {
                    for item in vector {
                        item.resolve_bindings(env).await;
                    }
                }
                Self::Identifier {
                    ref ident,
                    ref mut bound,
                    ..
                } => *bound = env.is_bound(ident).await,
                _ => (),
            }
        })
    }

    async fn apply_transformer(
        &self,
        curr_env: &Env,
        macro_env: Env,
        cont: &Option<Arc<Continuation>>,
        transformer: Gc<Value>,
    ) -> Result<Expansion<'static>, RuntimeError> {
        // Create a new mark for the expansion context
        let new_mark = Mark::new();
        // Apply the new mark to the input
        // TODO: Figure out a better way to do this without cloning so much
        let mut input = self.clone();
        input.resolve_bindings(curr_env).await;
        input.mark(new_mark);
        // Call the transformer with the input:
        let mut output = match &*transformer.read().await {
            Value::Procedure(proc) => {
                let output = proc
                    .call(vec![Gc::new(Value::Syntax(input))], cont)
                    .await?
                    .eval(cont)
                    .await?;
                let output = output.read().await;
                match &*output {
                    Value::Syntax(syntax) => syntax.clone(),
                    _ => todo!(),
                }
            }
            Value::Transformer(transformer) => transformer.expand(&input).unwrap(),
            x => return Err(RuntimeError::invalid_type("procedure", x.type_name())),
        };
        // Apply the new mark to the output
        output.mark(new_mark);
        Ok(Expansion::Expanded {
            mark: new_mark,
            syntax: output,
            macro_env,
        })
    }

    fn expand<'a>(
        &'a self,
        env: &'a Env,
        cont: &'a Option<Arc<Continuation>>,
    ) -> BoxFuture<'a, Result<Expansion<'a>, RuntimeError>> {
        Box::pin(async move {
            match self {
                Self::List { list, .. } => {
                    // We have to check for the very special set! variable transformer form here
                    match &list[..] {
                        [Self::Identifier { ident, .. }, tail @ ..] if ident == "set!" => {
                            // Check for a variable transformer
                            if let Some(Syntax::Identifier { ident, .. }) = tail.get(0) {
                                if let Some((macro_env, transformer)) = env.fetch_macro(ident).await
                                {
                                    if !transformer.read().await.is_variable_transformer() {
                                        return Err(RuntimeError::not_variable_transformer());
                                    }
                                    return self
                                        .apply_transformer(env, macro_env, cont, transformer)
                                        .await;
                                }
                            }
                        }
                        _ => (),
                    }

                    // If the head is not an identifier, we leave the expression unexpanded
                    // for now. We will expand it later
                    let ident = match list.get(0) {
                        Some(Self::Identifier { ident, .. }) => ident,
                        _ => return Ok(Expansion::Unexpanded(self)),
                    };

                    if let Some((macro_env, transformer)) = env.fetch_macro(ident).await {
                        return self
                            .apply_transformer(env, macro_env, cont, transformer)
                            .await;
                    }
                }
                Self::Identifier { ident, .. } => {
                    if let Some((macro_env, transformer)) = env.fetch_macro(ident).await {
                        return self
                            .apply_transformer(env, macro_env, cont, transformer)
                            .await;
                    }
                }
                _ => (),
            }
            Ok(Expansion::Unexpanded(self))
        })
    }

    pub fn compile<'a>(
        &'a self,
        env: &'a Env,
        cont: &'a Option<Arc<Continuation>>,
    ) -> BoxFuture<'a, Result<CompileResult, CompileError>> {
        Box::pin(async move {
            match self.expand(env, cont).await? {
                Expansion::Expanded {
                    mark,
                    macro_env,
                    syntax,
                } => {
                    let new_env =
                        Env::Expansion(Gc::new(env.new_expansion_context(mark, macro_env.clone())));
                    let mut result = syntax.compile(&new_env, cont).await?;
                    result.push_macro_expansion(mark, macro_env);
                    Ok(result)
                }
                Expansion::Unexpanded(syntax) => {
                    if let Syntax::List { list, span } = syntax {
                        match &list[..] {
                            [Self::Identifier { ident, .. }, tail @ ..] if ident == "begin" => {
                                return Ok(CompileResult::body(
                                    self.span().clone(),
                                    tail[..tail.len() - 1].to_owned(),
                                ));
                            }
                            [head @ Syntax::List { .. }, tail @ ..] => {
                                // Attempt to expand the first argument
                                if let Expansion::Expanded {
                                    mark,
                                    macro_env,
                                    syntax,
                                } = head.expand(env, cont).await?
                                {
                                    let new_env = Env::Expansion(Gc::new(
                                        env.new_expansion_context(mark, macro_env.clone()),
                                    ));
                                    let syntax: Vec<_> =
                                        [syntax].into_iter().chain(tail.iter().cloned()).collect();
                                    let syntax = Syntax::new_list(syntax, span.clone());
                                    let mut result = syntax.compile(&new_env, cont).await?;
                                    result.push_macro_expansion(mark, macro_env);
                                    return Ok(result);
                                }
                            }
                            _ => (),
                        }
                    }
                    match syntax {
                        Syntax::List { list, .. } => match &list[..] {
                            [Self::Identifier { ident, .. }, tail @ ..] if ident == "define" => {
                                env.def_var(ident, Gc::new(Value::Nil)).await;
                                return Ok(CompileResult::definition(
                                    self.span().clone(),
                                    tail.to_owned(),
                                ));
                            }
                            [Self::Identifier { ident, span, .. }, tail @ ..]
                                if ident == "define-syntax" =>
                            {
                                ast::DefineSyntax::compile_to_expr(tail, env, cont, span)
                                    .await?
                                    .eval(env, cont)
                                    .await?;
                                return Ok(CompileResult::define_syntax(self.span().clone()));
                            }
                            _ => (),
                        },
                        _ => (),
                    }
                    Ok(CompileResult::expression(
                        self.span().clone(),
                        syntax.compile_expr(env, cont).await?,
                    ))
                }
            }
        })
    }

    pub async fn compile_expr(
        &self,
        env: &Env,
        cont: &Option<Arc<Continuation>>,
    ) -> Result<Arc<dyn Eval>, CompileError> {
        match self {
            Self::Nil { span } => Err(CompileError::UnexpectedEmptyList(span.clone())),
            Self::Identifier { ident, .. } => Ok(Arc::new(ident.clone()) as Arc<dyn Eval>),
            Self::Literal { literal, .. } => Ok(Arc::new(literal.clone()) as Arc<dyn Eval>),
            Self::List { list: exprs, span } => match &exprs[..] {
                // Function call:
                [Self::Identifier { ident, .. }, ..] if env.is_bound(ident).await => {
                    ast::Call::compile_to_expr(exprs, env, cont, span).await
                }
                // Special forms:
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "quote" => {
                    ast::Quote::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "syntax" => {
                    ast::SyntaxQuote::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "begin" => {
                    ast::Body::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "let" => {
                    ast::Let::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "lambda" => {
                    ast::Lambda::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "if" => {
                    ast::If::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "and" => {
                    ast::And::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "or" => {
                    ast::Or::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "syntax-case" => {
                    ast::SyntaxCase::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "syntax-rules" => {
                    ast::SyntaxRules::compile_to_expr(tail, env, cont, span).await
                }
                [Self::Identifier { ident, span, .. }, tail @ ..] if ident == "set!" => {
                    ast::Set::compile_to_expr(tail, env, cont, span).await
                }
                // Definition in expression context is an error:
                [Self::Identifier { ident, span, .. }, ..]
                    if ident == "define" || ident == "define-syntax" =>
                {
                    Err(CompileError::DefinitionInExpressionPosition(span.clone()))
                }
                // Special function call:
                _ => ast::Call::compile_to_expr(exprs, env, cont, span).await,
            },
            Self::Vector { vector, .. } => {
                let vals = vector.iter().map(Value::from_syntax).collect();
                Ok(Arc::new(ast::Vector { vals }) as Arc<dyn Eval>)
            }
        }
    }

    pub async fn compile_repl(
        &self,
        env: &Env,
        cont: &Option<Arc<Continuation>>,
    ) -> Result<Arc<dyn Eval>, CompileError> {
        ast::Body::compile_to_expr(
            &[
                self.clone(),
                Syntax::Nil {
                    span: self.span().clone(),
                },
            ],
            env,
            cont,
            self.span(),
        )
        .await
    }
}

pub struct CompileResult {
    pub span: Span,
    pub expansions: Vec<(Mark, Env)>,
    pub kind: CompileResultKind,
}

pub enum CompileResultKind {
    Body(Vec<Syntax>),
    Definition(Vec<Syntax>),
    DefineSyntax,
    Expression(Arc<dyn Eval>),
}

pub fn wrap_expansions(expansions: &[(Mark, Env)], mut expr: Arc<dyn Eval>) -> Arc<dyn Eval> {
    for (mark, env) in expansions {
        expr = Arc::new(ast::MacroExpansionContext {
            mark: *mark,
            macro_env: env.clone(),
            expr,
        });
    }
    expr
}

impl CompileResult {
    fn body(span: Span, body: Vec<Syntax>) -> Self {
        Self {
            span,
            expansions: Vec::new(),
            kind: CompileResultKind::Body(body),
        }
    }

    fn definition(span: Span, body: Vec<Syntax>) -> Self {
        Self {
            span,
            expansions: Vec::new(),
            kind: CompileResultKind::Definition(body),
        }
    }

    fn define_syntax(span: Span) -> Self {
        Self {
            span,
            expansions: Vec::new(),
            kind: CompileResultKind::DefineSyntax,
        }
    }

    fn expression(span: Span, expr: Arc<dyn Eval>) -> Self {
        Self {
            span,
            expansions: Vec::new(),
            kind: CompileResultKind::Expression(expr),
        }
    }

    fn push_macro_expansion(&mut self, mark: Mark, macro_env: Env) {
        self.expansions.push((mark, macro_env));
    }

    pub fn push_macro_expansions(&mut self, iter: impl IntoIterator<Item = (Mark, Env)>) {
        self.expansions.extend(iter);
    }

    pub fn expr<'a>(
        self,
        env: &'a Env,
        cont: &'a Option<Arc<Continuation>>,
    ) -> BoxFuture<'a, Result<Arc<dyn Eval>, CompileError>> {
        Box::pin(async move {
            match self.kind {
                CompileResultKind::Body(body) => {
                    let mut res = Vec::new();
                    for item in body {
                        res.push(item.compile(env, cont).await?.expr(env, cont).await?);
                    }
                    Ok(wrap_expansions(
                        &self.expansions,
                        Arc::new(ast::Body::new(res)),
                    ))
                }
                CompileResultKind::Expression(expr) => Ok(wrap_expansions(&self.expansions, expr)),
                _ => Err(CompileError::DefinitionInExpressionPosition(self.span)),
            }
        })
    }
}

pub enum Expansion<'a> {
    /// Syntax remained unchanged after expansion
    Unexpanded(&'a Syntax),
    /// Syntax was expanded, producing a new expansion context
    Expanded {
        mark: Mark,
        macro_env: Env,
        syntax: Syntax,
    },
}

impl Expansion<'_> {
    pub fn is_expanded(&self) -> bool {
        matches!(self, Self::Expanded { .. })
    }

    pub fn is_unexpanded(&self) -> bool {
        matches!(self, Self::Unexpanded(_))
    }
}

/*
impl<'a> Expansion<'a> {
    pub fn compile(
        self,
        env: &'a Env,
        cont: &'a Option<Arc<Continuation>>,
    ) -> BoxFuture<'a, Result<Arc<dyn Eval>, CompileError>> {
        Box::pin(async move {
            match self {
                Self::Unexpanded(syntax) => syntax.compile_expanded(env, cont).await,
                Self::Expanded {
                    mark,
                    syntax,
                    macro_env,
                } => {
                    // If the expression has been expanded, we may need to expand it again, but
                    // it must be done in a new expansion context.
                    let env = Env::Expansion(Gc::new(env.new_expansion_context(mark, macro_env)));
                    syntax.expand(&env, cont).await?.compile(&env, cont).await
                }
            }
        })
    }
}
*/

impl std::ops::Deref for Expansion<'_> {
    type Target = Syntax;

    fn deref(&self) -> &Syntax {
        match self {
            Self::Unexpanded(syntax) => syntax,
            Self::Expanded { syntax, .. } => syntax,
        }
    }
}

#[derive(Debug)]
pub struct ParsedSyntax {
    pub doc_comment: Option<String>,
    syntax: Syntax,
}

impl ParsedSyntax {
    fn parse_fragment<'a>(i: &'a [Token<'a>]) -> Result<(&'a [Token<'a>], Self), ParseError<'a>> {
        let (doc_comment, remaining) = if let Token {
            lexeme: Lexeme::DocComment(ref doc_comment),
            ..
        } = i[0]
        {
            (Some(doc_comment.clone()), &i[1..])
        } else {
            (None, i)
        };
        let (remaining, syntax) = crate::parse::expression(remaining)?;
        Ok((
            remaining,
            Self {
                doc_comment,
                syntax,
            },
        ))
    }

    pub fn parse<'a>(mut i: &'a [Token<'a>]) -> Result<Vec<Self>, ParseError<'a>> {
        let mut output = Vec::new();
        while !i.is_empty() {
            let (remaining, expr) = Self::parse_fragment(i)?;
            output.push(expr);
            i = remaining
        }
        Ok(output)
    }

    pub async fn compile(
        &self,
        env: &Env,
        cont: &Option<Arc<Continuation>>,
    ) -> Result<Arc<dyn Eval>, CompileError> {
        Ok(Arc::new(CatchContinuationCall::new(
            self.syntax.compile_repl(env, cont).await?,
        )))
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Mark(u64);

impl Mark {
    pub fn new() -> Self {
        Self(rand::random())
    }
}

impl Default for Mark {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Identifier {
    pub name: String,
    pub marks: BTreeSet<Mark>,
}

impl Identifier {
    pub fn new(name: String) -> Self {
        Self {
            name,
            marks: BTreeSet::default(),
        }
    }

    pub fn mark(&mut self, mark: Mark) {
        if self.marks.contains(&mark) {
            self.marks.remove(&mark);
        } else {
            self.marks.insert(mark);
        }
    }
}

impl PartialEq<str> for Identifier {
    fn eq(&self, rhs: &str) -> bool {
        self.name == rhs
    }
}

impl Syntax {
    pub fn span(&self) -> &Span {
        match self {
            Self::Nil { span } => span,
            Self::List { span, .. } => span,
            Self::Vector { span, .. } => span,
            Self::Literal { span, .. } => span,
            Self::Identifier { span, .. } => span,
        }
    }

    // There's got to be a better way:

    pub fn new_nil(span: impl Into<Span>) -> Self {
        Self::Nil { span: span.into() }
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, Self::Nil { .. })
    }

    pub fn new_list(list: Vec<Syntax>, span: impl Into<Span>) -> Self {
        Self::List {
            list,
            span: span.into(),
        }
    }

    pub fn is_list(&self) -> bool {
        matches!(self, Self::List { .. })
    }

    pub fn new_vector(vector: Vec<Syntax>, span: impl Into<Span>) -> Self {
        Self::Vector {
            vector,
            span: span.into(),
        }
    }

    pub fn is_vector(&self) -> bool {
        matches!(self, Self::Vector { .. })
    }

    pub fn new_literal(literal: Literal, span: impl Into<Span>) -> Self {
        Self::Literal {
            literal,
            span: span.into(),
        }
    }

    pub fn is_literal(&self) -> bool {
        matches!(self, Self::Literal { .. })
    }

    pub fn new_identifier(name: &str, span: impl Into<Span>) -> Self {
        Self::Identifier {
            ident: Identifier::new(name.to_string()),
            span: span.into(),
            bound: false,
        }
    }

    pub fn is_identifier(&self) -> bool {
        matches!(self, Self::Identifier { .. })
    }
}

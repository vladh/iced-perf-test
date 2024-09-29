// © 2022 Vlad-Stefan Harbuz <vlad@vladh.net>
// SPDX-License-Identifier: AGPL-3.0-only
// “Cellsum” is a registered trademark and no rights to it are ceded.

//! Parses and evaluates Cellsum formulas.

#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::VecDeque;
use std::fmt;
use std::str::FromStr;

use rust_decimal::Decimal;
#[allow(unused_imports)]
use tracing::{debug, error, info, instrument, warn};
#[allow(unused_imports)]
use tracing_subscriber::field::MakeExt;

use crate::sheet::{CellAbsPos, CellAbsRange};
use crate::storage;

mod fixup {}

mod format {}

mod lex {
    //! Lexes Cellsum formulas.

    use std::iter::Peekable;
    use std::str::{Chars, FromStr};

    use super::*;

    #[derive(Debug, PartialEq, Clone, Copy)]
    /// A lexing error.
    pub enum Error {
        UnimplementedToken,
        UnclosedStringLiteral,
        CouldNotParseNumber,
    }

    #[derive(Debug, Clone, PartialEq)]
    /// The possible tokens produced by lexing.
    pub(super) enum Token {
        /// An opening paren `(`.
        Lparen,
        /// A closing paren `)`.
        Rparen,
        /// A comma `,`.
        Comma,
        /// The division sign `/`.
        Div,
        /// The minus sign `-`.
        Minus,
        /// The plus sign `+`.
        Plus,
        /// The times sign `*`.
        Times,
        /// The range sign used for ranges of cellrefs, `:`. It is used in, for example, `A1:B3`.
        Range,
        /// A text literal such as `"hello"`.
        TextLiteral(String),
        /// A number literal such as `12.345` or `17`.
        NumberLiteral(Decimal),
        /// A name, such as `test`. A name is used, for example, as the name of a function, as in
        /// `myfn()`.
        Name(String),
        /// A cellref, i.e. a name referring to a cell, such as `A1` or `XYZ123`.
        Cellref(String),
    }

    #[derive(Debug)]
    /// The state of a lexer.
    pub(super) struct Lexer<'a> {
        chars: Peekable<Chars<'a>>,
        unlexed: Option<Token>,
    }

    impl<'a> Lexer<'a> {
        /// Creates a new lexer.
        pub(super) fn new(s: &'a str) -> Self {
            Self {
                chars: s.chars().peekable(),
                unlexed: None,
            }
        }

        /// Peeks at the next token and returns it without consuming it.
        pub(super) fn peek(&mut self) -> Result<Option<Token>, Error> {
            match self.lex()? {
                Some(token) => {
                    self.unlex(&token);
                    Ok(Some(token))
                }
                None => Ok(None),
            }
        }

        /// Consumes the next token and returns it.
        pub(super) fn lex(&mut self) -> Result<Option<Token>, Error> {
            if self.unlexed.is_some() {
                let token = self.unlexed.clone();
                self.unlexed = None;
                return Ok(token);
            }

            let Some(c) = self.peek_char() else {
                return Ok(None);
            };

            if c.is_alphabetic() || c == '_' {
                return self.lex_name();
            }

            if c.is_numeric() {
                return self.lex_numeric_literal();
            }

            let c = self
                .next_char()
                .expect("could not get next_char() despite having just peek_char()'d it");

            match c {
                '"' => self.lex_string_literal(),
                '(' => Ok(Some(Token::Lparen)),
                ')' => Ok(Some(Token::Rparen)),
                ',' => Ok(Some(Token::Comma)),
                '/' => Ok(Some(Token::Div)),
                '-' => Ok(Some(Token::Minus)),
                '+' => Ok(Some(Token::Plus)),
                '*' => Ok(Some(Token::Times)),
                ':' => Ok(Some(Token::Range)),
                _ => Err(Error::UnimplementedToken),
            }
        }

        /// Un-consumes `token`, so that `token` will be returned on the next call to [`lex`]. Note
        /// that unlexing is supported only once, so one must [`lex`] before calling this function
        /// again.
        pub(super) fn unlex(&mut self, token: &Token) {
            assert!(
                self.unlexed.is_none(),
                "tried to unlex more than once, which is not supported"
            );
            self.unlexed = Some(token.clone());
        }

        fn lex_name(&mut self) -> Result<Option<Token>, Error> {
            let mut does_match_cellref = true;
            let mut have_seen_numbers = false;
            let mut strval = String::new();

            loop {
                let Some(c) = self.peek_char() else {
                    break;
                };

                if !c.is_alphabetic() && c != '_' && !c.is_numeric() {
                    break;
                }

                let c = self
                    .next_char()
                    .expect("could not get next_char() despite having just peek_char()'d it");
                strval.push(c);

                // This segment is just to check whether this particular literal looks like a cell
                // ref (e.g. "AB123").
                if have_seen_numbers {
                    if !c.is_numeric() {
                        does_match_cellref = false;
                    }
                } else if c.is_numeric() {
                    have_seen_numbers = true;
                } else if !c.is_uppercase() {
                    does_match_cellref = false;
                }
            }

            if strval.is_empty() {
                return Ok(None);
            }

            if does_match_cellref && !have_seen_numbers {
                does_match_cellref = false;
            }

            if does_match_cellref {
                Ok(Some(Token::Cellref(strval)))
            } else {
                Ok(Some(Token::Name(strval)))
            }
        }

        fn lex_numeric_literal(&mut self) -> Result<Option<Token>, Error> {
            let mut strval = String::new();

            loop {
                let Some(c) = self.peek_char() else {
                    break;
                };

                if !c.is_numeric() && c != '.' {
                    break;
                }

                let c = self
                    .next_char()
                    .expect("could not get next_char() despite having just peek_char()'d it");
                strval.push(c);
            }

            let num = Decimal::from_str(&strval).map_err(|_| Error::CouldNotParseNumber)?;

            Ok(Some(Token::NumberLiteral(num)))
        }

        fn lex_string_literal(&mut self) -> Result<Option<Token>, Error> {
            let mut strval = String::new();
            let mut saw_closing_quote = false;

            loop {
                let Some(c) = self.next_char() else {
                    break;
                };

                if c == '"' {
                    saw_closing_quote = true;
                    break;
                }

                strval.push(c);
            }

            if !saw_closing_quote {
                return Err(Error::UnclosedStringLiteral);
            }

            Ok(Some(Token::TextLiteral(strval)))
        }

        fn next_char(&mut self) -> Option<char> {
            loop {
                let c = self.peek_char()?;
                if c.is_whitespace() {
                    self.chars.next();
                } else {
                    return self.chars.next();
                }
            }
        }

        fn peek_char(&mut self) -> Option<char> {
            loop {
                let c = *self.chars.peek()?;
                if c.is_whitespace() {
                    self.chars.next();
                    continue;
                } else {
                    return Some(c);
                }
            }
        }
    }
}

mod parse {
    /*!
    Parses Cellsum formulas.

    The BNF grammar for the formula language:

    ```
    digit:
        "0" - "9"

    lower:
        "a" - "z"

    upper:
        "A" - "Z"

    alpha:
        lower
        upper

    alunder:
        alpha
        "_"

    alnumunder:
        digit
        alpha
        "_"

    name:
        alunder (alnumunder)*

    cellref:
        upper (upper)* digit (digit)*

    integer_literal:
        digit (digit)*

    literal:
        integer_literal

    plain_expr:
        literal
        name
        cellref

    nested_expr:
        plain_expr
        "(" expr ")"

    argument_list:
        expr ("," argument_list)*

    call_expr:
        name "(" argument_list ")"

    postfix_expr:
        nested_expr
        call_expr

    cell_expr:
        postfix_expr
        cell_expr ":" postfix_expr

    mult_expr:
        cell_expr
        mult_expr "*" cell_expr
        mult_expr "/" cell_expr

    add_expr:
        mult_expr
        add_expr "+" mult_expr
        add_expr "-" mult_expr

    expr:
        add_expr
    ```
    */

    use super::*;

    #[derive(Debug, PartialEq, Clone, Copy)]
    /// A parsing error.
    pub enum Error {
        LexError(lex::Error),
        ExpectedPlainExpr,
        PlainExprExpectedLiteralNameCellref,
        ExpectedNestedExpr,
        NestedExprExpectedLparen,
        CallExprExpectedLvalue,
        CallExprExpectedLparen,
        CallExprExpectedArgsOrRparen,
        CallExprConstructionFailed,
        CallExprExpectedCommaOrRparen,
        CallExprExpectedComma,
        ExpectedPostfixExpr,
        ExpectedBinarithmExpr,
        BinarithmExprLvalueConstructionFailed,
        BinarithmExprConstructionFailed,
    }

    impl From<lex::Error> for Error {
        fn from(e: lex::Error) -> Self {
            Error::LexError(e)
        }
    }

    #[derive(Debug, PartialEq, Clone, Copy)]
    /// A binary arithmetic operator.
    pub enum BinarithmOp {
        /// The division sign `/`.
        Div,
        /// The minus sign `-`.
        Minus,
        /// The plus sign `+`.
        Plus,
        /// The times sign `*`.
        Times,
        /// The range sign used for ranges of cellrefs, `:`. It is used in, for example, `A1:B3`.
        Range,
    }

    impl BinarithmOp {
        /// Attempts to convert a [`lex::Token`] into a binary arithmetic operator, returning
        /// `None` on failure.
        fn from_token(token: &lex::Token) -> Option<Self> {
            match token {
                lex::Token::Minus => Some(BinarithmOp::Minus),
                lex::Token::Plus => Some(BinarithmOp::Plus),
                lex::Token::Times => Some(BinarithmOp::Times),
                lex::Token::Div => Some(BinarithmOp::Div),
                lex::Token::Range => Some(BinarithmOp::Range),
                _ => None,
            }
        }

        /// Returns the precedence of a binary arithmetic operator. Higher precedence is
        /// prioritised when parsing.
        fn precedence(self) -> i32 {
            match self {
                BinarithmOp::Minus | BinarithmOp::Plus => 1,
                BinarithmOp::Times | BinarithmOp::Div => 2,
                BinarithmOp::Range => 3,
            }
        }
    }

    #[derive(Debug, PartialEq)]
    /// An expression of many possible kinds. These expressions make up the parsed tree.
    pub(super) enum Expr {
        /// A binary arithmetic expression, such as `A1 + test` or `A1:C3`.
        Binarithm {
            op: BinarithmOp,
            term1: Box<Expr>,
            term2: Box<Expr>,
        },
        /// A text literal such as `"hello"`.
        TextLiteral(String),
        /// A number literal such as `12.345` or `17`.
        NumberLiteral(Decimal),
        /// A bare name not used in a function call, such as `test`.
        Name(String),
        /// A cellref, i.e. a name referring to a cell, such as `A1` or `XYZ123`.
        Cellref(String),
        /// A function call, such as `TEST(A1, 5, 2.0)`.
        Call { name: String, args: Vec<Expr> },
    }

    fn parse_plain_expr(lexer: &mut lex::Lexer<'_>) -> Result<Box<Expr>, Error> {
        match lexer.lex()?.ok_or(Error::ExpectedPlainExpr)? {
            lex::Token::TextLiteral(strval) => Ok(Box::new(Expr::TextLiteral(strval))),
            lex::Token::NumberLiteral(num) => Ok(Box::new(Expr::NumberLiteral(num))),
            lex::Token::Name(strval) => Ok(Box::new(Expr::Name(strval))),
            lex::Token::Cellref(strval) => Ok(Box::new(Expr::Cellref(strval))),
            _ => Err(Error::PlainExprExpectedLiteralNameCellref),
        }
    }

    fn parse_nested_expr(lexer: &mut lex::Lexer<'_>) -> Result<Box<Expr>, Error> {
        let token = lexer.lex()?.ok_or(Error::ExpectedNestedExpr)?;
        if token == lex::Token::Lparen {
            let e = parse_expr(lexer)?;
            match lexer.lex()?.ok_or(Error::NestedExprExpectedLparen)? {
                lex::Token::Rparen => Ok(e),
                _ => Err(Error::NestedExprExpectedLparen),
            }
        } else {
            lexer.unlex(&token);
            parse_plain_expr(lexer)
        }
    }

    fn parse_call_expr(lexer: &mut lex::Lexer<'_>, lvalue: Expr) -> Result<Box<Expr>, Error> {
        let mut e = if let Expr::Name(name) = lvalue {
            Box::new(Expr::Call {
                name,
                args: Vec::default(),
            })
        } else {
            return Err(Error::CallExprExpectedLvalue);
        };

        if lexer.lex()?.ok_or(Error::CallExprExpectedLparen)? != lex::Token::Lparen {
            return Err(Error::CallExprExpectedLparen);
        }

        if lexer.peek()?.ok_or(Error::CallExprExpectedArgsOrRparen)? != lex::Token::Rparen {
            loop {
                if let Expr::Call {
                    name: _,
                    ref mut args,
                } = *e
                {
                    args.push(*parse_expr(lexer)?);
                } else {
                    return Err(Error::CallExprConstructionFailed);
                }
                if lexer.peek()?.ok_or(Error::CallExprExpectedCommaOrRparen)? == lex::Token::Rparen
                {
                    lexer.lex()?.ok_or(Error::CallExprExpectedCommaOrRparen)?;
                    break;
                }
                if lexer.lex()?.ok_or(Error::CallExprExpectedComma)? != lex::Token::Comma {
                    return Err(Error::CallExprExpectedComma);
                }
            }
        }

        Ok(e)
    }

    fn parse_postfix_expr(lexer: &mut lex::Lexer<'_>) -> Result<Box<Expr>, Error> {
        let e = parse_nested_expr(lexer)?;

        if matches!(*e, Expr::Name { .. }) {
            let token = lexer.peek()?;
            if token == Some(lex::Token::Lparen) {
                return parse_call_expr(lexer, *e);
            }
        }

        Ok(e)
    }

    fn parse_binarithm_expr(
        lexer: &mut lex::Lexer<'_>,
        mut lvalue: Option<Box<Expr>>,
        precedence_0: i32,
    ) -> Result<Box<Expr>, Error> {
        if lvalue.is_none() {
            lvalue = Some(parse_postfix_expr(lexer)?);
        }
        let mut token = lexer.lex()?;

        if token.is_some() {
            loop {
                let Some(ref some_token) = token else {
                    break;
                };
                let Some(op_1) = BinarithmOp::from_token(some_token) else {
                    break;
                };
                let precedence_1 = op_1.precedence();
                if precedence_1 < precedence_0 {
                    break;
                }

                let mut rvalue = parse_postfix_expr(lexer)?;

                token = lexer.lex()?;
                loop {
                    let Some(ref some_token) = token else {
                        break;
                    };
                    let Some(op_2) = BinarithmOp::from_token(some_token) else {
                        break;
                    };
                    let precedence_2 = op_2.precedence();
                    if precedence_2 <= precedence_1 {
                        break;
                    }

                    lexer.unlex(some_token);
                    rvalue = parse_binarithm_expr(lexer, Some(rvalue), precedence_2)?;
                    token = lexer.lex()?;
                }

                lvalue = Some(Box::new(Expr::Binarithm {
                    op: op_1,
                    term1: lvalue.ok_or(Error::BinarithmExprLvalueConstructionFailed)?,
                    term2: rvalue,
                }));
            }
        }

        if let Some(ref some_token) = token {
            lexer.unlex(some_token);
        }

        lvalue.ok_or(Error::BinarithmExprConstructionFailed)
    }

    /// Parses an [`Expr`] by getting tokens from a [`lex::Lexer`].
    pub(super) fn parse_expr(lexer: &mut lex::Lexer<'_>) -> Result<Box<Expr>, Error> {
        parse_binarithm_expr(lexer, None, 0)
    }
}

pub mod eval {
    //! Evaluates Cellsum formulas to produce a resulting value.

    use super::*;

    #[derive(Debug, PartialEq, Clone)]
    /// An evaluation error.
    pub enum Error {
        ParseError(parse::Error),
        UnexpectedName,
        UnexpectedCellrange,
        OperationUnimplemented {
            op: parse::BinarithmOp,
            term1: Box<Value>,
            term2: Box<Value>,
        },
        FailedToParseCellref {
            cellref: String,
        },
        FailedToGetCellByCellref {
            cellref: String,
        },
        FoundCircularReference {
            abs_pos: CellAbsPos,
        },
        FunctionNotFound {
            name: String,
        },
        FunctionArgError {
            function_name: String,
        },
        DependencyErrored,
    }

    #[derive(Debug, PartialEq, Clone)]
    /// The value of an expression.
    pub enum Value {
        /// A numeric value.
        Number(Decimal),
        /// A string value.
        Text(String),
        /// A cellref, i.e. a name referring to a cell, such as `A1` or `XYZ123`.
        Cellref(String),
        /// A range of cellrefs for example, `A1:B3`.
        Cellrange(String, String),
        /// An evaluation error.
        Error(Error),
    }

    impl fmt::Display for Value {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Value::Number(num) => write!(f, "{num}"),
                Value::Text(strval) => write!(f, "{strval}"),
                Value::Cellref(strval) => write!(f, "{strval}"),
                Value::Cellrange(start, end) => write!(f, "{start}:{end}"),
                Value::Error(error) => write!(f, "{error:?}"),
            }
        }
    }

    #[derive(Debug)]
    /// The context an expression is evaluated against, i.e. which sheet we are using to look up
    /// cell values when evaluating.
    pub struct Context<'a> {
        sheet: &'a storage::Sheet,
    }

    impl<'a> Context<'a> {
        /// Creates a [`Context`] from a [`storage::Sheet`].
        pub fn new(sheet: &'a storage::Sheet) -> Self {
            Self { sheet }
        }
    }

    #[derive(Debug)]
    /// The state used when evaluating an expression.
    pub struct Evaluator<'a> {
        ctx: &'a Context<'a>,
    }

    impl<'a> Evaluator<'a> {
        /// Creates a new [`Evaluator`].
        pub fn new(ctx: &'a Context<'_>) -> Self {
            Self { ctx }
        }

        /// Handles a binary operation using the `/` operator.
        fn op_div(&mut self, val1: Value, val2: Value) -> Result<Value, Error> {
            match (val1.clone(), val2.clone()) {
                (Value::Number(num1), Value::Number(num2)) => Ok(Value::Number(num1 / num2)),
                _ => Err(Error::OperationUnimplemented {
                    op: parse::BinarithmOp::Div,
                    term1: Box::new(val1),
                    term2: Box::new(val2),
                }),
            }
        }

        /// Handles a binary operation using the `-` operator.
        fn op_minus(&mut self, val1: Value, val2: Value) -> Result<Value, Error> {
            match (val1.clone(), val2.clone()) {
                (Value::Number(num1), Value::Number(num2)) => Ok(Value::Number(num1 - num2)),
                _ => Err(Error::OperationUnimplemented {
                    op: parse::BinarithmOp::Minus,
                    term1: Box::new(val1),
                    term2: Box::new(val2),
                }),
            }
        }

        /// Handles a binary operation using the `+` operator.
        fn op_plus(&mut self, val1: Value, val2: Value) -> Result<Value, Error> {
            match (val1.clone(), val2.clone()) {
                (Value::Number(num1), Value::Number(num2)) => Ok(Value::Number(num1 + num2)),
                _ => Err(Error::OperationUnimplemented {
                    op: parse::BinarithmOp::Plus,
                    term1: Box::new(val1),
                    term2: Box::new(val2),
                }),
            }
        }

        /// Handles a binary operation using the `*` operator.
        fn op_times(&mut self, val1: Value, val2: Value) -> Result<Value, Error> {
            match (val1.clone(), val2.clone()) {
                (Value::Number(num1), Value::Number(num2)) => Ok(Value::Number(num1 * num2)),
                _ => Err(Error::OperationUnimplemented {
                    op: parse::BinarithmOp::Times,
                    term1: Box::new(val1),
                    term2: Box::new(val2),
                }),
            }
        }

        /// Handles a binary operation using the `:` range operator, e.g. `A1:C3`.
        fn op_range(&mut self, val1: Value, val2: Value) -> Result<Value, Error> {
            match (val1.clone(), val2.clone()) {
                (Value::Cellref(strval1), Value::Cellref(strval2)) => {
                    let range = CellAbsRange::from_cellref_explicit_range(&strval1, &strval2)
                        .map_err(|err| Error::FailedToParseCellref {
                            cellref: strval1.clone() + ":" + &strval2.clone(),
                        })?;
                    Ok(Value::Cellrange(strval1, strval2))
                }
                _ => Err(Error::OperationUnimplemented {
                    op: parse::BinarithmOp::Range,
                    term1: Box::new(val1),
                    term2: Box::new(val2),
                }),
            }
        }

        /// If `value` is a [`Value::Cellref`], returns the value of the cell being referred to.
        /// Otherwise, just returns `value`.
        fn try_deref(&mut self, value: Value) -> Result<Value, Error> {
            match value {
                Value::Cellref(strval) => {
                    let abs_pos = CellAbsPos::from_cellref(&strval).map_err(|err| {
                        Error::FailedToParseCellref {
                            cellref: strval.clone(),
                        }
                    })?;
                    Ok(self
                        .ctx
                        .sheet
                        .get_value(abs_pos)
                        .ok_or(Error::FailedToGetCellByCellref {
                            cellref: strval.clone(),
                        })?
                        .clone())
                }
                _ => Ok(value),
            }
        }

        /// Evaluates an expression of any kind.
        fn eval_expr(&mut self, e: parse::Expr) -> Result<Value, Error> {
            match e {
                parse::Expr::Binarithm { op, term1, term2 } => {
                    let (val1, val2) = match op {
                        parse::BinarithmOp::Div
                        | parse::BinarithmOp::Minus
                        | parse::BinarithmOp::Plus
                        | parse::BinarithmOp::Times => {
                            let val1_raw = self.eval_expr(*term1)?;
                            let val2_raw = self.eval_expr(*term2)?;
                            (self.try_deref(val1_raw)?, self.try_deref(val2_raw)?)
                        }
                        parse::BinarithmOp::Range => {
                            (self.eval_expr(*term1)?, self.eval_expr(*term2)?)
                        }
                    };
                    match op {
                        parse::BinarithmOp::Div => self.op_div(val1, val2),
                        parse::BinarithmOp::Minus => self.op_minus(val1, val2),
                        parse::BinarithmOp::Plus => self.op_plus(val1, val2),
                        parse::BinarithmOp::Times => self.op_times(val1, val2),
                        parse::BinarithmOp::Range => self.op_range(val1, val2),
                    }
                }
                parse::Expr::Call { name, args } => self.eval_call(&name, args),
                parse::Expr::TextLiteral(strval) => Ok(Value::Text(strval)),
                parse::Expr::NumberLiteral(num) => Ok(Value::Number(num)),
                parse::Expr::Cellref(strval) => Ok(Value::Cellref(strval)),
                parse::Expr::Name(_) => Err(Error::UnexpectedName),
            }
        }
    }

    #[derive(Debug, Default)]
    /// The state used when finding an expression's dependencies.
    pub struct DependencyFinder {
        pub dependencies: VecDeque<CellAbsPos>,
    }

    impl DependencyFinder {
        /// Finds and stores all of an expression's dependencies.
        fn find(&mut self, e: &parse::Expr) -> Result<(), Error> {
            match e {
                parse::Expr::Binarithm { op, term1, term2 } => {
                    match op {
                        parse::BinarithmOp::Div
                        | parse::BinarithmOp::Minus
                        | parse::BinarithmOp::Plus
                        | parse::BinarithmOp::Times => {
                            self.find(term1.as_ref())?;
                            self.find(term2.as_ref())?;
                        }
                        parse::BinarithmOp::Range => {
                            if let (parse::Expr::Cellref(strval1), parse::Expr::Cellref(strval2)) =
                                (term1.as_ref(), term2.as_ref())
                            {
                                let range =
                                    CellAbsRange::from_cellref_explicit_range(strval1, strval2)
                                        .map_err(|err| Error::FailedToParseCellref {
                                            cellref: strval1.clone() + ":" + &strval2.clone(),
                                        })?;
                                self.dependencies.extend(&range.expand());
                            }
                        }
                    };
                }
                parse::Expr::Call { name, args } => {
                    for arg in args {
                        self.find(arg)?;
                    }
                }
                parse::Expr::Cellref(strval) => {
                    self.dependencies
                        .push_back(CellAbsPos::from_cellref(strval).map_err(|_| {
                            Error::FailedToParseCellref {
                                cellref: strval.clone(),
                            }
                        })?);
                }
                _ => {}
            };
            Ok(())
        }
    }

    /// Evaluates a static formula, which is a formula that does not start with `=`.
    fn evaluate_static(formula: &str) -> Value {
        if let Ok(num) = Decimal::from_str(formula) {
            return Value::Number(num);
        }
        Value::Text(formula.to_string())
    }

    /// Takes a string containing a `formula` and evaluates it in a certain [`Context`], returning
    /// the value as a [`Value`].
    pub fn evaluate(ctx: &Context<'_>, formula: &str) -> (Value, VecDeque<CellAbsPos>) {
        let formula = formula.trim();
        if let Some(formula) = formula.strip_prefix('=') {
            let mut dependency_finder = DependencyFinder::default();
            let res = || -> Result<Value, Error> {
                let mut lexer = lex::Lexer::new(formula);
                let e = parse::parse_expr(&mut lexer).map_err(Error::ParseError)?;
                dependency_finder.find(e.as_ref())?;
                let mut evaluator = Evaluator::new(ctx);
                let value = evaluator.eval_expr(*e)?;
                let value = evaluator.try_deref(value)?;
                match value {
                    Value::Cellrange(_, _) => Err(Error::UnexpectedCellrange),
                    value => Ok(value),
                }
            }();
            match res {
                Ok(value) => (value, dependency_finder.dependencies),
                Err(err) => (Value::Error(err), dependency_finder.dependencies),
            }
        } else {
            (evaluate_static(formula), VecDeque::default())
        }
    }

    impl<'a> Evaluator<'a> {
        /// Evaluates a call expression, like `FOO(a, 5)`.
        fn eval_call(&mut self, name: &str, args: Vec<parse::Expr>) -> Result<Value, Error> {
            let mut arg_values: Vec<Value> = Vec::default();
            for arg in args {
                arg_values.push(self.eval_expr(arg)?);
            }
            match name {
                "SUM" => functions_check::sum(arg_values),
                _ => Err(Error::FunctionNotFound {
                    name: name.to_string(),
                }),
            }
        }
    }
}

mod functions_check {
    //! Checks arguments for each respective function in [`functions`].

    use super::*;

    pub fn sum(args: Vec<eval::Value>) -> Result<eval::Value, eval::Error> {
        let make_err = || eval::Error::FunctionArgError {
            function_name: "SUM".to_string(),
        };
        let first = args.first().ok_or_else(make_err)?;
        let eval::Value::Cellrange(start, end) = first else {
            return Err(make_err());
        };
        functions::sum(start, end)
    }
}

mod functions {
    //! Contains the functions used in formulas, such as `SUM()`.

    use super::*;

    #[doc = include_str!("../doc/functions/sum.md")]
    pub fn sum(start: &str, end: &str) -> Result<eval::Value, eval::Error> {
        Ok(eval::Value::Text("TODO".to_string()))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn lex() {
        let expected = [
            lex::Token::Lparen,
            lex::Token::Lparen,
            lex::Token::NumberLiteral(dec!(2.5)),
            lex::Token::Div,
            lex::Token::NumberLiteral(dec!(0.4)),
            lex::Token::Rparen,
            lex::Token::Minus,
            lex::Token::TextLiteral("a".to_string()),
            lex::Token::Rparen,
            lex::Token::Minus,
            lex::Token::Name("F".to_string()),
            lex::Token::Lparen,
            lex::Token::NumberLiteral(dec!(5)),
            lex::Token::Comma,
            lex::Token::Name("G".to_string()),
            lex::Token::Lparen,
            lex::Token::Cellref("A1".to_string()),
            lex::Token::Range,
            lex::Token::Cellref("XYZ333".to_string()),
            lex::Token::Comma,
            lex::Token::Name("c".to_string()),
            lex::Token::Rparen,
            lex::Token::Minus,
            lex::Token::NumberLiteral(dec!(2)),
            lex::Token::Rparen,
            lex::Token::Plus,
            lex::Token::Name("d".to_string()),
            lex::Token::Div,
            lex::Token::Name("a".to_string()),
            lex::Token::Times,
            lex::Token::Name("b".to_string()),
        ];
        let s = " ((2.5 / 0.4) - \"a\") - F(5, G(A1:XYZ333, c) - 2) + d / a * b";
        let mut lexer = lex::Lexer::new(s);
        for expected_token in expected {
            assert_eq!(lexer.lex(), Ok(Some(expected_token)));
        }
        assert_eq!(lexer.lex(), Ok(None));
    }

    #[test]
    fn parse_small_expr() {
        let expected = Box::new(parse::Expr::NumberLiteral(dec!(2.5)));
        let s = "2.5";
        let mut lexer = lex::Lexer::new(s);
        assert_eq!(parse::parse_expr(&mut lexer), Ok(expected));
    }

    #[test]
    fn parse_big_expr() {
        let expected = Box::new(parse::Expr::Binarithm {
            op: parse::BinarithmOp::Plus,
            term1: Box::new(parse::Expr::Binarithm {
                op: parse::BinarithmOp::Minus,
                term1: Box::new(parse::Expr::Binarithm {
                    op: parse::BinarithmOp::Minus,
                    term1: Box::new(parse::Expr::Binarithm {
                        op: parse::BinarithmOp::Div,
                        term1: Box::new(parse::Expr::NumberLiteral(dec!(2.5))),
                        term2: Box::new(parse::Expr::NumberLiteral(dec!(0.4))),
                    }),
                    term2: Box::new(parse::Expr::TextLiteral("a".to_string())),
                }),
                term2: Box::new(parse::Expr::Call {
                    name: "F".to_string(),
                    args: vec![
                        parse::Expr::NumberLiteral(dec!(5)),
                        parse::Expr::Binarithm {
                            op: parse::BinarithmOp::Minus,
                            term1: Box::new(parse::Expr::Call {
                                name: "G".to_string(),
                                args: vec![
                                    parse::Expr::Binarithm {
                                        op: parse::BinarithmOp::Range,
                                        term1: Box::new(parse::Expr::Cellref("A1".to_string())),
                                        term2: Box::new(parse::Expr::Cellref("XYZ333".to_string())),
                                    },
                                    parse::Expr::Name("c".to_string()),
                                ],
                            }),
                            term2: Box::new(parse::Expr::NumberLiteral(dec!(2))),
                        },
                    ],
                }),
            }),
            term2: Box::new(parse::Expr::Binarithm {
                op: parse::BinarithmOp::Times,
                term1: Box::new(parse::Expr::Binarithm {
                    op: parse::BinarithmOp::Div,
                    term1: Box::new(parse::Expr::Name("d".to_string())),
                    term2: Box::new(parse::Expr::Name("a".to_string())),
                }),
                term2: Box::new(parse::Expr::Name("b".to_string())),
            }),
        });
        let s = "((2.5 / 0.4) - \"a\") - F(5, G(A1:XYZ333, c) - 2) + d / a * b";
        let mut lexer = lex::Lexer::new(s);
        assert_eq!(parse::parse_expr(&mut lexer), Ok(expected));
    }

    #[test]
    fn eval_static_number_expr() {
        let s = "12345";
        let sheet = storage::Sheet::default();
        let ctx = eval::Context::new(&sheet);
        let (value, dependencies) = eval::evaluate(&ctx, s).expect("evaluation failed");
        assert_eq!(value, eval::Value::Number(dec!(12345)));
    }

    #[test]
    fn eval_static_text_expr() {
        let s = "1 + 2";
        let sheet = storage::Sheet::default();
        let ctx = eval::Context::new(&sheet);
        let (value, dependencies) = eval::evaluate(&ctx, s).expect("evaluation failed");
        assert_eq!(value, eval::Value::Text("1 + 2".to_string()));
    }

    #[test]
    fn eval() {
        let s = "= 1 + 2";
        let sheet = storage::Sheet::default();
        // TODO: Proper tests with some mock sheets here
        let ctx = eval::Context::new(&sheet);
        let (value, dependencies) = eval::evaluate(&ctx, s).expect("evaluation failed");
        assert_eq!(value, eval::Value::Number(dec!(3)));
    }
}

use laps::{lexer::Lexer, prelude::*, reader::Reader, span::Span, token::TokenBuffer};
use std::{fmt, io, str};

/// Kind of tokens.
#[token_kind]
#[derive(Debug, Tokenize)]
enum TokenKind {
  /// Spaces and comments.
  #[skip(r"\s+|;.*\n|;.*")]
  _Skip,
  /// Quote.
  #[regex(r"'")]
  Quote,
  /// Parentheses.
  #[regex(r"(|)")]
  Paren(char),
  /// Number.
  #[regex(r"-?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?")]
  Num(f64),
  /// String.
  #[regex(r#""([^\x00-\x1f"\\]|\\(["\\/bfnrt]|u[0-9a-fA-F]{4}))*""#, str_literal)]
  Str(String),
  /// Symbol.
  #[regex(r"[^\s()]+")]
  Sym(Sym),
  /// End-of-file.
  #[eof]
  Eof,
}

/// Symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Sym(String);

impl fmt::Display for Sym {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    self.0.fmt(f)
  }
}

impl str::FromStr for Sym {
  type Err = <String as str::FromStr>::Err;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    String::from_str(s).map(Sym)
  }
}

/// Parses the given string literal.
fn str_literal(s: &str) -> Option<String> {
  let mut buf = String::new();
  let mut escape = false;
  let mut hex_num = 0;
  let mut hex = 0;
  for c in s[1..s.len() - 1].chars() {
    if escape {
      if hex_num > 0 && c.is_ascii_digit() {
        hex = hex * 16 + c.to_digit(16)?;
        hex_num -= 1;
        if hex_num == 0 {
          buf.push(char::from_u32(hex)?);
          hex = 0;
          escape = false;
        }
      } else if c == 'u' {
        hex_num = 4;
      } else {
        match c {
          '"' => buf.push('"'),
          '\\' => buf.push('\\'),
          '/' => buf.push('/'),
          'b' => buf.push('\x08'),
          'f' => buf.push('\x0c'),
          'n' => buf.push('\n'),
          'r' => buf.push('\r'),
          't' => buf.push('\t'),
          _ => return None,
        }
        escape = false;
      }
    } else {
      match c {
        '\\' => escape = true,
        c => buf.push(c),
      }
    }
  }
  Some(buf)
}

/// Type of token.
type Token = laps::token::Token<TokenKind>;

token_ast! {
  #[derive(Debug)]
  macro Token<TokenKind> {
    [quote] => { kind: TokenKind::Quote },
    [lpr] => { kind: TokenKind::Paren('(') },
    [rpr] => { kind: TokenKind::Paren(')') },
    [num] => { kind: TokenKind::Num(_), prompt: "number" },
    [str] => { kind: TokenKind::Str(_), prompt: "string" },
    [sym] => { kind: TokenKind::Sym(_), prompt: "symbol" },
    [eof] => { kind: TokenKind::Eof },
  }
}

/// Statement.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
enum Statement {
  Elem(Elem),
  End(Token![eof]),
}

/// Element.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
enum Elem {
  Num(Token![num]),
  Str(Token![str]),
  Sym(Token![sym]),
  Quote(Quote),
  List(List),
}

/// Quoted element.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
struct Quote {
  _quote: Token![quote],
  elem: Box<Elem>,
}

/// List.
#[derive(Debug, Parse, Spanned)]
#[token(Token)]
struct List {
  _lpr: Token![lpr],
  elems: Vec<Elem>,
  _rpr: Token![rpr],
}

/// Parser.
pub struct Parser<R> {
  tokens: TokenBuffer<Lexer<Reader<R>, TokenKind>, Token>,
}

impl<R> Parser<R> {
  /// Creates a new parser.
  pub fn new(reader: Reader<R>) -> Self {
    Self {
      tokens: TokenBuffer::new(TokenKind::lexer(reader)),
    }
  }

  /// Parses the next element from the reader. Returns [`Ok(None)`] on EOF.
  pub fn parse(&mut self) -> laps::span::Result<Option<Element>>
  where
    R: io::Read,
  {
    Ok(match self.tokens.parse::<Statement>()? {
      Statement::Elem(elem) => Some(Self::elem_to_element(elem)),
      Statement::End(_) => None,
    })
  }

  /// Converts [`Elem`] to [`Element`].
  fn elem_to_element(elem: Elem) -> Element {
    let span = elem.span();
    let kind = match elem {
      Elem::Num(num) => ElemKind::Num(num.unwrap()),
      Elem::Str(str) => ElemKind::Str(str.unwrap()),
      Elem::Sym(sym) => ElemKind::Sym(sym.unwrap::<Sym, _>().0),
      Elem::Quote(quote) => ElemKind::Quote(Box::new(Self::elem_to_element(*quote.elem))),
      Elem::List(list) => {
        ElemKind::List(list.elems.into_iter().map(Self::elem_to_element).collect())
      }
    };
    Element { kind, span }
  }
}

/// Element.
#[derive(Debug, Clone)]
pub struct Element {
  pub kind: ElemKind,
  pub span: Span,
}

/// Kind of element.
#[derive(Debug, Clone)]
pub enum ElemKind {
  /// Number.
  Num(f64),
  /// String.
  Str(String),
  /// Symbol.
  Sym(String),
  /// Quoted element.
  Quote(Box<Element>),
  /// List.
  List(Vec<Element>),
}

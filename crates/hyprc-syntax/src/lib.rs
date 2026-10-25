//! Rust syntax for hyprc: tokens, the lexer, the syntax tree and the parser.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod token;

pub use lexer::tokenize;
pub use parser::{
    Edition, MAX_DEPTH, PARSER_STACK_SIZE, PErr, PResult, Parser, PathStyle, parse_file,
};

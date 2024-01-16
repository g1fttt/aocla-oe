#![allow(dead_code)]

use std::collections::HashMap;
use std::io::Write;
use std::path::Path;
use std::{error, fmt, fs, io, str};

#[rustfmt::skip]
#[derive(Debug, Clone)]
enum ObjectKind {
    Int(isize),
    List(Vec<Object>),
    Tuple { data: Vec<Object>, is_quoted: bool },
    Str(String),
    Bool(bool),
    Symbol { data: String, is_quoted: bool },
}

#[derive(Debug, Clone)]
struct Object {
    kind: ObjectKind,
    line: usize,
    column: usize,
}

impl Object {
    fn value<T>(&self) -> Result<&T> {
        use std::any::type_name as tname;
        use std::mem::transmute as trans;

        macro_rules! err_if_neq {
            ($v:expr, $a:ty, $b:ty) => {{
                if tname::<$a>() != tname::<$b>() {
                    return Err(error!(self.line, self.column, "Type mismatch"));
                }
                $v
            }};
        }

        use ObjectKind::*;
        Ok(unsafe {
            match &self.kind {
                Int(i) => err_if_neq!(trans(i), isize, T),
                List(v) => err_if_neq!(trans(v), Vec<Object>, T),
                Tuple { data, .. } => err_if_neq!(trans(data), Vec<Object>, T),
                Str(s) => err_if_neq!(trans(s), String, T),
                Bool(b) => err_if_neq!(trans(b), bool, T),
                Symbol { data, .. } => err_if_neq!(trans(data), String, T),
            }
        })
    }
}

enum Proc {
    Aocla(Object),
    Rust(fn(&mut AoclaCtx) -> Result),
}

#[derive(Debug)]
struct AoclaError {
    message: &'static str,
    line: usize,
    column: usize,
}

impl fmt::Display for AoclaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: Add also a filename
        writeln!(
            f,
            "Error occured: {}. At line {} and column {}",
            self.message, self.line, self.column
        )
    }
}

impl error::Error for AoclaError {}

#[macro_export]
macro_rules! error {
    ($line:expr, $column:expr, $message:expr) => {
        AoclaError {
            message: $message,
            line: $line,
            column: $column,
        }
    };
    ($object:expr, $message:expr) => {{
        let object = $object.as_ref().unwrap();
        AoclaError {
            message: $message,
            line: object.line,
            column: object.column,
        }
    }};
}

#[inline(always)]
fn column(idx: usize, line: usize) -> usize {
    idx + 1 - line
}

#[derive(Default)]
struct AoclaCtx {
    stack: Vec<Object>,
    proc: HashMap<String, Proc>,
    frame: HashMap<String, Object>,
    cur_proc_name: Option<String>,
    cur_object: Option<Object>,
}

impl AoclaCtx {
    fn new() -> Self {
        let mut ctx = Self::default();
        ctx.load_library();
        ctx
    }

    fn pop_stack(&mut self) -> Result<Object> {
        self.stack
            .pop()
            .ok_or(error!(self.cur_object, "Out of stack"))
    }

    fn peek_stack(&self) -> Result<&Object> {
        self.stack
            .last()
            .ok_or(error!(self.cur_object, "Out of stack"))
    }

    #[inline]
    fn add_proc(&mut self, name: &str, proc: Proc) {
        self.proc.insert(name.to_owned(), proc);
    }

    fn load_library(&mut self) {
        self.add_proc("+", Proc::Rust(arithmetic_proc()));
        self.add_proc("-", Proc::Rust(arithmetic_proc()));
        self.add_proc("*", Proc::Rust(arithmetic_proc()));
        self.add_proc("/", Proc::Rust(arithmetic_proc()));
        self.add_proc("print", Proc::Rust(print_proc()));
        self.add_proc("println", Proc::Rust(print_proc()));
    }

    fn call_proc(&mut self, proc_name: String, f: impl Fn(&mut Self) -> Result) -> Result {
        let prev_proc_name = self.cur_proc_name.clone();
        let prev_stack_frame = self.frame.clone();

        self.cur_proc_name = Some(proc_name);

        // TODO: Implement `upeval` by not creating new frame
        self.frame = Default::default();

        f(self)?;

        self.frame = prev_stack_frame;
        self.cur_proc_name = prev_proc_name;

        Ok(())
    }

    fn call_aocla_proc(&mut self, data: String, obj: Object) -> Result {
        self.call_proc(data, |ctx| ctx.eval(obj.clone()))
    }

    fn dequote_and_push(&mut self, obj: &Object) {
        let mut notq = obj.clone();
        match notq.kind {
            ObjectKind::Tuple {
                ref mut is_quoted, ..
            }
            | ObjectKind::Symbol {
                ref mut is_quoted, ..
            } => {
                *is_quoted = false;
            }
            _ => unreachable!(),
        }
        self.stack.push(notq);
    }

    fn eval_tuple(&mut self, data: &Vec<Object>) -> Result {
        for obj in data {
            let ObjectKind::Symbol { data, .. } = &obj.kind else {
                return Err(error!(self.cur_object, "Cannot capture non-symbol objects"));
            };
            let obj = self.pop_stack()?;
            self.frame.insert(data.clone(), obj);
        }
        Ok(())
    }

    fn eval_symbol(&mut self, data: &String) -> Result {
        if let Some(data) = data.strip_prefix('$') {
            let Some(local) = self.frame.get(data) else {
                return Err(error!(self.cur_object, "Unbound local variable"));
            };
            self.stack.push(local.clone());
        } else {
            let Some(proc) = self.proc.get(data) else {
                return Err(error!(self.cur_object, "Unbound procedure"));
            };
            match proc {
                Proc::Rust(f) => self.call_proc(data.clone(), *f)?,
                Proc::Aocla(o) => self.call_aocla_proc(data.clone(), o.clone())?,
            }
        }
        Ok(())
    }

    fn eval(&mut self, root_obj: Object) -> Result {
        let root_obj_list: &Vec<Object> = root_obj.value()?;

        for obj in root_obj_list {
            self.cur_object = Some(obj.clone());
            match &obj.kind {
                ObjectKind::Tuple { data, is_quoted } => {
                    if *is_quoted {
                        self.dequote_and_push(obj);
                    } else {
                        if self.stack.len() < data.len() {
                            return Err(error!(
                                self.cur_object,
                                "Out of stack while capturing local variable"
                            ));
                        }
                        self.eval_tuple(data)?;
                    }
                }
                ObjectKind::Symbol { data, is_quoted } => {
                    if *is_quoted {
                        self.dequote_and_push(obj);
                    } else {
                        self.eval_symbol(data)?;
                    }
                }
                _ => self.stack.push(obj.clone()),
            }
        }
        Ok(())
    }
}

fn arithmetic_proc() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let b_obj = ctx.pop_stack()?;
        let a_obj = ctx.pop_stack()?;

        let b = *b_obj.value::<isize>()?;
        let a = *a_obj.value::<isize>()?;

        ctx.stack.push(Object {
            kind: ObjectKind::Int(match ctx.cur_proc_name.as_ref().unwrap().as_str() {
                "+" => a + b,
                "-" => a - b,
                "*" => a * b,
                "/" => a / b,
                _ => unreachable!(),
            }),
            line: b_obj.line,
            column: b_obj.column,
        });
        Ok(())
    }
}

fn print_proc() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let obj = ctx.peek_stack()?;

        use ObjectKind::*;
        match &obj.kind {
            Int(i) => print!("{}", i),
            List(v) => print!("{:?}", v), // TODO: Pretty print
            Tuple { data, .. } => print!("{:?}", data),
            Str(s) => print!("{}", s),
            Bool(b) => print!("{}", b),
            Symbol { data, .. } => print!("{}", data),
        }

        let should_print_nl = ctx
            .cur_proc_name
            .as_ref()
            .is_some_and(|s| s.as_str() == "println");

        if should_print_nl {
            println!();
        } else {
            io::stdout().flush().unwrap();
        }
        Ok(())
    }
}

#[derive(Debug)]
struct Parser {
    src: Vec<char>,
    idx: usize,
    line: usize,
    column: usize,
}

impl Parser {
    fn new(src: &str) -> Self {
        let src = format!("[{}]", src).chars().collect();
        Self {
            src,
            idx: 0,
            line: 1,
            column: 0,
        }
    }

    #[inline]
    fn curr(&self) -> char {
        self.src[self.idx]
    }

    #[inline]
    fn next(&self) -> char {
        self.src[self.idx + 1]
    }

    fn consume_space(&mut self) {
        loop {
            while self.curr().is_whitespace() {
                if self.curr() == '\n' {
                    self.line += 1;
                }
                self.idx += 1;
            }
            if self.curr() != '/' || self.next() != '/' {
                break;
            }
            while self.curr() != '\n' {
                self.idx += 1;
            }
        }
    }

    fn parse_integer(&mut self) -> ObjectKind {
        let start = self.idx;
        while matches!(self.curr(), '0'..='9' | '-') {
            self.idx += 1;
        }
        let num = self.src[start..self.idx]
            .iter()
            .collect::<String>()
            .parse()
            .unwrap();
        ObjectKind::Int(num)
    }

    fn skip_if_quoted(&mut self) -> bool {
        let is_quoted = self.curr() == '\'';
        if is_quoted {
            self.idx += 1;
        }
        is_quoted
    }

    fn parse_sequence(&mut self, lbracket: char) -> Result<ObjectKind> {
        let is_quoted = self.skip_if_quoted();
        self.idx += 1; // left bracket

        let rbracket = match lbracket {
            '(' => ')',
            '[' => ']',
            _ => unreachable!(),
        };

        let mut data = Vec::new();
        loop {
            self.consume_space();

            // Earlier, we skipped the quote and the bracket.
            // That's why we're doing `.wrapping_sub(2)`
            let (start_line, start_column) =
                (self.line, column(self.idx, self.line).wrapping_sub(2));

            if self.curr() == rbracket {
                self.idx += 1;
                return Ok(match rbracket {
                    ']' => ObjectKind::List(data),
                    ')' => ObjectKind::Tuple { data, is_quoted },
                    _ => unreachable!(),
                });
            }

            data.push(self.parse_object()?);
            if self.idx >= self.src.len() {
                return Err(error!(start_line, start_column, "Sequence never closed"));
            }
        }
    }

    fn parse_symbol(&mut self) -> ObjectKind {
        let is_quoted = self.skip_if_quoted();

        let start = self.idx;
        while is_symbol(self.curr()) {
            self.idx += 1;
        }

        let data = self.src[start..self.idx].iter().collect();
        ObjectKind::Symbol { data, is_quoted }
    }

    fn parse_boolean(&mut self) -> Result<ObjectKind> {
        let state = self.next();
        if state != 't' && state != 'f' {
            return Err(error!(
                self.line,
                self.column, "Booleans are either #t or #f"
            ));
        }
        self.idx += 2;
        Ok(ObjectKind::Bool(state == 't'))
    }

    fn parse_string(&mut self) -> Result<ObjectKind> {
        let (start_line, start_column) = (self.line, column(self.idx, self.line));
        self.idx += 1;

        let start = self.idx;
        while self.curr() != '"' {
            self.idx += 1;
            if self.idx >= self.src.len() {
                return Err(error!(start_line, start_column, "String never closed"));
            }
        }

        let (mut chars, mut buf) = {
            let chars = &self.src[start..self.idx];
            (chars.iter(), String::with_capacity(chars.len()))
        };

        while let Some(&c) = chars.next() {
            if c == '\\' {
                let Some(nc) = chars.next() else {
                    break;
                };
                buf.push(match nc {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    &nc => nc,
                });
            } else {
                buf.push(c);
            }
        }
        self.idx += 1;

        buf.shrink_to_fit();
        Ok(ObjectKind::Str(buf))
    }

    fn parse_object(&mut self) -> Result<Object> {
        self.consume_space();

        self.column = column(self.idx, self.line);

        Ok(Object {
            line: self.line,
            column: self.column,
            kind: match self.curr() {
                c if is_symbol(c) => self.parse_symbol(),
                lb @ '(' | lb @ '[' => self.parse_sequence(lb)?,
                '0'..='9' | '-' => self.parse_integer(),
                '#' => self.parse_boolean()?,
                '"' => self.parse_string()?,
                '\'' => match self.next() {
                    c if is_symbol(c) => self.parse_symbol(),
                    lb @ '(' => self.parse_sequence(lb)?,
                    _ => {
                        return Err(error!(
                            self.line,
                            self.column, "Only symbols and tuples can be quoted"
                        ))
                    }
                },
                ')' | ']' => return Err(error!(self.line, self.column, "Sequence never opened")),
                _ => {
                    return Err(error!(
                        self.line,
                        self.column, "No object type starts like this"
                    ))
                }
            },
        })
    }
}

fn is_symbol(c: char) -> bool {
    matches!(c, 'a'..='z'
    | 'A'..='Z'
    | '@'
    | '$'
    | '+'
    | '-'
    | '*'
    | '/'
    | '='
    | '?'
    | '%'
    | '>'
    | '<'
    | '_'
    )
}

fn eval_file<P>(filename: P) -> Result
where
    P: AsRef<Path>,
{
    let Ok(buf) = fs::read_to_string(&filename) else {
        panic!(
            "Failed to read file: {:?}. Does it exists?",
            filename.as_ref()
        );
    };

    let mut parser = Parser::new(&buf);
    let obj = parser.parse_object()?;

    let mut ctx = AoclaCtx::new();
    ctx.eval(obj)?;

    Ok(())
}

fn repl() {
    let mut ctx = AoclaCtx::new();
    loop {
        print!("> ");
        io::stdout().flush().unwrap();

        let mut buf = String::new();
        io::stdin().read_line(&mut buf).unwrap();

        match buf.trim() {
            "quit" | "exit" | "leave" => break,
            code => {
                let mut parser = Parser::new(code);
                let Ok(root_obj) = parser.parse_object() else {
                    continue;
                };
                let _ = ctx.eval(root_obj);
            }
        }
    }
}

type Result<T = ()> = std::result::Result<T, AoclaError>;

#[inline(always)]
fn main() {
    repl()
}

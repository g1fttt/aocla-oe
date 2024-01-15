#![allow(dead_code)]

use std::collections::HashMap;
use std::io::Write;
use std::mem::{self, Discriminant};
use std::path::Path;
use std::{fs, io, str};

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
    line: usize, // TODO: Use in error message
}

impl From<ObjectKind> for Object {
    fn from(kind: ObjectKind) -> Self {
        Self { kind, line: 0 }
    }
}

impl Object {
    fn value<T>(&self) -> Result<&T> {
        use std::any::type_name as tname;
        use std::mem::transmute as trans;

        macro_rules! err_if_neq {
            ($v:expr, $a:ty, $b:ty) => {{
                if tname::<$a>() != tname::<$b>() {
                    return Err("Type mismatch");
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

    #[inline]
    fn kind(&self) -> Discriminant<ObjectKind> {
        mem::discriminant(&self.kind)
    }

    #[cfg(debug_assertions)]
    fn traverse(&self) {
        fn traverse(obj: &Object, indent: Option<usize>) {
            let indent = indent.unwrap_or(0);
            print!("{}", " ".repeat(indent));

            use ObjectKind::*;

            const STEP: usize = 2;

            match &obj.kind {
                Int(i) => println!("Int: {}", i),
                List(v) => {
                    println!("List:");
                    v.iter().for_each(|o| traverse(o, Some(indent + STEP)));
                }
                Tuple { data, is_quoted } => {
                    println!("Tuple (is_quoted = {}):", is_quoted);
                    data.iter().for_each(|o| traverse(o, Some(indent + STEP)));
                }
                Str(s) => println!("Str: {:?}", s),
                Bool(b) => println!("Bool: {}", b),
                Symbol { data, is_quoted } => {
                    println!("Symbol (is_quoted = {}): {}", is_quoted, data)
                }
            }
        }
        traverse(self, None);
    }
}

#[derive(Debug)]
enum Proc {
    Aocla(Object),
    Rust(fn(&mut AoclaCtx) -> Result),
}

#[derive(Debug, Default)]
struct AoclaCtx {
    stack: Vec<Object>,
    proc: HashMap<String, Proc>,
    frame: HashMap<String, Object>,
    cur_proc_name: Option<String>,
}

impl AoclaCtx {
    fn new() -> Self {
        let mut ctx = Self::default();
        ctx.load_library();
        ctx
    }

    fn pop_stack(&mut self) -> Result<Object> {
        self.stack.pop().ok_or("Out of stack")
    }

    fn basic_math(&self) -> fn(&mut Self) -> Result {
        |ctx| {
            let b = ctx.pop_stack()?;
            let a = ctx.pop_stack()?;

            let b = *b.value::<isize>()?;
            let a = *a.value::<isize>()?;

            ctx.stack.push(Object::from(ObjectKind::Int(
                match ctx.cur_proc_name.as_ref().unwrap().as_str() {
                    "+" => a + b,
                    "-" => a - b,
                    "*" => a * b,
                    "/" => a / b,
                    _ => unreachable!(),
                },
            )));
            Ok(())
        }
    }

    fn print_proc(&self) -> fn(&mut Self) -> Result {
        |ctx| {
            let obj = ctx.pop_stack()?;

            use ObjectKind::*;
            match obj.kind {
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

    #[inline]
    fn add_proc(&mut self, name: &str, proc: Proc) {
        self.proc.insert(name.to_owned(), proc);
    }

    fn load_library(&mut self) {
        self.add_proc("+", Proc::Rust(self.basic_math()));
        self.add_proc("-", Proc::Rust(self.basic_math()));
        self.add_proc("*", Proc::Rust(self.basic_math()));
        self.add_proc("/", Proc::Rust(self.basic_math()));
        self.add_proc("print", Proc::Rust(self.print_proc()));
        self.add_proc("println", Proc::Rust(self.print_proc()));
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
                return Err("Cannot capture non-symbol objects");
            };
            let obj = self.pop_stack()?;
            self.frame.insert(data.clone(), obj);
        }
        Ok(())
    }

    fn eval_symbol(&mut self, data: &String) -> Result {
        if let Some(data) = data.strip_prefix('$') {
            let Some(local) = self.frame.get(data) else {
                return Err("Unbound local variable");
            };
            self.stack.push(local.clone());
        } else {
            let Some(proc) = self.proc.get(data) else {
                return Err("Unbound procedure");
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
            match &obj.kind {
                ObjectKind::Tuple { data, is_quoted } => {
                    if *is_quoted {
                        self.dequote_and_push(obj);
                    } else {
                        if self.stack.len() < data.len() {
                            return Err("Out of stack while capturing local");
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

#[derive(Debug)]
struct Parser {
    src: Vec<char>,
    idx: usize,
    line: usize,
}

impl Parser {
    fn new(src: &str) -> Self {
        let src = format!("[{}]", src).chars().collect();
        Self {
            src,
            idx: 0,
            line: 1,
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

    #[inline]
    fn is_integer(&self) -> bool {
        (self.curr() == '-' && self.next().is_numeric()) || self.curr().is_numeric()
    }

    fn parse_integer(&mut self) -> ObjectKind {
        let start = self.idx;
        while self.curr().is_numeric() || self.curr() == '-' {
            self.idx += 1;
        }
        let num = self.src[start..self.idx]
            .iter()
            .collect::<String>()
            .parse()
            .unwrap();
        ObjectKind::Int(num)
    }

    #[inline]
    fn is_list(&self) -> bool {
        self.curr() == '['
    }

    #[inline]
    fn is_tuple(&self) -> bool {
        self.curr() == '('
    }

    #[inline]
    fn is_quote(&self) -> bool {
        self.curr() == '\''
    }

    #[inline]
    fn is_quoted_tuple(&self) -> bool {
        self.is_quote() && self.next() == '('
    }

    fn parse_sequence_until(&mut self, stop_bracket: char) -> Result<ObjectKind> {
        let is_quoted = self.is_quote();
        if is_quoted {
            self.idx += 1;
        }
        self.idx += 1; // [ or (

        let mut data = Vec::new();
        loop {
            self.consume_space();
            if self.curr() == stop_bracket {
                self.idx += 1;
                return Ok(match stop_bracket {
                    ']' => ObjectKind::List(data),
                    ')' => ObjectKind::Tuple { data, is_quoted },
                    _ => unreachable!(),
                });
            }

            data.push(self.parse_object()?);
            if self.idx >= self.src.len() {
                return Err("List never closed");
            }
        }
    }

    fn is_symbol(&self) -> bool {
        self.curr().is_alphabetic()
            || matches!(
                self.curr(),
                '@' | '$' | '+' | '-' | '*' | '/' | '=' | '?' | '%' | '>' | '<' | '_' | '\''
            )
    }

    fn parse_symbol(&mut self) -> ObjectKind {
        let is_quoted = self.is_quote();
        if is_quoted {
            self.idx += 1;
        }

        let start = self.idx;
        while self.is_symbol() {
            self.idx += 1;
        }

        let data = self.src[start..self.idx].iter().collect();
        ObjectKind::Symbol { data, is_quoted }
    }

    #[inline]
    fn is_boolean(&self) -> bool {
        self.curr() == '#'
    }

    fn parse_boolean(&mut self) -> Result<ObjectKind> {
        let state = self.next();
        if state != 't' && state != 'f' {
            return Err("Booleans are either #t or #f");
        }
        self.idx += 2;
        Ok(ObjectKind::Bool(state == 't'))
    }

    #[inline]
    fn is_string(&self) -> bool {
        self.curr() == '"'
    }

    fn parse_string(&mut self) -> Result<ObjectKind> {
        self.idx += 1;

        let start = self.idx;
        while self.curr() != '"' {
            self.idx += 1;
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
        Ok(Object {
            line: self.line,
            kind: if self.is_integer() {
                self.parse_integer()
            } else if self.is_list() {
                self.parse_sequence_until(']')?
            } else if self.is_tuple() || self.is_quoted_tuple() {
                self.parse_sequence_until(')')?
            } else if self.is_symbol() {
                self.parse_symbol()
            } else if self.is_boolean() {
                self.parse_boolean()?
            } else if self.is_string() {
                self.parse_string()?
            } else {
                return Err("No object type starts like this");
            },
        })
    }
}

fn eval_file<P>(filename: P) -> Result
where
    P: AsRef<Path>,
{
    let buf = fs::read_to_string(filename).map_err(|_| "Failed to read file (does it exists?)")?;

    let mut parser = Parser::new(&buf);
    let obj = parser.parse_object()?;

    let mut ctx = AoclaCtx::new();
    ctx.eval(obj)?;

    Ok(())
}

fn repl() -> Result {
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
                let root_obj = parser.parse_object()?;
                root_obj.traverse();

                ctx.eval(root_obj)?;
            }
        }
    }
    Ok(())
}

type Result<T = ()> = std::result::Result<T, &'static str>;

fn main() -> Result {
    repl()
}

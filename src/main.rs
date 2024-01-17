use std::cmp::Ordering;
use std::collections::HashMap;
use std::io::Write;
use std::path::Path;
use std::{env, error, fmt, fs, io, str};

#[rustfmt::skip]
#[derive(Debug, Clone)]
enum ObjectKind {
    Int(isize),
    List(Vec<Object>),
    Tuple(Vec<Object>, bool),
    Str(String),
    Bool(bool),
    Symbol(String, bool),
}

#[derive(Debug, Clone)]
struct Object {
    kind: ObjectKind,
    line: usize,
    column: usize,
}

impl From<ObjectKind> for Object {
    fn from(kind: ObjectKind) -> Self {
        Self {
            kind,
            line: 0,
            column: 0,
        }
    }
}

#[derive(Debug)]
enum Proc {
    Aocla(Object),
    Rust(fn(&mut AoclaCtx) -> Result),
}

#[derive(Debug)]
struct AoclaError {
    message: String,
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
            message: $message.to_owned(),
            line: $line,
            column: $column,
        }
    };
    ($object:expr, $message:expr) => {{
        let object = $object.as_ref().unwrap();
        error!(object.line, object.column, $message)
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
    fn new() -> Result<Self> {
        let mut ctx = Self::default();
        ctx.load_library()?;
        Ok(ctx)
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

    fn add_proc_string(&mut self, name: &str, proc_body: &str) -> Result {
        let mut parser = Parser::new(proc_body);
        let obj = parser.parse_object()?;

        self.add_proc(name, Proc::Aocla(obj));

        Ok(())
    }

    #[inline]
    fn add_proc(&mut self, name: &str, proc: Proc) {
        self.proc.insert(name.to_owned(), proc);
    }

    fn load_library(&mut self) -> Result {
        self.add_proc("+", Proc::Rust(arithmetic_proc()));
        self.add_proc("-", Proc::Rust(arithmetic_proc()));
        self.add_proc("*", Proc::Rust(arithmetic_proc()));
        self.add_proc("/", Proc::Rust(arithmetic_proc()));
        self.add_proc("=", Proc::Rust(compare_proc()));
        self.add_proc("<>", Proc::Rust(compare_proc()));
        self.add_proc(">=", Proc::Rust(compare_proc()));
        self.add_proc("<=", Proc::Rust(compare_proc()));
        self.add_proc(">", Proc::Rust(compare_proc()));
        self.add_proc("<", Proc::Rust(compare_proc()));
        self.add_proc("print", Proc::Rust(print_proc()));
        self.add_proc("println", Proc::Rust(print_proc()));
        self.add_proc("proc", Proc::Rust(proc_proc()));
        self.add_proc("if", Proc::Rust(proc_if()));
        self.add_proc("ifelse", Proc::Rust(proc_if()));
        self.add_proc("while", Proc::Rust(proc_while()));
        self.add_proc("get", Proc::Rust(proc_get()));
        self.add_proc_string("dup", "(x) $x $x")?;
        self.add_proc_string("swap", "(x y) $y $x")?;
        self.add_proc_string("drop", "(_)")?;
        Ok(())
    }

    fn call_proc(&mut self, proc_name: String, f: impl Fn(&mut Self) -> Result) -> Result {
        let prev_proc_name = self.cur_proc_name.clone();

        self.cur_proc_name = Some(proc_name);
        f(self)?;
        self.cur_proc_name = prev_proc_name;

        Ok(())
    }

    fn call_aocla_proc(&mut self, proc_name: String, proc_body: Object) -> Result {
        let prev_stack_frame = self.frame.clone();

        self.frame = Default::default();
        self.call_proc(proc_name, |ctx| ctx.eval(&proc_body))?;
        self.frame = prev_stack_frame;

        Ok(())
    }

    fn dequote_and_push(&mut self, mut notq: Object) {
        match notq.kind {
            ObjectKind::Tuple(_, ref mut is_quoted) | ObjectKind::Symbol(_, ref mut is_quoted) => {
                *is_quoted = false;
            }
            _ => unreachable!(),
        }
        self.stack.push(notq);
    }

    fn eval_tuple(&mut self, tuple: &Vec<Object>) -> Result {
        for obj in tuple {
            let ObjectKind::Symbol(sym, _) = &obj.kind else {
                return Err(error!(
                    self.cur_object,
                    "Only objects of type Symbol can be captured"
                ));
            };
            let obj = self.pop_stack()?;
            self.frame.insert(sym.clone(), obj);
        }
        Ok(())
    }

    fn eval_symbol(&mut self, sym: &String) -> Result {
        if let Some(sym) = sym.strip_prefix('$') {
            let Some(local) = self.frame.get(sym) else {
                return Err(error!(self.cur_object, "Unbound local variable"));
            };
            self.stack.push(local.clone());
        } else {
            let Some(proc) = self.proc.get(sym) else {
                return Err(error!(self.cur_object, "Unbound procedure"));
            };
            match proc {
                Proc::Rust(f) => self.call_proc(sym.clone(), *f)?,
                Proc::Aocla(o) => self.call_aocla_proc(sym.clone(), o.clone())?,
            }
        }
        Ok(())
    }

    fn eval(&mut self, root_obj: &Object) -> Result {
        let ObjectKind::List(root_obj_list) = &root_obj.kind else {
            return Err(error!(
                root_obj.line,
                root_obj.column, "Root object must be of type List"
            ));
        };

        for obj in root_obj_list {
            self.cur_object = Some(obj.clone());
            match &obj.kind {
                ObjectKind::Tuple(tuple, is_quoted) => {
                    if *is_quoted {
                        self.dequote_and_push(obj.clone());
                    } else {
                        if self.stack.len() < tuple.len() {
                            return Err(error!(
                                self.cur_object,
                                "Out of stack while capturing local variable"
                            ));
                        }
                        self.eval_tuple(tuple)?;
                    }
                }
                ObjectKind::Symbol(sym, is_quoted) => {
                    if *is_quoted {
                        self.dequote_and_push(obj.clone());
                    } else {
                        self.eval_symbol(sym)?;
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

        let (ObjectKind::Int(b), ObjectKind::Int(a)) = (b_obj.kind, a_obj.kind) else {
            return Err(error!(ctx.cur_object, "Both objects must be of type Int"));
        };

        ctx.stack.push(Object::from(ObjectKind::Int(
            match ctx.cur_proc_name.as_deref().unwrap() {
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

fn compare_proc() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let b_obj = ctx.pop_stack()?;
        let a_obj = ctx.pop_stack()?;

        use ObjectKind::*;
        let ord = match (&a_obj.kind, &b_obj.kind) {
            (Int(a), Int(b)) => a.cmp(b),
            (Bool(a), Bool(b)) => a.cmp(b),
            (Str(a), Str(b))
            | (Symbol(a, _), Symbol(b, _))
            | (Str(a), Symbol(b, _))
            | (Symbol(b, _), Str(a)) => a.cmp(b),
            (List(a), List(b))
            | (Tuple(a, _), Tuple(b, _))
            | (List(a), Tuple(b, _))
            | (Tuple(b, _), List(a)) => a.len().cmp(&b.len()),
            _ => {
                ctx.stack.extend_from_slice(&[b_obj, a_obj]);
                return Err(error!(ctx.cur_object, "Unable to compare two objects"));
            }
        };

        let cur_proc_name = ctx.cur_proc_name.as_deref().unwrap();
        ctx.stack
            .push(Object::from(ObjectKind::Bool(match cur_proc_name {
                "=" => ord == Ordering::Equal,
                "<>" => ord != Ordering::Equal,
                ">=" => ord == Ordering::Equal || ord == Ordering::Greater,
                "<=" => ord == Ordering::Equal || ord == Ordering::Less,
                ">" => ord == Ordering::Greater,
                "<" => ord == Ordering::Less,
                _ => unreachable!(),
            })));
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
            Tuple(t, _) => print!("{:?}", t),
            Str(s) => print!("{}", s),
            Bool(b) => print!("{}", b),
            Symbol(s, _) => print!("{}", s),
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

fn proc_proc() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let ObjectKind::Symbol(name, _) = ctx.pop_stack()?.kind else {
            return Err(error!(
                ctx.cur_object,
                "The object naming the procedure must be of type Symbol"
            ));
        };

        let body = ctx.pop_stack()?;
        if !matches!(body.kind, ObjectKind::List(_)) {
            return Err(error!(
                ctx.cur_object,
                "The object representing the body of the procedure must be of type List"
            ));
        }

        ctx.add_proc(&name, Proc::Aocla(body));

        Ok(())
    }
}

fn proc_if() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let else_branch = ctx
            .cur_proc_name
            .as_deref()
            .is_some_and(|s| s == "ifelse")
            .then_some(ctx.pop_stack()?);

        let if_branch = ctx.pop_stack()?;
        if !matches!(if_branch.kind, ObjectKind::List(_)) {
            return Err(error!(ctx.cur_object, "`if` branch must be of type List"));
        }

        let cond = ctx.pop_stack()?;
        if !matches!(cond.kind, ObjectKind::List(_)) {
            return Err(error!(
                ctx.cur_object,
                "`if` condition must be of type List, that push Bool value to stack"
            ));
        }

        ctx.eval(&cond)?;
        let ObjectKind::Bool(state) = ctx.pop_stack()?.kind else {
            return Err(error!(
                ctx.cur_object,
                "`if` condition must push Bool value to stack"
            ));
        };

        if state {
            ctx.eval(&if_branch)?;
        } else if let Some(o) = else_branch {
            if !matches!(o.kind, ObjectKind::List(_)) {
                return Err(error!(ctx.cur_object, "`else` branch must be of type List"));
            }
            ctx.eval(&o)?;
        }
        Ok(())
    }
}

fn proc_while() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let loop_body = ctx.pop_stack()?;
        if !matches!(loop_body.kind, ObjectKind::List(_)) {
            return Err(error!(ctx.cur_object, "`while` body must be of type List"));
        }

        let cond = ctx.pop_stack()?;
        if !matches!(cond.kind, ObjectKind::List(_)) {
            return Err(error!(
                ctx.cur_object,
                "`while` condition must be of type List, that push Bool value to stack"
            ));
        }

        loop {
            ctx.eval(&cond)?;
            let ObjectKind::Bool(state) = ctx.pop_stack()?.kind else {
                return Err(error!(
                    ctx.cur_object,
                    "`while` condition must push Bool value to stack"
                ));
            };
            if !state {
                break;
            }
            ctx.eval(&loop_body)?;
        }
        Ok(())
    }
}

fn proc_get() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let ObjectKind::Int(index) = ctx.pop_stack()?.kind else {
            return Err(error!(
                ctx.cur_object,
                "Sequences can be indexed only by object of type Int"
            ));
        };

        if index.is_negative() {
            return Err(error!(
                ctx.cur_object,
                "Only numbers that are >= 0 can be used as index for sequences"
            ));
        }

        let index = index as usize;
        let seq = ctx.pop_stack()?.kind;

        match seq {
            ObjectKind::List(s) | ObjectKind::Tuple(s, _) => ctx.stack.push(
                s.get(index)
                    .ok_or(error!(ctx.cur_object, "Out of sequence bounds"))?
                    .clone(),
            ),
            ObjectKind::Str(s) => ctx.stack.push(Object::from(ObjectKind::Str(format!(
                "{}",
                s.chars()
                    .nth(index)
                    .ok_or(error!(ctx.cur_object, "Out of string bounds"))?
            )))),
            _ => {
                return Err(error!(
                    ctx.cur_object,
                    "Only objects of type List, Tuple or Str can be indexed"
                ))
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
            if self.curr() != ';' {
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
                    ')' => ObjectKind::Tuple(data, is_quoted),
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
        while is_symbol(self.curr()) || self.curr().is_ascii_digit() {
            self.idx += 1;
        }

        let sym = self.src[start..self.idx].iter().collect();
        ObjectKind::Symbol(sym, is_quoted)
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
                c if is_symbol(c) => self.parse_symbol(),
                lb @ ('(' | '[') => self.parse_sequence(lb)?,
                c => {
                    return Err(error!(
                        self.line,
                        self.column,
                        format!("No object type starts like this: `{}`", c)
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
    let root_obj = parser.parse_object()?;

    let mut ctx = AoclaCtx::new()?;
    ctx.eval(&root_obj)?;

    Ok(())
}

fn repl() -> Result {
    let mut ctx = AoclaCtx::new()?;
    loop {
        print!("> ");
        io::stdout().flush().unwrap();

        let mut buf = String::new();
        io::stdin().read_line(&mut buf).unwrap();

        match buf.trim() {
            "quit" | "exit" | "leave" => break,
            code => {
                let mut parser = Parser::new(code);
                match parser.parse_object() {
                    Ok(root_obj) => {
                        if let Err(err) = ctx.eval(&root_obj) {
                            eprintln!("{}", err);
                        }
                    }
                    Err(err) => eprintln!("{}", err),
                }
            }
        }
    }
    Ok(())
}

type Result<T = ()> = std::result::Result<T, AoclaError>;

fn main() {
    let result = if let Some(filename) = env::args().nth(1) {
        eval_file(filename)
    } else {
        repl()
    };

    if let Err(err) = result {
        eprintln!("{}", err);
    }
}

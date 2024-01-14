#![allow(dead_code)]

use std::collections::HashMap;
use std::path::Path;

#[rustfmt::skip]
#[derive(Debug, Clone)]
enum ObjectKind<'a> {
    Int(isize),
    List(Vec<Object<'a>>),
    Tuple { data: Vec<Object<'a>>, is_quoted: bool },
    Str(&'a [u8]),
    Bool(bool),
    Symbol { data: &'a [u8], is_quoted: bool },
}

#[derive(Debug, Clone)]
struct Object<'a> {
    kind: ObjectKind<'a>,
    line: usize, // TODO: Use in error message
}

impl<'a> From<ObjectKind<'a>> for Object<'a> {
    fn from(kind: ObjectKind<'a>) -> Self {
        Self { kind, line: 0 }
    }
}

impl Object<'_> {
    fn value<T>(&self) -> Result<&T> {
        use std::any::type_name as tname;
        use std::mem::transmute as trans;

        use ObjectKind::*;

        macro_rules! err_if_neq {
            ($v:expr, $a:ty, $b:ty) => {{
                if tname::<$a>() != tname::<$b>() {
                    return Err("Type mismatch");
                }
                $v
            }};
        }

        Ok(unsafe {
            match &self.kind {
                Int(i) => err_if_neq!(trans(i), isize, T),
                List(v) => err_if_neq!(trans(v), Vec<Object<'_>>, T),
                Tuple { data, .. } => err_if_neq!(trans(data), Vec<Object<'_>>, T),
                Str(s) => err_if_neq!(trans(s), &[u8], T),
                Bool(b) => err_if_neq!(trans(b), bool, T),
                Symbol { data, .. } => err_if_neq!(trans(data), &[u8], T),
            }
        })
    }

    #[cfg(debug_assertions)]
    fn traverse(&self) {
        fn traverse(obj: &Object<'_>, indent: Option<usize>) {
            let indent = indent.unwrap_or(0);
            print!("{}", " ".repeat(indent));

            use std::str::from_utf8_unchecked;

            use ObjectKind::*;
            match &obj.kind {
                Int(i) => println!("Int: {}", i),
                List(v) => {
                    println!("List:");
                    for o in v {
                        traverse(o, Some(indent + 2));
                    }
                }
                Tuple { data, is_quoted } => {
                    println!("Tuple (is_quoted = {}):", is_quoted);
                    for o in data {
                        traverse(o, Some(indent + 2));
                    }
                }
                Str(s) => println!("Str: {}", unsafe { from_utf8_unchecked(s) }),
                Bool(b) => println!("Bool: {}", b),
                Symbol { data, is_quoted } => {
                    println!("Symbol (is_quoted = {}): {}", is_quoted, unsafe {
                        from_utf8_unchecked(data)
                    })
                }
            }
        }
        traverse(self, None);
    }
}

#[derive(Debug)]
enum Proc<'a> {
    Aocla(Object<'a>),
    Rust(fn(&mut AoclaCtx<'a>) -> Result),
}

type StackFrame<'a> = HashMap<&'a [u8], Object<'a>>;

#[derive(Debug, Default)]
struct AoclaCtx<'a> {
    stack: Vec<Object<'a>>,
    proc: HashMap<&'a [u8], Proc<'a>>,
    frame: StackFrame<'a>,
    cur_proc_name: Option<&'a [u8]>,
}

impl<'a> AoclaCtx<'a> {
    fn new() -> Result<Self> {
        let mut ctx = Self::default();
        ctx.load_library()?;
        Ok(ctx)
    }

    #[inline]
    fn pop_stack(&mut self) -> Result<Object<'a>> {
        self.stack.pop().ok_or("Out of stack")
    }

    fn basic_math(&self) -> fn(&mut Self) -> Result {
        |ctx| {
            let b = ctx.pop_stack()?;
            let a = ctx.pop_stack()?;

            let b = *b.value::<isize>()?;
            let a = *a.value::<isize>()?;

            ctx.stack.push(Object::from(ObjectKind::Int(
                match ctx.cur_proc_name.unwrap() {
                    b"+" => a + b,
                    b"-" => a - b,
                    b"*" => a * b,
                    b"/" => a / b,
                    _ => unreachable!(),
                },
            )));
            Ok(())
        }
    }

    fn load_library(&mut self) -> Result {
        self.proc.insert(b"+", Proc::Rust(self.basic_math()));
        self.proc.insert(b"-", Proc::Rust(self.basic_math()));
        self.proc.insert(b"*", Proc::Rust(self.basic_math()));
        self.proc.insert(b"/", Proc::Rust(self.basic_math()));
        Ok(())
    }

    fn call_proc(&mut self, data: &'a [u8], f: impl Fn(&mut Self) -> Result) -> Result<()> {
        let prev_proc_name = self.cur_proc_name;
        let prev_stack_frame = self.frame.clone();

        self.cur_proc_name = Some(data);

        // TODO: Implement `upeval` by not creating new frame
        self.frame = StackFrame::default();

        f(self)?;

        self.frame = prev_stack_frame;
        self.cur_proc_name = prev_proc_name;

        Ok(())
    }

    fn call_aocla_proc(&mut self, data: &'a [u8], obj: Object<'a>) -> Result<()> {
        self.call_proc(data, |ctx| ctx.eval(obj.clone()))
    }

    fn dequote_and_push(&mut self, obj: &Object<'a>) {
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

    fn eval(&mut self, obj: Object<'a>) -> Result {
        let ObjectKind::List(data) = obj.kind else {
            return Err("First object is not a List");
        };

        for obj in data {
            match &obj.kind {
                ObjectKind::Tuple { data, is_quoted } => {
                    if *is_quoted {
                        self.dequote_and_push(&obj);
                        return Ok(());
                    }

                    if self.stack.len() < data.len() {
                        return Err("Out of stack while capturing local");
                    }

                    for _ in 0..data.len() {
                        self.stack.pop();
                    }

                    for obj in data {
                        let ObjectKind::Symbol { data, .. } = obj.kind else {
                            return Err("Cannot capture non-symbol objects");
                        };
                        self.frame.insert(data, obj.clone());
                    }
                }
                ObjectKind::Symbol { data, is_quoted } => {
                    if *is_quoted {
                        self.dequote_and_push(&obj);
                        return Ok(());
                    }

                    if data[0] == b'$' {
                        let Some(local) = self.frame.get(data) else {
                            return Err("Ubound local variable");
                        };
                        self.stack.push(local.clone());
                    } else {
                        let Some(proc) = self.proc.get(data) else {
                            return Err("Symbol not bound to procedure");
                        };
                        match proc {
                            Proc::Rust(f) => self.call_proc(data, *f)?,
                            Proc::Aocla(o) => self.call_aocla_proc(data, o.clone())?,
                        }
                    }
                }
                _ => self.stack.push(obj),
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
struct Parser<'a> {
    src: &'a [u8],
    idx: usize,
    line: usize,
}

impl<'a> Parser<'a> {
    fn new(src: &'a [u8]) -> Self {
        Self {
            src,
            idx: 0,
            line: 1,
        }
    }

    #[inline]
    fn curr(&self) -> u8 {
        self.src[self.idx]
    }

    #[inline]
    fn next(&self) -> u8 {
        self.src[self.idx + 1]
    }

    fn consume_space(&mut self) {
        loop {
            while self.curr().is_ascii_whitespace() {
                if self.curr() == b'\n' {
                    self.line += 1;
                }
                self.idx += 1;
            }
            if self.curr() != b'/' || self.next() != b'/' {
                break;
            }
            while self.curr() != b'\n' {
                self.idx += 1;
            }
        }
    }

    #[inline]
    fn is_integer(&self) -> bool {
        (self.curr() == b'-' && self.next().is_ascii_digit()) || self.curr().is_ascii_digit()
    }

    fn parse_integer(&mut self) -> ObjectKind<'a> {
        let start = self.idx;
        while self.curr().is_ascii_digit() || self.curr() == b'-' {
            self.idx += 1;
        }
        let num = std::str::from_utf8(&self.src[start..self.idx])
            .unwrap()
            .parse()
            .unwrap();
        ObjectKind::Int(num)
    }

    #[inline]
    fn is_list(&self) -> bool {
        self.curr() == b'['
    }

    #[inline]
    fn is_tuple(&self) -> bool {
        self.curr() == b'('
    }

    #[inline]
    fn is_quote(&self) -> bool {
        self.curr() == b'\''
    }

    #[inline]
    fn is_quoted_tuple(&self) -> bool {
        self.is_quote() && self.next() == b'('
    }

    fn parse_sequence_until(&mut self, stop_bracket: u8) -> Result<ObjectKind<'a>> {
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
                    b']' => ObjectKind::List(data),
                    b')' => ObjectKind::Tuple { data, is_quoted },
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
        self.curr().is_ascii_alphabetic()
            || matches!(
                self.curr(),
                b'@' | b'$'
                    | b'+'
                    | b'-'
                    | b'*'
                    | b'/'
                    | b'='
                    | b'?'
                    | b'%'
                    | b'>'
                    | b'<'
                    | b'_'
                    | b'\''
            )
    }

    fn parse_symbol(&mut self) -> ObjectKind<'a> {
        let is_quoted = self.is_quote();
        if is_quoted {
            self.idx += 1;
        }

        let start = self.idx;
        while self.is_symbol() {
            self.idx += 1;
        }

        let data = &self.src[start..self.idx];
        ObjectKind::Symbol { data, is_quoted }
    }

    #[inline]
    fn is_boolean(&self) -> bool {
        self.curr() == b'#'
    }

    fn parse_boolean(&mut self) -> Result<ObjectKind<'a>> {
        let state = self.next();
        if state != b't' && state != b'f' {
            return Err("Booleans are either #t or #f");
        }
        self.idx += 2;
        Ok(ObjectKind::Bool(state == b't'))
    }

    #[inline]
    fn is_string(&self) -> bool {
        self.curr() == b'"'
    }

    fn parse_string(&mut self) -> Result<ObjectKind<'a>> {
        self.idx += 1;
        let start = self.idx;

        while self.curr() != b'"' {
            self.idx += 1;
        }

        self.idx += 1;
        Ok(ObjectKind::Str(&self.src[start..self.idx]))
    }

    fn parse_object(&mut self) -> Result<Object<'a>> {
        self.consume_space();
        Ok(Object {
            line: self.line,
            kind: if self.is_integer() {
                self.parse_integer()
            } else if self.is_list() {
                self.parse_sequence_until(b']')?
            } else if self.is_tuple() || self.is_quoted_tuple() {
                self.parse_sequence_until(b')')?
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
    let buf = std::fs::read_to_string(filename).map_err(|_| "Failed to read file")?;
    let src = format!("[{}]", buf);

    let mut parser = Parser::new(src.as_bytes());
    let obj = parser.parse_object()?;
    obj.traverse();

    let mut ctx = AoclaCtx::new()?;
    ctx.eval(obj)?;

    dbg!(ctx.stack);

    Ok(())
}

type Result<T = ()> = std::result::Result<T, &'static str>;

fn main() -> Result {
    eval_file("examples/123.aocla")
}

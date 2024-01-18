#![allow(dead_code)]

use std::cmp::Ordering;
use std::collections::HashMap;
use std::io::Write;
use std::path::Path;
use std::{env, error, fmt, fs, io, str};

mod parser;

use parser::Object;

#[derive(Debug)]
enum Proc {
    Aocla(Object),
    Rust(fn(&mut AoclaCtx) -> Result),
}

#[derive(Debug)]
struct AoclaError {
    message: String,
}

impl fmt::Display for AoclaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Error occured: {}", self.message)
    }
}

impl error::Error for AoclaError {}

#[macro_export]
macro_rules! error {
    ($message:expr) => {
        AoclaError {
            message: $message.to_owned(),
        }
    };
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
        self.stack.pop().ok_or(error!("Out of stack"))
    }

    fn peek_stack(&self) -> Result<&Object> {
        self.stack.last().ok_or(error!("Out of stack"))
    }

    fn cur_proc_name(&self) -> Result<&str> {
        self.cur_proc_name
            .as_deref()
            .ok_or(error!("Not inside procedure"))
    }

    fn add_proc_string(&mut self, proc_name: &str, proc_body: &str) -> Result {
        let proc_body = parser::wrap(proc_body);
        let proc = parser::parse_root(&proc_body)
            .map_err(|err| error!(err.to_string()))?
            .1;
        self.add_proc(proc_name, Proc::Aocla(proc));
        Ok(())
    }

    fn add_proc(&mut self, name: &str, proc: Proc) {
        self.proc.insert(name.to_owned(), proc);
    }

    fn add_rust_proc(&mut self, name: &str, f: fn(&mut Self) -> Result) {
        self.add_proc(name, Proc::Rust(f));
    }

    fn load_library(&mut self) -> Result {
        self.add_rust_proc("+", arithmetic_proc());
        self.add_rust_proc("-", arithmetic_proc());
        self.add_rust_proc("*", arithmetic_proc());
        self.add_rust_proc("/", arithmetic_proc());
        self.add_rust_proc("=", compare_proc());
        self.add_rust_proc("<>", compare_proc());
        self.add_rust_proc(">=", compare_proc());
        self.add_rust_proc("<=", compare_proc());
        self.add_rust_proc(">", compare_proc());
        self.add_rust_proc("<", compare_proc());
        self.add_rust_proc("and", boolean_proc());
        self.add_rust_proc("or", boolean_proc());
        self.add_rust_proc("not", boolean_proc());
        self.add_rust_proc("print", print_proc());
        self.add_rust_proc("println", print_proc());
        self.add_rust_proc("proc", proc_proc());
        self.add_rust_proc("if", proc_if());
        self.add_rust_proc("ifelse", proc_if());
        self.add_rust_proc("while", proc_while());
        self.add_rust_proc("get", proc_get());
        self.add_rust_proc("len", proc_len());
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
        match notq {
            Object::Tuple(_, ref mut is_quoted) | Object::Sym(_, ref mut is_quoted) => {
                *is_quoted = false;
            }
            _ => unreachable!(),
        }
        self.stack.push(notq);
    }

    fn eval_tuple(&mut self, tuple: &[Object]) -> Result {
        for obj in tuple.iter().rev() {
            let Object::Sym(sym, _) = &obj else {
                return Err(error!("Only objects of type Symbol can be captured"));
            };
            let obj = self.pop_stack()?;
            self.frame.insert(sym.clone(), obj);
        }
        Ok(())
    }

    fn eval_symbol(&mut self, sym: &String) -> Result {
        if let Some(sym) = sym.strip_prefix('$') {
            let local = self
                .frame
                .get(sym)
                .ok_or(error!("Unbound local variable"))?;
            self.stack.push(local.clone());
        } else {
            let proc = self.proc.get(sym).ok_or(error!("Unbound procedure"))?;
            match proc {
                Proc::Rust(f) => self.call_proc(sym.clone(), *f)?,
                Proc::Aocla(o) => self.call_aocla_proc(sym.clone(), o.clone())?,
            }
        }
        Ok(())
    }

    fn eval(&mut self, root_obj: &Object) -> Result {
        let Object::List(root_obj_list) = &root_obj else {
            return Err(error!("Root object must be of type List"));
        };

        for obj in root_obj_list {
            self.cur_object = Some(obj.clone());
            match &obj {
                Object::Tuple(tuple, is_quoted) => {
                    if *is_quoted {
                        self.dequote_and_push(obj.clone());
                    } else {
                        if self.stack.len() < tuple.len() {
                            return Err(error!("Out of stack while capturing local variable"));
                        }
                        self.eval_tuple(tuple)?;
                    }
                }
                Object::Sym(sym, is_quoted) => {
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

        let (Object::Int(b), Object::Int(a)) = (b_obj, a_obj) else {
            return Err(error!("Both objects must be of type Int"));
        };

        ctx.stack.push(Object::Int(match ctx.cur_proc_name()? {
            "+" => a + b,
            "-" => a - b,
            "*" => a * b,
            "/" => a / b,
            _ => unreachable!(),
        }));
        Ok(())
    }
}

fn compare_proc() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let b_obj = ctx.pop_stack()?;
        let a_obj = ctx.pop_stack()?;

        use Object::*;
        let ord = match (&a_obj, &b_obj) {
            (Int(a), Int(b)) => a.cmp(b),
            (Bool(a), Bool(b)) => a.cmp(b),
            (Str(a), Str(b))
            | (Sym(a, _), Sym(b, _))
            | (Str(a), Sym(b, _))
            | (Sym(b, _), Str(a)) => a.cmp(b),
            (List(a), List(b))
            | (Tuple(a, _), Tuple(b, _))
            | (List(a), Tuple(b, _))
            | (Tuple(b, _), List(a)) => a.len().cmp(&b.len()),
            _ => {
                ctx.stack.extend_from_slice(&[b_obj, a_obj]);
                return Err(error!("Unable to compare two objects"));
            }
        };

        ctx.stack.push(Object::Bool(match ctx.cur_proc_name()? {
            "=" => ord == Ordering::Equal,
            "<>" => ord != Ordering::Equal,
            ">=" => ord == Ordering::Equal || ord == Ordering::Greater,
            "<=" => ord == Ordering::Equal || ord == Ordering::Less,
            ">" => ord == Ordering::Greater,
            "<" => ord == Ordering::Less,
            _ => unreachable!(),
        }));
        Ok(())
    }
}

fn boolean_proc() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let is_unary_op = ctx.cur_proc_name().is_ok_and(|s| s == "not");

        if is_unary_op {
            if let Object::Bool(b) = ctx.pop_stack()? {
                ctx.stack.push(Object::Bool(!b));
            } else {
                return Err(error!("Expected object of type Bool"));
            }
        } else {
            let rigth_obj = ctx.pop_stack()?;
            let left_obj = ctx.pop_stack()?;
            let (Object::Bool(left), Object::Bool(right)) = (left_obj, rigth_obj) else {
                return Err(error!("Both objects must be of type Bool"));
            };
            ctx.stack.push(Object::Bool(match ctx.cur_proc_name()? {
                "and" => left && right,
                "or" => left || right,
                _ => unreachable!(),
            }));
        }
        Ok(())
    }
}

fn print_proc() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        use Object::*;
        match ctx.peek_stack()? {
            Int(i) => print!("{}", i),
            List(v) => print!("{:?}", v), // TODO: Pretty print
            Tuple(t, _) => print!("{:?}", t),
            Str(s) => print!("{}", s),
            Bool(b) => print!("{}", b),
            Sym(s, _) => print!("{}", s),
        }

        let should_print_nl = ctx.cur_proc_name().is_ok_and(|s| s == "println");

        if should_print_nl {
            println!();
        } else {
            io::stdout()
                .flush()
                .map_err(|err| error!(err.to_string()))?;
        }
        Ok(())
    }
}

fn proc_proc() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let Object::Sym(proc_name, _) = ctx.pop_stack()? else {
            return Err(error!(
                "The object naming the procedure must be of type Symbol"
            ));
        };

        let proc_body = ctx.pop_stack()?;
        if !matches!(proc_body, Object::List(_)) {
            return Err(error!(
                "The object representing the body of the procedure must be of type List"
            ));
        }

        ctx.add_proc(&proc_name, Proc::Aocla(proc_body));

        Ok(())
    }
}

fn proc_if() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let else_branch = if ctx.cur_proc_name().is_ok_and(|s| s == "ifelse") {
            Some(ctx.pop_stack()?)
        } else {
            None
        };

        let if_branch = ctx.pop_stack()?;
        if !matches!(if_branch, Object::List(_)) {
            return Err(error!("`if` branch must be of type List"));
        }

        let cond = ctx.pop_stack()?;
        if !matches!(cond, Object::List(_)) {
            return Err(error!(
                "`if` condition must be of type List, that push Bool value to stack"
            ));
        }

        ctx.eval(&cond)?;
        let Object::Bool(state) = ctx.pop_stack()? else {
            return Err(error!("`if` condition must push Bool value to stack"));
        };

        if state {
            ctx.eval(&if_branch)?;
        } else if let Some(o) = else_branch {
            if !matches!(o, Object::List(_)) {
                return Err(error!("`else` branch must be of type List"));
            }
            ctx.eval(&o)?;
        }
        Ok(())
    }
}

fn proc_while() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let loop_body = ctx.pop_stack()?;
        if !matches!(loop_body, Object::List(_)) {
            return Err(error!("`while` body must be of type List"));
        }

        let loop_cond = ctx.pop_stack()?;
        if !matches!(loop_cond, Object::List(_)) {
            return Err(error!(
                "`while` condition must be of type List, that push Bool value to stack"
            ));
        }

        loop {
            ctx.eval(&loop_cond)?;
            let Object::Bool(state) = ctx.pop_stack()? else {
                return Err(error!("`while` condition must push Bool value to stack"));
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
        let Object::Int(index) = ctx.pop_stack()? else {
            return Err(error!(
                "Sequences can be indexed only by object of type Int"
            ));
        };

        if index.is_negative() {
            return Err(error!(
                "Only numbers that are >= 0 can be used as index for sequences"
            ));
        }

        let index = index as usize;

        match ctx.pop_stack()? {
            Object::List(s) | Object::Tuple(s, _) => ctx.stack.push(
                s.get(index)
                    .ok_or(error!("Out of sequence bounds"))?
                    .clone(),
            ),
            Object::Str(s) => ctx.stack.push(Object::Str(format!(
                "{}",
                s.chars().nth(index).ok_or(error!("Out of string bounds"))?
            ))),
            _ => {
                return Err(error!(
                    "Only objects of type List, Tuple or Str can be indexed"
                ))
            }
        }
        Ok(())
    }
}

fn proc_len() -> fn(&mut AoclaCtx) -> Result {
    |ctx| {
        let seq = ctx.pop_stack()?;
        match seq {
            Object::List(s) | Object::Tuple(s, _) => ctx.stack.push(Object::Int(s.len() as _)),
            Object::Str(s) => ctx.stack.push(Object::Int(s.len() as _)),
            _ => {
                return Err(error!(
                    "Only objects of type List, Tuple or Str can have length"
                ))
            }
        }
        Ok(())
    }
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

    let buf = parser::wrap(&buf);
    let root_obj = parser::parse_root(&buf)
        .map_err(|err| error!(err.to_string()))?
        .1;

    let mut ctx = AoclaCtx::new()?;
    ctx.eval(&root_obj)?;

    Ok(())
}

fn repl() -> Result {
    let mut ctx = AoclaCtx::new()?;
    loop {
        print!("> ");
        io::stdout()
            .flush()
            .map_err(|err| error!(err.to_string()))?;

        let mut buf = String::new();
        io::stdin()
            .read_line(&mut buf)
            .map_err(|err| error!(err.to_string()))?;

        match buf.trim() {
            "quit" => break,
            code => {
                let code = parser::wrap(code);
                match parser::parse_root(&code) {
                    Ok((_, root_obj)) => {
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

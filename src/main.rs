use std::cmp::Ordering;
use std::collections::HashMap;
use std::io::Write;
use std::path::Path;
use std::{env, fs, io, str};

mod error;
mod parser;
mod stack;

use error::*;
use parser::Object;
use stack::Stack;

#[rustfmt::skip]
#[derive(Debug, Clone)]
enum Proc<F: Fn(&mut AoclaCtx) -> Result =
    fn(&mut AoclaCtx) -> Result>
{
    Aocla(Object),
    Rust(F),
}

#[derive(Default)]
struct AoclaCtx {
    stack: Stack,
    procs: HashMap<String, Proc>,
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

    fn cur_proc_name(&self) -> Result<&str> {
        self.cur_proc_name
            .as_deref()
            .ok_or(error!("Not inside procedure"))
    }

    fn add_string_proc(&mut self, proc_name: &str, proc_body: &str) -> Result {
        let proc = parser::parse_root(proc_body).map_err(|err| error!(err))?;
        self.add_proc(proc_name, Proc::Aocla(proc));
        Ok(())
    }

    fn add_rust_proc(&mut self, name: &str, f: fn(&mut Self) -> Result) {
        self.add_proc(name, Proc::Rust(f));
    }

    fn add_proc(&mut self, name: &str, proc: Proc) {
        self.procs.insert(name.to_owned(), proc);
    }

    fn load_library(&mut self) -> Result {
        self.add_rust_proc("+", arithmetic_proc);
        self.add_rust_proc("-", arithmetic_proc);
        self.add_rust_proc("*", arithmetic_proc);
        self.add_rust_proc("/", arithmetic_proc);
        self.add_rust_proc("=", compare_proc);
        self.add_rust_proc("<>", compare_proc);
        self.add_rust_proc(">=", compare_proc);
        self.add_rust_proc("<=", compare_proc);
        self.add_rust_proc(">", compare_proc);
        self.add_rust_proc("<", compare_proc);
        self.add_rust_proc("and", boolean_proc);
        self.add_rust_proc("or", boolean_proc);
        self.add_rust_proc("not", boolean_proc);
        self.add_rust_proc("print", print_proc);
        self.add_rust_proc("println", print_proc);
        self.add_rust_proc("proc", proc_proc);
        self.add_rust_proc("if", proc_if);
        self.add_rust_proc("ifelse", proc_if);
        self.add_rust_proc("while", proc_while);
        self.add_rust_proc("get", proc_get);
        self.add_rust_proc("len", proc_len);
        self.add_string_proc("dup", "(x) $x $x")?;
        self.add_string_proc("swap", "(x y) $y $x")?;
        self.add_string_proc("drop", "(_)")?;
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
            let obj = self.stack.pop()?;
            self.frame.insert(sym.clone(), obj);
        }
        Ok(())
    }

    fn eval_symbol(&mut self, sym: &String) -> Result {
        if let Some(sym) = sym.strip_prefix('$') {
            let local = self
                .frame
                .get(sym)
                .ok_or(error!(format!("Unbound local variable: '{sym}'")))?;
            self.stack.push(local.clone());
        } else {
            let proc = match self.procs.get(sym) {
                Some(proc) => proc.clone(),
                None => match self.frame.get(sym) {
                    Some(local @ Object::Sym(_, _)) => {
                        Proc::Aocla(Object::List(vec![local.clone()]))
                    }
                    Some(_) | None => return Err(error!(format!("Unbound procedure: '{sym}'"))),
                },
            };
            match proc {
                Proc::Rust(f) => self.call_proc(sym.clone(), f)?,
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

fn arithmetic_proc(ctx: &mut AoclaCtx) -> Result {
    let b_obj = ctx.stack.pop()?;
    let a_obj = ctx.stack.pop()?;

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

fn compare_proc(ctx: &mut AoclaCtx) -> Result {
    let b_obj = ctx.stack.pop()?;
    let a_obj = ctx.stack.pop()?;

    use Object::*;
    let ord = match (&a_obj, &b_obj) {
        (Int(a), Int(b)) => a.cmp(b),
        (Bool(a), Bool(b)) => a.cmp(b),
        (Str(a), Str(b)) | (Sym(a, _), Sym(b, _)) | (Str(a), Sym(b, _)) | (Sym(b, _), Str(a)) => {
            a.cmp(b)
        }
        (List(a), List(b))
        | (Tuple(a, _), Tuple(b, _))
        | (List(a), Tuple(b, _))
        | (Tuple(b, _), List(a)) => a.len().cmp(&b.len()),
        _ => {
            ctx.stack.extend(&[b_obj, a_obj]);
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

fn boolean_proc(ctx: &mut AoclaCtx) -> Result {
    let is_unary_op = ctx.cur_proc_name().is_ok_and(|s| s == "not");

    if is_unary_op {
        if let Object::Bool(b) = ctx.stack.pop()? {
            ctx.stack.push(Object::Bool(!b));
        } else {
            return Err(error!("Expected object of type Bool"));
        }
    } else {
        let rigth_obj = ctx.stack.pop()?;
        let left_obj = ctx.stack.pop()?;
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

fn print_proc(ctx: &mut AoclaCtx) -> Result {
    use Object::*;
    match ctx.stack.peek()? {
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

fn proc_proc(ctx: &mut AoclaCtx) -> Result {
    let Object::Sym(proc_name, _) = ctx.stack.pop()? else {
        return Err(error!(
            "The object naming the procedure must be of type Symbol"
        ));
    };

    let proc_body = ctx.stack.pop()?;
    if !matches!(proc_body, Object::List(_)) {
        return Err(error!(
            "The object representing the body of the procedure must be of type List"
        ));
    }

    ctx.add_proc(&proc_name, Proc::Aocla(proc_body));

    Ok(())
}

fn proc_if(ctx: &mut AoclaCtx) -> Result {
    let else_branch = if ctx.cur_proc_name().is_ok_and(|s| s == "ifelse") {
        Some(ctx.stack.pop()?)
    } else {
        None
    };

    let if_branch = ctx.stack.pop()?;
    if !matches!(if_branch, Object::List(_)) {
        return Err(error!("`if` branch must be of type List"));
    }

    let cond = ctx.stack.pop()?;
    if !matches!(cond, Object::List(_)) {
        return Err(error!(
            "`if` condition must be of type List, that push Bool value to stack"
        ));
    }

    ctx.eval(&cond)?;
    let Object::Bool(state) = ctx.stack.pop()? else {
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

fn proc_while(ctx: &mut AoclaCtx) -> Result {
    let loop_body = ctx.stack.pop()?;
    if !matches!(loop_body, Object::List(_)) {
        return Err(error!("`while` body must be of type List"));
    }

    let loop_cond = ctx.stack.pop()?;
    if !matches!(loop_cond, Object::List(_)) {
        return Err(error!(
            "`while` condition must be of type List, that push Bool value to stack"
        ));
    }

    loop {
        ctx.eval(&loop_cond)?;
        let Object::Bool(state) = ctx.stack.pop()? else {
            return Err(error!("`while` condition must push Bool value to stack"));
        };
        if !state {
            break;
        }
        ctx.eval(&loop_body)?;
    }
    Ok(())
}

fn proc_get(ctx: &mut AoclaCtx) -> Result {
    let Object::Int(index) = ctx.stack.pop()? else {
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

    match ctx.stack.pop()? {
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

fn proc_len(ctx: &mut AoclaCtx) -> Result {
    let seq = ctx.stack.pop()?;
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

    let root_obj = parser::parse_root(&buf).map_err(|err| error!(err))?;

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
            code => match parser::parse_root(code) {
                Ok(root_obj) => {
                    if let Err(err) = ctx.eval(&root_obj) {
                        eprintln!("{}", err);
                    }
                }
                Err(err) => eprintln!("{}", err),
            },
        }
    }
    Ok(())
}

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

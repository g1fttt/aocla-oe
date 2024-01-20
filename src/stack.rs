use crate::error::*;
use crate::parser::Object;

#[derive(Debug, Default)]
pub struct Stack(Vec<Object>);

impl Stack {
    pub fn push(&mut self, o: Object) {
        self.0.push(o);
    }

    pub fn extend(&mut self, objs: &[Object]) {
        self.0.extend_from_slice(objs);
    }

    pub fn pop(&mut self) -> Result<Object> {
        check_boundaries(self.0.pop())
    }

    pub fn peek(&self) -> Result<&Object> {
        check_boundaries(self.0.last())
    }

    pub fn peek_mut(&mut self) -> Result<&mut Object> {
        check_boundaries(self.0.last_mut())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

fn check_boundaries<T>(x: Option<T>) -> Result<T> {
    x.ok_or(error!("Out of stack"))
}

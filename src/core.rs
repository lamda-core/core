use std::rc::Rc;

// High-order VM: https://github.com/Kindelia/HVM
// Closure calculus: https://dl.acm.org/doi/pdf/10.1145/3294032.3294085

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
  Nil,                     // Empty environment       _
  Int(i64),                // Integer value           42
  Ctr(usize),              // Constructor index       #0
  Var(usize),              // DeBruijn variable       %0
  App(Rc<Expr>, Rc<Expr>), // Application             a b
  Lam(Rc<Expr>, Rc<Expr>), // Lamda closure           \env body
  Def(Rc<Expr>, Rc<Expr>), // Environment definition  {a, b}
  Jmp(Rc<Vec<Rc<Expr>>>),  // Jump table              [a, b]
  Op2(BinaryOp),           // Binary operator         +
}
use Expr::*;

#[derive(Clone, Debug, PartialEq)]
pub enum BinaryOp {
  Add,
  Sub,
  Mul,
}
use BinaryOp::*;

fn nil() -> Rc<Expr> {
  Rc::new(Nil)
}
fn ctr(i: usize) -> Rc<Expr> {
  Rc::new(Ctr(i))
}
fn var(i: usize) -> Rc<Expr> {
  Rc::new(Var(i))
}
fn int(i: i64) -> Rc<Expr> {
  Rc::new(Int(i))
}
fn lam(env: Rc<Expr>, body: Rc<Expr>) -> Rc<Expr> {
  Rc::new(Lam(env, body))
}
fn def(a: Rc<Expr>, b: Rc<Expr>) -> Rc<Expr> {
  Rc::new(Def(a, b))
}
fn app(a: Rc<Expr>, b: Rc<Expr>) -> Rc<Expr> {
  Rc::new(App(a, b))
}
fn jmp(vec: Rc<Vec<Rc<Expr>>>) -> Rc<Expr> {
  Rc::new(Jmp(vec))
}
macro_rules! jmp {
  () => {
    Rc::new(Jmp(Rc::new(vec![])))
  };
  ($($x:expr),+ $(,)?) => {
    Rc::new(Jmp(Rc::new(vec![$($x),+])))
  };
}
fn add(a: Rc<Expr>, b: Rc<Expr>) -> Rc<Expr> {
  app(app(Rc::new(Op2(Add)), a), b)
}
fn sub(a: Rc<Expr>, b: Rc<Expr>) -> Rc<Expr> {
  app(app(Rc::new(Op2(Sub)), a), b)
}
fn mul(a: Rc<Expr>, b: Rc<Expr>) -> Rc<Expr> {
  app(app(Rc::new(Op2(Mul)), a), b)
}

fn reduce(expr: Rc<Expr>) -> Rc<Expr> {
  match expr.as_ref() {
    App(fun, arg) => {
      let fun = reduce(fun.clone());
      let arg = reduce(arg.clone());
      match (fun.as_ref(), arg.as_ref()) {
        (Nil, _) => reduce(arg),
        (Var(_), _) => app(fun, arg),
        (App(op, a), _) => match (op.as_ref(), a.as_ref(), arg.as_ref()) {
          (Op2(Add), Int(a), Int(b)) => int(a + b),
          (Op2(Sub), Int(a), Int(b)) => int(a - b),
          (Op2(Mul), Int(a), Int(b)) => int(a * b),
          _ => app(fun, arg),
        },
        (Lam(env, body), _) => reduce(app(def(arg, env.clone()), body.clone())),
        (Def(x, _), Var(0)) => reduce(x.clone()),
        (Def(_, env), Var(i)) => reduce(app(env.clone(), var(i - 1))),
        (Def(_, _), Lam(env, body)) => lam(app(fun, env.clone()), body.clone()),
        (Def(_, _), Def(x, env)) => def(app(fun.clone(), x.clone()), app(fun, env.clone())),
        (Def(_, _), App(a, b)) => reduce(app(app(fun.clone(), a.clone()), app(fun, b.clone()))),
        (Def(_, _), _) => arg,
        (Jmp(branches), Ctr(i)) => reduce(branches[*i].clone()),
        _ => expr,
      }
    }
    _ => expr,
  }
}

impl Expr {
  fn show(&self) -> String {
    match self {
      Nil => String::from("_"),
      Int(i) => i.to_string(),
      Ctr(i) => format!("#{i}"),
      Var(i) => format!("%{i}"),
      App(fun, arg) => format!("({} {})", fun.show(), arg.show()),
      Lam(env, body) => format!("(\\{} {})", env.show(), body.show()),
      Def(x, env) => format!("{{{} {}}}", x.show(), env.show()),
      Jmp(branches) => format!(
        "[{}]",
        branches
          .iter()
          .map(|br| br.show())
          .collect::<Vec<String>>()
          .join(", ")
      ),
      Op2(Add) => String::from("+"),
      Op2(Sub) => String::from("-"),
      Op2(Mul) => String::from("*"),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_reduce() {
    assert_eq!(reduce(app(nil(), int(1))), int(1));
    assert_eq!(reduce(app(int(1), int(2))), app(int(1), int(2)));
    assert_eq!(reduce(app(var(0), int(1))), app(var(0), int(1)));
    assert_eq!(reduce(app(var(1), int(1))), app(var(1), int(1)));
    assert_eq!(
      reduce(app(app(int(1), int(2)), int(3))),
      app(app(int(1), int(2)), int(3))
    );
    assert_eq!(reduce(app(lam(var(0), int(2)), int(1))), int(2));

    let env = def(int(1), def(int(2), nil()));
    assert_eq!(reduce(app(env.clone(), nil())), nil());
    assert_eq!(reduce(app(env.clone(), int(3))), int(3));
    assert_eq!(reduce(app(env.clone(), var(0))), int(1));
    assert_eq!(reduce(app(env.clone(), var(1))), int(2));
    assert_eq!(reduce(app(env.clone(), var(2))), var(0));
    assert_eq!(
      reduce(app(env.clone(), lam(nil(), int(3)))),
      lam(app(env.clone(), nil()), int(3))
    );
    assert_eq!(
      reduce(app(env.clone(), app(int(1), int(2)))),
      app(app(env.clone(), int(1)), app(env.clone(), int(2)))
    );
    let env2 = def(int(3), def(int(4), nil()));
    assert_eq!(
      reduce(app(env.clone(), env2.clone())),
      def(
        app(env.clone(), int(3)),
        app(env.clone(), def(int(4), nil()))
      )
    );

    assert_eq!(reduce(app(jmp![int(1), int(2)], ctr(0))), int(1));
    assert_eq!(reduce(app(jmp![int(1), int(2)], ctr(1))), int(2));

    assert_eq!(reduce(add(int(1), int(2))), int(3));
    assert_eq!(reduce(sub(int(1), int(2))), int(-1));
    assert_eq!(reduce(mul(int(1), int(2))), int(2));
  }

  #[test]
  fn test_show() {
    assert_eq!(nil().show(), "_");
    assert_eq!(int(1).show(), "1");
    assert_eq!(ctr(0).show(), "#0");
    assert_eq!(var(0).show(), "%0");
    assert_eq!(app(nil(), int(1)).show(), "(_ 1)");
    assert_eq!(lam(nil(), int(1)).show(), "(\\_ 1)");
    assert_eq!(def(nil(), int(1)).show(), "{_ 1}");
    assert_eq!(jmp![].show(), "[]");
    assert_eq!(jmp![int(1)].show(), "[1]");
    assert_eq!(jmp![int(1), int(2)].show(), "[1, 2]");
    assert_eq!(jmp![int(1), int(2), int(3)].show(), "[1, 2, 3]");
  }

  #[test]
  fn test_factorial() {
    // f 0 = 1
    // f n = n * f (n - 1)
  }
}

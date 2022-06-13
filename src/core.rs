use std::rc::Rc;

// High-order VM: https://github.com/Kindelia/HVM
// Closure calculus: https://dl.acm.org/doi/pdf/10.1145/3294032.3294085
//      https://blog.chewxy.com/wp-content/uploads/personal/dissertation31482.pdf

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
  Nil,                              // Empty expression
  Int(i64),                         // Integer value           42
  Ctr(usize),                       // Constructor index       #0
  Var(usize),                       // DeBruijn variable       %0
  Def(Rc<Expr>, Rc<Expr>),          // Definition              {a, b}
  App(Rc<Expr>, Rc<Expr>),          // Application             a b
  Lam(Rc<Expr>, Rc<Expr>),          // Lamda closure           \a. b
  Jmp(Rc<Expr>, Rc<Vec<Rc<Expr>>>), // Lamda closure           #a. [b1 | b2 | ..]
  Op2(BinaryOp),                    // Binary operator         +
  Fix,                              // Fixed point recursion   @
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
fn def(a: Rc<Expr>, b: Rc<Expr>) -> Rc<Expr> {
  Rc::new(Def(a, b))
}
fn app(a: Rc<Expr>, b: Rc<Expr>) -> Rc<Expr> {
  Rc::new(App(a, b))
}
fn lam(env: Rc<Expr>, body: Rc<Expr>) -> Rc<Expr> {
  Rc::new(Lam(env, body))
}
fn jmp(env: Rc<Expr>, cases: Rc<Vec<Rc<Expr>>>) -> Rc<Expr> {
  Rc::new(Jmp(env, cases))
}
macro_rules! jmp {
  ($env: expr, $cases: expr) => {
    Rc::new(Jmp($env, Rc::new($cases.to_vec())))
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
fn fix(a: Rc<Expr>) -> Rc<Expr> {
  app(Rc::new(Fix), a)
}

impl Expr {
  fn show(&self) -> String {
    match self {
      Nil => String::from(""),
      Int(i) => i.to_string(),
      Ctr(i) => format!("#{i}"),
      Var(i) => format!("%{i}"),
      Def(a, b) => match b.as_ref() {
        Nil => format!("{{{}}}", a.show()),
        _ => format!("{{{}, {}}}", a.show(), b.show()),
      },
      App(a, b) => format!("({} {})", a.show(), b.show()),
      Lam(a, b) => format!("\\{}. {}", a.show(), b.show()),
      Jmp(a, b) => format!(
        "#{}. [{}]",
        a.show(),
        b.iter()
          .map(|br| br.show())
          .collect::<Vec<String>>()
          .join(" | ")
      ),
      Fix => String::from("@"),
      Op2(Add) => String::from("+"),
      Op2(Sub) => String::from("-"),
      Op2(Mul) => String::from("*"),
    }
  }
}

fn reduce(expr: Rc<Expr>) -> Rc<Expr> {
  match expr.as_ref() {
    App(a, b) => {
      let a = reduce(a.clone());
      let b = reduce(b.clone());
      match (a.as_ref(), b.as_ref()) {
        (Nil, _) => reduce(b),
        (Var(_), _) => app(a, b),
        (Def(a1, _), Var(0)) => reduce(a1.clone()),
        (Def(_, a2), Var(i)) => reduce(app(a2.clone(), var(i - 1))),
        (Def(_, _), Lam(b1, b2)) => lam(app(a, b1.clone()), b2.clone()),
        (Def(_, _), Def(b1, b2)) => def(app(a.clone(), b1.clone()), app(a, b2.clone())),
        (Def(_, _), App(b1, b2)) => reduce(app(
          reduce(app(a.clone(), b1.clone())),
          reduce(app(a.clone(), b2.clone())),
        )),
        (Def(_, _), Jmp(b1, b2)) => jmp(app(a, b1.clone()), b2.clone()),
        (Def(_, _), _) => b,
        (App(op, i), j) => match (op.as_ref(), i.as_ref(), j) {
          (Op2(Add), Int(i), Int(j)) => int(i + j),
          (Op2(Sub), Int(i), Int(j)) => int(i - j),
          (Op2(Mul), Int(i), Int(j)) => int(i * j),
          _ => app(a, b),
        },
        (Lam(a1, a2), _) => reduce(app(def(b, a1.clone()), a2.clone())),
        (Jmp(a1, a2), Ctr(i)) => reduce(app(a1.clone(), a2[*i].clone())),
        (Fix, Lam(b1, b2)) => reduce(app(def(fix(b.clone()), b1.clone()), b2.clone())),
        _ => expr,
      }
    }
    _ => expr,
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_show() {
    assert_eq!(nil().show(), "");
    assert_eq!(int(1).show(), "1");
    assert_eq!(ctr(0).show(), "#0");
    assert_eq!(var(0).show(), "%0");
    assert_eq!(def(int(1), nil()).show(), "{1}");
    assert_eq!(def(int(1), def(int(2), nil())).show(), "{1, {2}}");
    assert_eq!(app(ctr(0), int(1)).show(), "(#0 1)");
    assert_eq!(lam(nil(), int(1)).show(), "\\. 1");
    assert_eq!(lam(def(int(1), nil()), int(2)).show(), "\\{1}. 2");
    assert_eq!(jmp!(nil(), []).show(), "#. []");
    assert_eq!(jmp!(nil(), [int(1)]).show(), "#. [1]");
    assert_eq!(jmp!(nil(), [int(1), int(2)]).show(), "#. [1 | 2]");
    assert_eq!(jmp!(def(int(1), nil()), []).show(), "#{1}. []");
  }

  // TODO: Break up into individual rules.
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
      app(int(1), int(2))
    );
    let env2 = def(int(3), def(int(4), nil()));
    assert_eq!(
      reduce(app(env.clone(), env2.clone())),
      def(
        app(env.clone(), int(3)),
        app(env.clone(), def(int(4), nil()))
      )
    );

    assert_eq!(reduce(app(jmp!(nil(), [int(1), int(2)]), ctr(0))), int(1));
    assert_eq!(reduce(app(jmp!(nil(), [int(1), int(2)]), ctr(1))), int(2));

    assert_eq!(reduce(add(int(1), int(2))), int(3));
    assert_eq!(reduce(sub(int(1), int(2))), int(-1));
    assert_eq!(reduce(mul(int(1), int(2))), int(2));

    // fix f = f (fix f)
    // @ = fix

    // @ (λf. 1)
    // -------------
    // {f = @ (λf. 1)} 1
    // 1
    assert_eq!(reduce(fix(lam(nil(), int(1)))), int(1));

    // @ (λf. λ{f=f}x. x)
    // --------
    // {f = @ (λf. λ{f=f}x. x)} (λ{f=f}x. x)
    // λ{f = @ (λf. λ{f=f}x. x), f=f}x. x
    let f = lam(nil(), lam(def(var(0), nil()), var(0)));
    assert_eq!(
      reduce(fix(f.clone())),
      lam(app(def(fix(f.clone()), nil()), def(var(0), nil())), var(0))
    );

    // @ (λf. λ{f=f}x. x) 1
    // @ (λ. λ{%0}x. x) 1
    // --------
    // {f = @ (λf. λ{f=f}x. x)} (λ{f=f}x. x) 1
    // (λ{f = @ (λf. λ{f=f}x. x), f=f}x. x)
    // {x=1, f=@...} x
    // 1
    assert_eq!(reduce(app(fix(f.clone()), int(1))), int(1));
  }

  // TODO: Make these part of each rule tests.
  #[test]
  fn test_sanity_checks() {
    // (λx. x) 1
    // ---------
    // 1
    assert_eq!(reduce(app(lam(nil(), var(0)), int(1))), int(1));

    // (λx. x 1) #0
    // ------------
    // #0 1
    assert_eq!(
      reduce(app(lam(nil(), app(var(0), int(1))), ctr(0))),
      app(ctr(0), int(1))
    );

    // (λx. λy. y) 1
    // -------------
    // λ{x=1}y. y
    assert_eq!(
      reduce(app(lam(nil(), lam(nil(), var(0))), int(1))),
      lam(app(def(int(1), nil()), nil()), var(0))
    );

    // (λx. λy. y) 1 2
    // -------------
    // 2
    assert_eq!(
      reduce(app(app(lam(nil(), lam(nil(), var(0))), int(1)), int(2))),
      int(2)
    );

    // (λx. λ{x=x}y. x) 1
    // ------------------
    // λ{x=1, x=x}y. x
    assert_eq!(
      reduce(app(lam(nil(), lam(def(var(0), nil()), var(1))), int(1))),
      lam(app(def(int(1), nil()), def(var(0), nil())), var(1))
    );

    // (λx. λ{x=x}y. x) 1 2
    // ------------------
    // 1
    assert_eq!(
      reduce(app(
        app(lam(nil(), lam(def(var(0), nil()), var(1))), int(1)),
        int(2)
      )),
      int(1)
    );

    // (False -> 0 | True -> 1) #0
    // (λ. [0, 1] %0) #0
    // ---------------------------
    // 0
    assert_eq!(
      reduce(app(
        lam(nil(), app(jmp!(nil(), [int(0), int(1)]), var(0))),
        ctr(0)
      )),
      int(0)
    );

    // (False -> 0 | True -> 1) #0
    // (λ. [0, 1] %0) #1
    // ---------------------------
    // 1
    assert_eq!(
      reduce(app(
        lam(nil(), app(jmp!(nil(), [int(0), int(1)]), var(0))),
        ctr(1)
      )),
      int(1)
    );
  }

  #[test]
  fn test_recursion() {
    // f False = 42
    // f True = f False
    //
    // f = @ (λf. False -> 42 | True -> f False)
    // f = @ (λf. λ{f=f}x. {x=x, f=f} [42, f #0] x)
    // f = @ (λ. λ{%0}. [42, %1 #0] %0)
    let f = fix(lam(
      nil(),
      lam(
        def(var(0), nil()),
        app(
          jmp!(
            def(var(0), def(var(1), nil())),
            [int(42), app(var(1), ctr(0))]
          ),
          var(0),
        ),
      ),
    ));
    assert_eq!(reduce(app(f.clone(), ctr(0))), int(42));
    assert_eq!(reduce(app(f.clone(), ctr(1))), int(42));
  }

  #[test]
  fn test_factorial() {
    // f 0 = 1
    // f n = n * f (n - 1)
    //
    // f = @ (λf. (0 -> 1 | n -> n * f (n - 1)))
    // f = @ (λ. #{%0}. [1 | %0 * %1 (- %0 1)])
  }
}

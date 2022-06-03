use std::rc::Rc;

// Closure calculus: https://blog.chewxy.com/wp-content/uploads/personal/dissertation31482.pdf

// TODO: Maybe optimization: Nil can be a null pointer.
// TODO: Test if Box is faster than Rc.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
  Nil,
  Int(usize),
  Var(usize),
  Def(Rc<Expr>, Rc<Expr>),
  Lam(Rc<Expr>),
  App(Rc<Expr>, Rc<Expr>),
  Arr(Rc<Expr>, Rc<Vec<Rc<Expr>>>),
}
use Expr::*;

// Synatx sugar.
fn nil() -> Rc<Expr> {
  Rc::new(Nil)
}
fn int(n: usize) -> Rc<Expr> {
  Rc::new(Int(n))
}
fn var(i: usize) -> Rc<Expr> {
  Rc::new(Var(i))
}
fn def(a: Rc<Expr>, env: Rc<Expr>) -> Rc<Expr> {
  Rc::new(Def(a, env))
}
fn lam(a: Rc<Expr>) -> Rc<Expr> {
  Rc::new(Lam(a))
}
fn app(a: Rc<Expr>, b: Rc<Expr>) -> Rc<Expr> {
  Rc::new(App(a, b))
}
fn arr(env: Rc<Expr>, array: Vec<Rc<Expr>>) -> Rc<Expr> {
  Rc::new(Arr(env, Rc::new(array)))
}

// TODO: Tail call optimization.
fn reduce(expr: &Expr) -> Expr {
  match expr {
    App(a, b) => match reduce(a) {
      // Nil closure.
      Nil => reduce(b),

      Def(a1, a2) => match b.as_ref() {
        // Variable lookup.
        Var(0) => reduce(a1.as_ref()),
        Var(i) => reduce(&App(a2.clone(), var(i - 1))),

        // Closure propagation.
        Lam(b) => Lam(app(a.clone(), b.clone())),
        Def(b1, b2) => Def(app(a.clone(), b1.clone()), app(a.clone(), b2.clone())),
        Arr(b, array) => Arr(app(a.clone(), b.clone()), array.clone()),

        // Closure application.
        App(b1, b2) => reduce(&App(app(a.clone(), b1.clone()), app(a.clone(), b2.clone()))),

        // Closure constant.
        b => (*b).clone(),
      },

      // Beta reduction.
      Lam(a) => reduce(&App(def(b.clone(), nil()), a.clone())),

      Arr(env, array) => match b.as_ref() {
        // Branch.
        Int(n) => reduce(&App(env, array[*n].clone())),

        // Constant.
        _ => expr.clone(),
      },

      // Application constant.
      _ => expr.clone(),
    },

    // -- Constant.
    _ => expr.clone(),
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_reduce_constant() {
    assert_eq!(reduce(&Nil), Nil);
    assert_eq!(reduce(&Int(1)), Int(1));
    assert_eq!(reduce(&Var(0)), Var(0));
    assert_eq!(reduce(&Def(int(1), nil())), Def(int(1), nil()));
    assert_eq!(reduce(&Lam(var(0))), Lam(var(0)));
    assert_eq!(reduce(&App(int(1), int(2))), App(int(1), int(2)));
    assert_eq!(
      reduce(&Arr(nil(), Rc::new(vec![]))),
      Arr(nil(), Rc::new(vec![]))
    );
  }

  #[test]
  fn test_reduce_nil_closure() {
    assert_eq!(reduce(&App(nil(), nil())), Nil);
    assert_eq!(reduce(&App(nil(), int(1))), Int(1));
    assert_eq!(reduce(&App(nil(), var(0))), Var(0));
    assert_eq!(reduce(&App(nil(), lam(int(1)))), Lam(int(1)));
    assert_eq!(reduce(&App(nil(), def(int(1), nil()))), Def(int(1), nil()));
    assert_eq!(reduce(&App(nil(), app(int(1), nil()))), App(int(1), nil()));
    assert_eq!(
      reduce(&App(nil(), arr(nil(), vec![]))),
      Arr(nil(), Rc::new(vec![]))
    );
  }

  #[test]
  fn test_reduce_closure_constant() {
    let env = def(int(1), nil());
    assert_eq!(reduce(&App(env.clone(), nil())), Nil);
    assert_eq!(reduce(&App(env.clone(), int(1))), Int(1));
  }

  #[test]
  fn test_reduce_variable_lookup() {
    let env = def(int(1), def(int(2), nil()));
    assert_eq!(reduce(&App(env.clone(), var(0))), Int(1));
    assert_eq!(reduce(&App(env.clone(), var(1))), Int(2));
    assert_eq!(reduce(&App(env.clone(), var(2))), Var(0));
    assert_eq!(reduce(&App(env.clone(), var(3))), Var(1));
  }

  #[test]
  fn test_reduce_closure_propagation() {
    let env1 = def(int(1), nil());
    let env2 = def(int(2), nil());
    assert_eq!(
      reduce(&App(env1.clone(), lam(int(2)))),
      Lam(app(env1.clone(), int(2)))
    );
    assert_eq!(
      reduce(&App(env1.clone(), env2.clone())),
      Def(app(env1.clone(), int(2)), app(env1.clone(), nil()))
    );
    assert_eq!(
      reduce(&App(env1.clone(), arr(env2.clone(), vec![]))),
      Arr(app(env1.clone(), env2.clone()), Rc::new(vec![]))
    );
  }

  #[test]
  fn test_reduce_closure_application() {
    let env = def(lam(var(0)), nil());
    assert_eq!(reduce(&App(env.clone(), app(var(0), int(1)))), Int(1));
  }

  #[test]
  fn test_reduce_beta_reduction() {
    assert_eq!(reduce(&App(lam(var(0)), int(1))), Int(1));
  }

  #[test]
  fn test_reduce_branch() {
    let arr = arr(def(int(3), nil()), vec![int(1), int(2), var(0)]);
    assert_eq!(reduce(&App(arr.clone(), int(0))), Int(1));
    assert_eq!(reduce(&App(arr.clone(), int(1))), Int(2));
    assert_eq!(reduce(&App(arr.clone(), int(2))), Int(3));
  }
}

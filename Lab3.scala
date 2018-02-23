package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * <Richard Morley>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */



  override type Env = Map[String, Expr]
  override val empty: Env = Map()

  override def lookup(env: Env, x: String): Expr = env(x)
  override def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }

  def get(env: Env, x: String): Expr = env(x)




  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => val num = raw"^d+".r
        val numCharacters = num.findFirstIn(s)
        numCharacters match {
          case Some(n) => n.toDouble
          case _ => Double.NaN
        }
      case Function(_, _, _) => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) if (n compare(0.0)) == 0 || (n compare(-0.0)) == 0 || n.isNaN => false
      case N(_) => true
      case Undefined => false
      case S("") => false
      case S(_) => true
      case Function(_, _, _) => true
      //case _ => ??? // delete this line when done
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case Undefined => "undefined"
      case B(b) => b.toString
      case N(n) => if (n.isWhole()) "%.0f" format(n) else n.toString
      //case _ => ??? // delete this line when done
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Ge => s1 >= s2
          case Gt => s1 > s2
        }
      case _ =>
        val  (n1, n2) = (toNumber(v1), toNumber(v2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Ge => n1 >= n2
          case Gt => n1 > n2
        }

    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */

  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    def eToN(e: Expr): Double = toNumber(eval(env, e))

    def eToB(e: Expr): Boolean = toBoolean(eval(env, e))

    def eToVal(e: Expr): Expr = eval(env, e)

    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e

      case Var(x) => get(env, x)

      case _ if isValue(e) => e

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      case Unary(uop, e1) => uop match {
        case Neg => N(-eToN(e1))

        case Not => B(!eToB(e1))
      }


      case Binary(Eq, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (Function(_,_,_), _) => throw new DynamicTypeError(e)
        case (_, Function(_,_,_)) => throw new DynamicTypeError(e)
        case (S(s1), S(s2)) => B(s1 == s2)
        case (N(n1), N(n2)) => B(n1 == n2)
        case (B(b1), B(b2)) => B(b1 == b2)
        case (_, _) => B(false)
      }
      case Binary(Ne, e1, e2) =>
        val v1 = eToVal(e1)
        val v2 = eToVal(e2)
        (v1,v2)match {
          case (Function(_,_,_), _) => throw new DynamicTypeError(e)
          case (_, Function(_,_,_)) => throw new DynamicTypeError(e)
          case (v1,v2) => B(v1 != v2)
        }

      case Binary(bop, e1, e2) => bop match {
        case Plus => (eToVal(e1), eToVal(e2)) match {
          case (S(_), _) => S(toStr(eToVal(e1)) + toStr(eToVal(e2)))
          case (_, S(_)) => S(toStr(eToVal(e1)) + toStr(eToVal(e2)))
          case (_, _) => N(toNumber(eToVal(e1)) + toNumber(eToVal(e2)))
        }
        case Minus => N(toNumber(eToVal(e1)) - toNumber(eToVal(e2)))


        case Times => N(toNumber(eToVal(e1)) * toNumber(eToVal(e2)))
        case Div => N(toNumber(eToVal(e1)) / toNumber(eToVal(e2)))
        case Gt => (eToVal(e1), eToVal(e2)) match {
          case (S(_), S(_)) => B(toStr(eToVal(e1)) > toStr(eToVal(e2)))
          case (_, _) => B(toNumber(eToVal(e1)) > toNumber(eToVal(e2)))
        }
        case Lt => (eToVal(e1), eToVal(e2)) match {
          case (S(_), S(_)) => B(toStr(eToVal(e1)) < toStr(eToVal(e2)))
          case (_, _) => B(toNumber(eToVal(e1)) < toNumber(eToVal(e2)))
        }

        case Le => (eToVal(e1), eToVal(e2)) match {
          case (S(_), S(_)) => B(toStr(eToVal(e1)) <= toStr(eToVal(e2)))
          case (_, _) => B(toNumber(eToVal(e1)) <= toNumber(eToVal(e2)))
        }
        case Ge => {
          val first: Expr = eval(env, e1)
          val second: Expr = eval(env, e2)
          (first, second) match {
            case (S(s1), S(s2)) => B(s1 >= s2)
            case _ => B(toNumber(first) >= toNumber(second))
          }
        }
        case And => val v1 = eToVal(e1)
          if (toBoolean(v1)) eToVal(e2) else v1
        case Or => val v1 = eToVal(e1)
          if (toBoolean(v1)) v1 else eToVal(e2)
        case Seq => eToVal(e1); eToVal(e2)
        // ****** Your cases here
      }

      case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)

      case If(e1, e2, e3) => if (eToB(e1)) eToVal(e2) else eToVal(e3)

      case Call(e1, e2) => eToVal(e1) match {
        case Function(Some(x1), x2, e3) => eval(extend(extend(env, x1, eval(env, e1)), x2, eval(env, e2)), e3)
        case Function(None, x, e3) => eval(extend(env, x, eToVal(e2)), e3)
        case _ => throw DynamicTypeError(e)
      }
      case _ => throw new UnsupportedOperationException // delete this line when done
    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case None => e
      case Some(e1) => {
        loop(e1, n+1)
      }
    }
    loop(e0, 0)
  }

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))

    def subst(e: Expr): Expr = substitute(e, v, x)

    e match {
      case N(_) | B(_) | Undefined | S(_) => e

      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))

      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Call(e1, e2) => Call(subst(e1), subst(e2))
      case Var(y) => if (y == x) v else Var(y)
      case Function(None, xf, e1) => if (xf == x) Function(None, xf, e1) else Function(None, xf, subst(e1))
      case Function(Some(y1), y2, e1) => if (y2 == x || y1 == x) Function(Some(y1), y2, e1) else Function(Some(y1), y2, subst(e1))
      case ConstDecl(y, e1, e2) =>
      {
        if (x == y) ConstDecl(y, subst(e1), e2)
        else ConstDecl(y, subst(e1), subst(e2))
      }
      case _ => throw new UnsupportedOperationException

    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case Unary(Neg, v) if isValue(v) => N(- toNumber(v))
      case Unary(Not, v) if isValue(v) => B( ! toBoolean(v))
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case(S(v1), _) => S(v1 + toStr(v2))
        case(_, S(v2)) => S(toStr(v1) + v2)
        case(_, _) => N(toNumber(v1) + toNumber(v2))
      }
      /* Do Arith */
      case Binary(Minus, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) - toNumber(v2))
      case Binary(Times, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) * toNumber(v2))
      case Binary(Div, v1, v2) if isValue(v1) && isValue(v2) => N(toNumber(v1) / toNumber(v2))

      /* Do inequality: number, number2, string */
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))

      case Binary(bop @ (Eq | Ne), v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match{
        case (Function(_, _, _), _) => throw new DynamicTypeError(e)
        case (_,Function(_, _, _)) => throw new DynamicTypeError(e)
        case (v1,v2) if isValue(v1) && isValue(v2) => {
          if (bop == Eq) B(v1 == v2)
          else B(v1 != v2)
        }
      }

      case Binary(And, v1, e2) if isValue(v1) => toBoolean(v1) match{
        case true => e2
        case _ => v1
      }

      case Binary(Or, v1, e2) if isValue(v1) => toBoolean(v1) match{
        case false => e2
        case _ => v1
      }

      case If(v1, e2, e3) if isValue(v1) => toBoolean(v1) match{
        case true => e2
        case false => e3
      }

      case ConstDecl(x, v1, e2) if isValue(v1) => {
        substitute(e2, v1, x)
      }
      /* substitute takes: e: expr, v: expr, x: string */

      case Call(v1, v2) if isValue(v1) && isValue(v2) => v1 match{
        /* Not recursive */
        case Function(None, x, e) => {
          substitute(e, v2, x)
        }
        /* Recursive */
        case Function(Some(f), x2, fbody) => {
          substitute(substitute(fbody, v1, f), v2, x2)
        }
        case _ => throw new DynamicTypeError(e)
      }

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

      //SearchBinary//
      case Binary(bop, e1, e2) => e1 match {
        //SearchBinaryArith2//
        case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => Binary(bop, e1, step(e2))
        //SearchBinary1//
        case _ => Binary(bop, step(e1), e2)
      }
      //SearchUnary//
      case Unary(uop, e1) => Unary(uop, step(e1))

      //SearchIf//
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      //SearchConst//
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      //SearchCall//
      case Call(e1, e2) => (e1,e2) match {
        case (Function(_, _, _), s2) =>  Call(e1, step(s2))
        case (s1,s2) => Call(step(s1),s2)
        //case _ => throw new TypeErrorCall(e)
      }

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }



  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}

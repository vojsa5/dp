package microc.symbolic_execution

import microc.ast.{CodeLoc, Expr, FunDecl, Loc}

import scala.collection.mutable
import scala.util.Random

object Value {

  sealed trait Val {
    def equals(other: Val): Boolean
  }

  trait Symbolic extends Expr with Val

  abstract class RefVal() extends Val {
    override def toString: String = s"<pointer ${hashCode()}>"
  }

  object UninitializedRef extends RefVal {

    override def equals(other: Val): Boolean =
      other match {
        case UninitializedRef => true
        case _ => false
      }
  }

  case class PointerVal(address: Int) extends RefVal {

    override def equals(other: Val): Boolean =
      other match {
        case PointerVal(address2) if address == address2 => true
        case _ => false
      }
  }

  case object NullRef extends RefVal {
    override def toString: String = "null"

    override def equals(other: Val): Boolean =
      other match {
        case NullRef => true
        case _ => false
      }
  }

//  case object ReturnRef extends RefVal {
//    override def toString: String = "return"
//  }

  case class ArrVal(elems: scala.Array[PointerVal]) extends Val {
    override def toString: String = elems.mkString("[", ",", "]")

    override def equals(other: Val): Boolean =
      other match {
        case ArrVal(elems2) =>
          if (elems.length == elems2.length) {
            for (i <- elems.indices) {
              if (!elems(i).equals(elems2(i))) {
                return false
              }
            }
            return true
          }
          false
        case _ => false
      }
  }

  case class RecVal(fields: mutable.Map[String, Val]) extends Val {
    override def toString: String = fields.map { case (k, v) => s"$k:$v" }.mkString("{", ",", "}")

    override def equals(other: Val): Boolean =
      other match {
        case RecVal(fields2) =>
          if (fields.size == fields2.size) {
            for (k <- fields.keys) {
              if (!fields2.contains(k)) {
                if (!fields(k).equals(fields2(k))) {
                  return false
                }
              }
            }
            return true
          }
          false
        case _ => false
      }
  }

  case class SymbolicVal(loc: Loc) extends Symbolic {
    val name = (1 to 10).map(_ => "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"(new Random().nextInt(52))).mkString
    override def toString: String = name

    override def equals(other: Val): Boolean =
      other match {
        case v@SymbolicVal(_) => name == v.name
        case _ => false
      }

    override def equals(other: Expr): Boolean =
      other match {
        case v@SymbolicVal(_) => name == v.name
        case _ => false
      }
  }

  case class SymbolicExpr(value: Expr, loc: Loc) extends Symbolic {
    override def toString: String = value.toString

    override def equals(other: Expr): Boolean =
      other match {
        case SymbolicExpr(value2, _) => value.equals(value2)
        case _ => false
      }

    override def equals(other: Val): Boolean =
      other match {
        case SymbolicExpr(value2, _) => value.equals(value2)
        case _ => false
      }
  }

  case class FunVal(fun: FunDecl) extends Val {
    override def equals(other: Val): Boolean =
      other match {
        case FunVal(fun2) => fun == fun2
        case _ => false
      }
  }

  case class IteVal(trueState: Val, falseState: Val, expr: Expr, loc: Loc) extends Symbolic {
    override def equals(other: Val): Boolean =
      other match {
        case v@IteVal(t, f, e, _) => trueState.equals(t) && falseState.equals(f) && expr.equals(e)
        case _ => false
      }

    override def equals(other: Expr): Boolean =
      other match {
        case v@IteVal(t, f, e, _) => trueState.equals(t) && falseState.equals(f) && expr.equals(e)
        case _ => false
      }
  }

}


package microc.symbolic_execution

import microc.ast.{CodeLoc, Expr, Loc}

object Value {

  sealed trait Val

  trait Symbolic extends Expr with Val

  class RefVal() extends Val {
    override def toString: String = s"<pointer ${hashCode()}>"
  }

  object UninitializedRef extends RefVal {

  }

  case class PointerVal(address: Int) extends RefVal {

  }

  object NullRef extends RefVal {
    override def toString: String = "null"
  }

  case object ReturnRef extends RefVal {
    override def toString: String = "return"
  }

  case class SymbolicVal(loc: Loc) extends Symbolic {
    override def toString: String = "unknown"
  }

  case class SymbolicExpr(value: Expr, loc: Loc) extends Symbolic {
    override def toString: String = value.toString
  }

}


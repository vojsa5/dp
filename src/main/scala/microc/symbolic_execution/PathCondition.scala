package microc.symbolic_execution

import microc.ast.{BinaryOp, CodeLoc, Equal, Expr, Number}

object PathCondition {
  def initial(): PathCondition = {
    new PathCondition(None, BinaryOp(Equal, Number(1, CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
  }
}


class PathCondition(val prev: Option[PathCondition], val expr: Expr) {

}

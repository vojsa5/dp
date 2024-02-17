package microc.symbolic_execution

import microc.ast.{AndAnd, BinaryOp, CodeLoc, Expr, Stmt}
import microc.symbolic_execution.Value.SymbolicVal

class Path(val statements: List[Stmt], var condition: Expr) {

  val iterations = SymbolicVal(CodeLoc(0, 0))

  def addedCondition(expr: Expr): Path = {
    new Path(statements, BinaryOp(AndAnd, condition, expr, condition.loc))
  }

  def appendedStatement(stmt: Stmt): Path = {
    new Path(statements.appended(stmt), condition)
  }

  def appendedAsPath(path: Path): Path = {
    new Path(statements.appendedAll(path.statements), BinaryOp(AndAnd, condition, path.condition, condition.loc))
  }

  def simplifiedCondition(): Path = {
    new Path(statements, LoopSummary.simplifyArithExpr(condition))
  }

}

package microc.symbolic_execution

import microc.ast.{AndAnd, BinaryOp, Expr, Stmt}

class Path(val statements: List[Stmt], var condition: Expr) {

  def addedCondition(expr: Expr): Path = {
    new Path(statements, BinaryOp(AndAnd, condition, expr, condition.loc))
  }

  def appendedStatement(stmt: Stmt): Path = {
    new Path(statements.appended(stmt), condition)
  }

  def appendedAsPath(path: Path): Path = {
    new Path(statements.appendedAll(path.statements), BinaryOp(AndAnd, condition, path.condition, condition.loc))
  }

}

package microc.symbolic_execution.optimizations

import microc.ast.{AndAnd, BinaryOp, CodeLoc, Expr, Stmt}
import microc.symbolic_execution.Utility
import microc.symbolic_execution.Value.SymbolicVal

//class Path(val statements: List[Stmt], var condition: Expr) {
//
//  val iterations = SymbolicVal(CodeLoc(0, 0))
//
//  def addedCondition(expr: Expr): Path = {
//    new Path(statements, BinaryOp(AndAnd, condition, expr, condition.loc))
//  }
//
//  def appendedStatement(stmt: Stmt): Path = {
//    new Path(statements.appended(stmt), condition)
//  }
//
//  def appendedAsPath(path: Path): Path = {
//    new Path(statements.appendedAll(path.statements), BinaryOp(AndAnd, condition, path.condition, condition.loc))
//  }
//
//  def simplifiedCondition(): Path = {
//    new Path(statements, LoopSummary.simplifyArithExpr(condition))
//  }
//
//}


class Path(var statements: List[Stmt], var condition: Expr, var changes: List[(Expr, (Expr) => ((Expr) => Expr))]) {

  val iterations = SymbolicVal(CodeLoc(0, 0))

  def addedCondition(expr: Expr): Path = {
    condition = BinaryOp(AndAnd, condition, expr, condition.loc)
    this
  }

  def appendedStatement(stmt: Stmt): Path = {
    statements = statements.appended(stmt)
    this
  }

  def appendedAsPath(path: Path): Path = {
    var newChanges = List[(Expr, (Expr) => ((Expr) => Expr))]()
    newChanges = newChanges.appendedAll(changes)
    newChanges = newChanges.appendedAll(path.changes)
//    changes = newChanges
//    condition = BinaryOp(AndAnd, condition, path.condition, condition.loc)
//    statements = statements.appendedAll(path.statements)
//    this
    new Path(statements.appendedAll(path.statements), BinaryOp(AndAnd, condition, path.condition, condition.loc), newChanges)
  }

  def simplifiedCondition(): Path = {
    condition = Utility.simplifyArithExpr(condition)
    this
  }

  def updatedChanges(name: Expr, change: (Expr) => ((Expr) => Expr)): Path = {
    changes = changes.filter(change => !change._1.equals(name))
    changes = changes.appended(name, change)
    condition = Utility.simplifyArithExpr(condition)
    this
  }

}

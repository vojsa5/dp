package microc.symbolic_execution

import microc.ast.{AndAnd, BinaryOp, CodeLoc, Expr, Number, Stmt}
import microc.symbolic_execution.Value.SymbolicVal

import scala.collection.mutable

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


class Path(val statements: List[Stmt], var condition: Expr, var changes: List[(Expr, (Expr) => ((Expr) => Expr))]) {

  val iterations = SymbolicVal(CodeLoc(0, 0))

  def addedCondition(expr: Expr): Path = {
    val res = new Path(statements, BinaryOp(AndAnd, condition, expr, condition.loc), changes)
    new Path(statements, BinaryOp(AndAnd, condition, expr, condition.loc), changes)
  }

  def appendedStatement(stmt: Stmt): Path = {
    new Path(statements.appended(stmt), condition, changes)
  }

  def appendedAsPath(path: Path): Path = {
    var newChanges = List[(Expr, (Expr) => ((Expr) => Expr))]()
    newChanges = newChanges.appendedAll(changes)
    newChanges = newChanges.appendedAll(path.changes)
    new Path(statements.appendedAll(path.statements), BinaryOp(AndAnd, condition, path.condition, condition.loc), newChanges)
  }

  def simplifiedCondition(): Path = {
    new Path(statements, Utility.simplifyArithExpr(condition), changes)
  }

  def updatedChanges(name: Expr, change: (Expr) => ((Expr) => Expr)): Path = {
    var newChanges = List[(Expr, (Expr) => ((Expr) => Expr))]()
    newChanges = newChanges.appendedAll(changes)
    newChanges = newChanges.appended(name, change)
    new Path(statements, Utility.simplifyArithExpr(condition), newChanges)
  }

}

package microc.symbolic_execution

import com.microsoft.z3.{ArithExpr, ArithSort, BoolSort, Context, Solver, Status}
import microc.ast.Expr
import microc.cfg.CfgNode

import scala.collection.mutable

class PathSubsumption(constraintSolver: ConstraintSolver, ctx: Context) {
  val annotations = mutable.HashMap[CfgNode, Set[com.microsoft.z3.Expr[_]]]()


  def addAnnotation(node: CfgNode, expr: com.microsoft.z3.Expr[_]): Unit = {
    annotations(node) = annotations.getOrElseUpdate(node, Set()) + ctx.mkNot(constraintSolver.getCondition(expr))
  }

  def checkSubsumption(node: CfgNode, expr: Expr, symbolicState: SymbolicState): Boolean = {
    val nodeAnnotations = annotations.get(node)
    if (nodeAnnotations.nonEmpty) {
      for (anotation <- nodeAnnotations.get) {
        val solver = ctx.mkSolver()
        val constraint = ctx.mkAnd(
          constraintSolver.getCondition(constraintSolver.createConstraintWithState(expr, symbolicState)),
          anotation.asInstanceOf[com.microsoft.z3.Expr[BoolSort]]
        )
        solver.add(constraint)
        solver.check() match {
          case Status.UNSATISFIABLE =>
            return false
          case _ =>
        }
      }
    }
    true
  }
}

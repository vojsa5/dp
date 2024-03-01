package microc.symbolic_execution

import com.microsoft.z3.{ArithExpr, ArithSort, BoolSort, Context, Solver, Status}
import microc.ast.{AndAnd, AssignStmt, AstNode, BinaryOp, CodeLoc, Expr, Identifier, Not, Null, Number, Stmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.PathSubsumption.tmp
import microc.symbolic_execution.Value.{SymbolicExpr, SymbolicVal}

import scala.collection.mutable


object PathSubsumption {


  def applyIdentifier(expr: Expr, identifier: Identifier, identifierValue: Expr): Expr = {
    expr match {
      case Not(expr, loc) =>
        Not(applyIdentifier(expr, identifier,identifierValue), loc)
      case BinaryOp(operator, left, right, loc) =>
        BinaryOp(operator, applyIdentifier(left, identifier, identifierValue), applyIdentifier(right, identifier, identifierValue), loc)
      case id@Identifier(name, _) if identifier.name == name => identifierValue
      case id@Identifier(_, _) => id
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyIdentifier(expr, identifier, identifierValue)
      case Null(loc) => Null(loc)
    }
  }


  def tmp(stmt: AstNode, annotation: Expr): Expr = {
    stmt match {
      case AssignStmt(Identifier(name, loc), right, _) =>
        applyIdentifier(annotation, Identifier(name, loc), right)
//        tmp2(annotation, name) match {
//          case Some(expr) => expr
//          case None => Number(1, loc)
//        }
      case _ => annotation
    }
  }

//  def tmp2(expr: Expr, id: String): Option[Expr] = {
//    expr match {
//      case BinaryOp(AndAnd, left, right, loc) =>
//        (tmp2(left, id), tmp2(right, id)) match {
//          case (Some(val1), Some(val2)) => Some(BinaryOp(AndAnd, val1, val2, loc))
//          case (Some(val1), None) => Some(val1)
//          case (None, Some(val2)) => Some(val2)
//          case (None, None) => None
//        }
//      case BinaryOp(operator, left, right, loc) =>
//        (tmp2(left, id), tmp2(right, id)) match {
//          case (Some(val1), Some(val2)) => Some(BinaryOp(operator, left, right, loc))
//          case _ => None
//        }
//      case Not(expr, loc) =>
//        tmp2(expr, id) match {
//          case Some(value) => Some(Not(value, loc))
//          case None => None
//        }
//      case Identifier(name, _) if name == id => None
//      case Identifier(name, loc) => Some(Identifier(name, loc))
//      case Number(value, loc) => Some(Number(value, loc))
//    }
//  }
}


class PathSubsumption(constraintSolver: ConstraintSolver, ctx: Context) {
//  val annotations = mutable.HashMap[CfgNode, Set[com.microsoft.z3.Expr[_]]]()
  val annotations = mutable.HashMap[CfgNode, Set[Expr]]()


//  def addAnnotation(node: CfgNode, expr: com.microsoft.z3.Expr[_]): Unit = {
//    annotations(node) = annotations.getOrElseUpdate(node, Set()) + ctx.mkNot(constraintSolver.getCondition(expr))
//  }


  def addAnnotation(node: CfgNode, expr: Expr): Unit = {
    annotations(node) = annotations.getOrElseUpdate(node, Set()) + expr
  }


  def computeAnnotation(node: CfgNode): Unit = {
    null
    for (succ <- node.succ) {
      annotations(node) = annotations.getOrElseUpdate(succ, Set()).map(annotation => tmp(node.ast, annotation))//TODO merge
    }
  }



  def checkSubsumption(node: CfgNode, expr: Expr, symbolicState: SymbolicState): Boolean = {
    val nodeAnnotations = annotations.get(node)
    if (nodeAnnotations.nonEmpty) {
      for (anotation <- nodeAnnotations.get) {
        val solver = ctx.mkSolver()
        val constraint = ctx.mkAnd(
          constraintSolver.getCondition(constraintSolver.createConstraintWithState(expr, symbolicState)),
          constraintSolver.getCondition(constraintSolver.createConstraintWithState(Not(anotation, CodeLoc(0, 0)), symbolicState))
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

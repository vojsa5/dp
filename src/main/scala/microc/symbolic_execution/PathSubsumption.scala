package microc.symbolic_execution

import com.microsoft.z3.{ArithExpr, ArithSort, BoolSort, Context, Solver, Status}
import microc.ast.{AndAnd, ArrayAccess, ArrayNode, AssignStmt, AstNode, BinaryOp, CodeLoc, Deref, Expr, FieldAccess, Identifier, IfStmt, Input, NestedBlockStmt, Not, Null, Number, OrOr, Record, RecordField, Stmt, VarRef, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.PathSubsumption.replaceExpr
import microc.symbolic_execution.Value.{SymbolicExpr, SymbolicVal}

import java.util
import scala.collection.mutable


object PathSubsumption {


  def replaceExpr(expr: Expr, toReplace: Expr, newValue: Expr): Expr = {
    expr match {
      case _ if expr.equals(toReplace) => newValue
      case Not(expr, loc) =>
        Not(replaceExpr(expr, toReplace,newValue), loc)
      case BinaryOp(operator, left, right, loc) =>
        BinaryOp(operator, replaceExpr(left, toReplace, newValue), replaceExpr(right, toReplace, newValue), loc)
      case id@Identifier(_, _) => id
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => replaceExpr(expr, toReplace, newValue)
      case Null(loc) => Null(loc)
      case Input(loc) => SymbolicVal(CodeLoc(0, 0))
      case ArrayAccess(array, index, loc) => ArrayAccess(replaceExpr(array, toReplace, newValue), replaceExpr(index, toReplace, newValue), loc)
      case ArrayNode(elems, loc) => ArrayNode(elems.map(elem => replaceExpr(elem, toReplace, newValue)), loc)
      case Deref(pointer, loc) => Deref(replaceExpr(pointer, toReplace, newValue), loc)
      case VarRef(id, loc) => replaceExpr(id, toReplace, newValue)
      case FieldAccess(record, field, loc) => FieldAccess(replaceExpr(record, toReplace, newValue), field, loc)
      case Record(fields, loc) => Record(fields.map(field => RecordField(field.name, replaceExpr(field.expr, toReplace, newValue), field.loc)), loc)
      case _ =>
        throw new Exception("IMPLEMENT")
    }
  }
}



class PathSubsumption(constraintSolver: ConstraintSolver, ctx: Context) {
//  val annotations = mutable.HashMap[CfgNode, Set[com.microsoft.z3.Expr[_]]]()
  val annotations = mutable.HashMap[CfgNode, Expr]()


  def addAnnotationsToALoop(loop: CfgNode, annotation: Expr): Unit = {
    val succs = loop.succ
    val maxSucc = succs.maxBy(node => node.id).id
    for (s <- succs) {
      addAnotations(s, loop.id, maxSucc, annotation)
    }
  }

  def addAnotations(node: CfgNode, minId: Double, maxId: Double, annotation: Expr): Unit = {
    if (node.id < maxId && node.id > minId) {
      node.ast match {
        case WhileStmt(_, _, _) =>
          addAnnotationsToALoop(node, annotation)
        case _ =>
          addAnnotation(node, annotation)
          node.succ.foreach(s => addAnotations(s, minId, maxId, annotation))
      }
    }
  }

  def addAnnotation(node: CfgNode, expr: Expr): Unit = {
    annotations(node) = Utility.simplifyArithExpr(BinaryOp(AndAnd, annotations.getOrElseUpdate(node, Number(1, CodeLoc(0, 0))), expr, CodeLoc(0, 0)))
  }


  def computeAnnotation(node: CfgNode): Unit = {
    val t: util.LinkedList[mutable.HashSet[Expr]] = new util.LinkedList[mutable.HashSet[Expr]]
    if (node.succ.size == 2) {
      val (guard, thenBranch) = node.ast match {
        case IfStmt(guard, thenBranch, _, _) => (guard, thenBranch)
        case WhileStmt(guard, thenBranch, _) => (guard, thenBranch)
        case _ =>
          throw new Exception("This should never happen")
      }
      var annotation: Expr = Number(0, CodeLoc(0, 0))
      val thenNode = node.succ.minBy(node => node.id)
      if (annotations.contains(thenNode)) {
        if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          annotation = BinaryOp(OrOr, annotation, BinaryOp(AndAnd, Not(guard, CodeLoc(0, 0)), annotations(thenNode), CodeLoc(0, 0)), CodeLoc(0, 0))
        }
        else {
          annotation = BinaryOp(OrOr, annotation, BinaryOp(AndAnd, guard, annotations(thenNode), CodeLoc(0, 0)), CodeLoc(0, 0))
        }
      }
      val elseNode = node.succ.maxBy(node => node.id)
      if (annotations.contains(elseNode)) {
        if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          annotation = BinaryOp(OrOr, annotation, BinaryOp(AndAnd, guard, annotations(elseNode), CodeLoc(0, 0)), CodeLoc(0, 0))
        }
        else {
          annotation = BinaryOp(OrOr, annotation, BinaryOp(AndAnd, Not(guard, CodeLoc(0, 0)), annotations(elseNode), CodeLoc(0, 0)), CodeLoc(0, 0))
        }}
      if (annotation == Number(0, CodeLoc(0, 0))) {
        return
      }
      annotations.put(node, Utility.simplifyArithExpr(annotation))
    }
    if (node.succ.size == 1) {
      if (annotations.contains(node.succ.head)) {
        val annotation = annotations(node.succ.head)
        val newAnnotation = node.ast match {
          case AssignStmt(left, right, _) =>
            replaceExpr(annotation, left, right)
          case _ =>
            annotation
        }
        annotations.put(node, newAnnotation)
      }
    }
  }



  def checkSubsumption(node: CfgNode, expr: Expr, symbolicState: SymbolicState): Boolean = {
    if (annotations.contains(node)) {
      val anotation = annotations(node)
      val solver = ctx.mkSolver()
      val constraint = constraintSolver.getCondition(
        constraintSolver.createConstraintWithState(
          BinaryOp(
            AndAnd,
            symbolicState.pathCondition.expr,
            Not(anotation, CodeLoc(0, 0)),
            CodeLoc(0, 0)
          ),
          symbolicState)
      )
      System.out.println(constraint)
      solver.add(constraint)
      solver.check() match {
        case Status.UNSATISFIABLE =>
          return true
        case _ =>
      }
    }
    false
  }
}

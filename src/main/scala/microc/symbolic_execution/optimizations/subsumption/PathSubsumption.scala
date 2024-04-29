package microc.symbolic_execution.optimizations.subsumption

import com.microsoft.z3.{Context, Status}
import microc.ast.{AndAnd, AssignStmt, BinaryOp, CodeLoc, Expr, Identifier, IfStmt, NestedBlockStmt, Not, Number, OrOr, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.Value.Val
import microc.symbolic_execution.optimizations.summarization.LoopSummarization
import microc.symbolic_execution.{ConstraintSolver, SymbolicExecutor, SymbolicState, Utility}

import java.util
import scala.collection.mutable





class PathSubsumption(constraintSolver: ConstraintSolver) {
  val annotations = mutable.HashMap[CfgNode, Expr]()

  val pathsInLoop = mutable.HashMap[CfgNode, (SymbolicState, mutable.HashSet[SymbolicState])]()


  def performInduction(nodes: List[CfgNode], identifier: Identifier,
                       symbolicState: SymbolicState, executor: SymbolicExecutor, loop: CfgNode): Unit = {
    for (node <- nodes) {
      annotations.get(node) match {
        case Some(ann) =>
          annotations.put(node,
            Utility.simplifyArithExpr(removeNonInductiveLabels(symbolicState, Utility.replaceExpr(ann, identifier, Number(0, CodeLoc(0, 0))), executor, loop)))
        case None =>
      }
    }
  }


  def addAnnotations(nodes: List[CfgNode], annotation: Expr): Unit = {
    for (node <- nodes) {
      addAnnotation(node, annotation)
    }
  }

  def addAnnotation(node: CfgNode, expr: Expr): Unit = {
    annotations(node) = BinaryOp(OrOr, annotations.getOrElseUpdate(node, Number(0, CodeLoc(0, 0))), expr, CodeLoc(0, 0))
  }


  def computeAnnotationFromSuccessors(node: CfgNode, considerTrueBranchForWhile: Boolean = false): Unit = {
    val t: util.LinkedList[mutable.HashSet[Expr]] = new util.LinkedList[mutable.HashSet[Expr]]
    if (node.succ.size == 2) {
      var annotation: Expr = Number(0, CodeLoc(0, 0))
      val (guard, thenBranch) = node.ast match {
        case IfStmt(guard, thenBranch, _, _) => (guard, thenBranch)
        case WhileStmt(guard, thenBranch, _) => {
          if (!considerTrueBranchForWhile) {
            val elseNode = node.succ.maxBy(node => node.id)
            if (annotations.contains(elseNode)) {
              annotations.put(node, annotations(elseNode))
            }
            return
          }
          (guard, thenBranch)
        }
        case _ =>
          throw new Exception("This should never happen")
      }
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
          case AssignStmt(Identifier(name, _), _, _) if Utility.isSubsumptionVar(name) =>
            annotation
          case AssignStmt(left, right, _) =>
            Utility.replaceExpr(annotation, left, right)
          case _ =>
            annotation
        }
        annotations.put(node, newAnnotation)
      }
    }
  }



  def checkSubsumption(symbolicState: SymbolicState): Boolean = {
    val node = symbolicState.programLocation
    if (annotations.contains(node)) {
      val anotation = annotations(node)
      val solver = constraintSolver.ctx.mkSolver()
      val expr =
        BinaryOp(
        AndAnd,
        symbolicState.pathCondition,
        Not(anotation, CodeLoc(0, 0)),
        CodeLoc(0, 0)
      )
      val constraint = ConstraintSolver.getCondition(constraintSolver.ctx, constraintSolver.createConstraint(expr, symbolicState))
      solver.add(constraint)
      solver.check() match {
        case Status.UNSATISFIABLE =>
          return true
        case _ =>
      }
    }
    false
  }



  def computeInductivness(symbolicState: SymbolicState, expr: Expr, executor: SymbolicExecutor, loop: CfgNode): Boolean = {
    val (generalState, states) = if (!pathsInLoop.contains(loop)) {
      val generalState = LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, new mutable.HashMap[Val, Expr]())
      val generalState2 = generalState.deepCopy()
      val states = LoopSummarization.getAllPaths(generalState2.programLocation.succ.minBy(node => node.id), generalState2.programLocation.id, generalState2, executor)
      pathsInLoop.put(loop, (generalState, states))
      (generalState, states)
    }
    else {
      pathsInLoop(loop)
    }
    val initialConstraint = Utility.applyTheState(expr, generalState)
    for (state <- states) {
      val constraint = BinaryOp(AndAnd, initialConstraint, Not(Utility.applyTheState(expr, state), CodeLoc(0, 0)), CodeLoc(0, 0))
      val solver = constraintSolver.ctx.mkSolver()
      solver.add(ConstraintSolver.getCondition(constraintSolver.ctx, constraintSolver.createConstraint(constraint, state)))
      solver.check() match {
        case Status.SATISFIABLE =>
          return false
        case _ =>
      }
    }
    true
  }


  def removeNonInductiveLabels(symbolicState: SymbolicState, expr: Expr, executor: SymbolicExecutor, loop: CfgNode): Expr = {
    expr match {
      case BinaryOp(OrOr, left, right, loc) =>
        Utility.simplifyArithExpr(
          BinaryOp(
            OrOr,
            removeNonInductiveLabels(symbolicState, left, executor, loop),
            removeNonInductiveLabels(symbolicState, right, executor, loop),
            loc
          )
        )
      case n: Number => n//optimization - number is always inductive
      case other =>
        if (computeInductivness(symbolicState, other, executor, loop)) {
          other
        }
        else {
          Number(0, CodeLoc(0, 0))
        }
    }
  }
}

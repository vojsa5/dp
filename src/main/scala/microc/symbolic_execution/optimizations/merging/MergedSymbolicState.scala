package microc.symbolic_execution.optimizations.merging

import microc.ast.{Expr, IdentifierDecl, IfStmt, NestedBlockStmt, Not, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.{SymbolicState, SymbolicStore}


class MergedSymbolicState(
                           nextStatement: CfgNode,
                           pathCondition: Expr,
                           symbolicStore: SymbolicStore,
                           callStack: List[(CfgNode, List[IdentifierDecl])] = List.empty,
                           variableDecls: List[IdentifierDecl] = List.empty,
                           var innerStates: (SymbolicState, SymbolicState))
  extends SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls) {

  var tookTooLongToMerge: Boolean = false

  override def associatedPathsCount(): Int = {
    innerStates._1.associatedPathsCount() + innerStates._2.associatedPathsCount()
  }

  override def tookToLongToMerge(): Boolean = tookTooLongToMerge

  override def getIfTrueState(): SymbolicState = {
    val nextStatement = getProgramLocation()
    val ast = nextStatement.ast;
    ast match {
      case WhileStmt(guard, thenBranch, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          nextStatement.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          nextStatement.succ.find(s => s.ast == firstThenStatement).get
        }
        new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, innerStates)
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          nextStatement.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          nextStatement.succ.find(s => s.ast == firstThenStatement).get
        }
        new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, innerStates)
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            nextStatement.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
            nextStatement.succ.find(s => s.ast == firstThenStatement).get
          }
          return new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, innerStates)
        }
        val next = nextStatement.succ.find(s => s.ast != elseBranch.head).get
        new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, innerStates)
      case _ =>
        throw new Exception("this should never happen")
    }
  }

  override def getIfFalseState(): SymbolicState = {
    val nextStatement = getProgramLocation()
    val ast = nextStatement.ast;
    ast match {
      case WhileStmt(guard, thenBranch, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          nextStatement.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          nextStatement.succ.find(s => s.ast != firstThenStatement).get
        }
        new MergedSymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, innerStates)//TODO add to path condition
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          nextStatement.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          nextStatement.succ.find(s => s.ast != firstThenStatement).get
        }
        new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, innerStates)
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            nextStatement.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
            nextStatement.succ.find(s => s.ast != firstThenStatement).get
          }
          return new MergedSymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, innerStates)
        }
        val next = nextStatement.succ.find(s => s.ast == elseBranch.head).get
        new MergedSymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, innerStates)
      case _ =>
        throw new Exception("this should never happen")
    }
  }
}

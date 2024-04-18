package microc.symbolic_execution

import microc.ast.{Expr, IdentifierDecl, IfStmt, NestedBlockStmt, Not, WhileStmt}
import microc.cfg.CfgNode


class MergedSymbolicState(
                           nextStatement: CfgNode,
                           pathCondition: Expr,
                           symbolicStore: SymbolicStore,
                           callStack: List[(CfgNode, List[IdentifierDecl])] = List.empty,
                           variableDecls: List[IdentifierDecl] = List.empty,
                           var subStates: (SymbolicState, SymbolicState))
  extends SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls) {

  override def pathsCount(): Int = {
    subStates._1.pathsCount() + subStates._2.pathsCount()
  }

  override def getIfTrueState(): SymbolicState = {
    val nextStatement = getNextStatement()
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
        new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, subStates)
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          nextStatement.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          nextStatement.succ.find(s => s.ast == firstThenStatement).get
        }
        new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, subStates)
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            nextStatement.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
            nextStatement.succ.find(s => s.ast == firstThenStatement).get
          }
          return new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, subStates)
        }
        val next = nextStatement.succ.find(s => s.ast != elseBranch.head).get
        new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, subStates)
      case _ =>
        throw new Exception("this should never happen")
    }
  }

  override def getIfFalseState(): SymbolicState = {
    val nextStatement = getNextStatement()
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
        new MergedSymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, subStates)//TODO add to path condition
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          nextStatement.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          nextStatement.succ.find(s => s.ast != firstThenStatement).get
        }
        new MergedSymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, subStates)
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            nextStatement.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
            nextStatement.succ.find(s => s.ast != firstThenStatement).get
          }
          return new MergedSymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, subStates)
        }
        val next = nextStatement.succ.find(s => s.ast == elseBranch.head).get
        new MergedSymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls, subStates)
      case _ =>
        throw new Exception("this should never happen")
    }
  }
}

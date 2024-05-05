package microc.symbolic_execution

import microc.ast.{Expr, IdentifierDecl, IfStmt, NestedBlockStmt, Not, WhileStmt}
import microc.cfg.CfgNode

class SymbolicStateNotAssociatedWithAPath(symbolicState: SymbolicState) extends
  SymbolicState(symbolicState.programLocation, symbolicState.pathCondition, symbolicState.symbolicStore, symbolicState.callStack) {

  override def associatedPathsCount(): Int = 0


  override def getIfTrueState(): SymbolicState = {
    val ast = programLocation.ast;
    new SymbolicStateNotAssociatedWithAPath(ast match {
      case WhileStmt(guard, thenBranch, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          programLocation.succ.find(s => s.ast == ast).get
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          programLocation.succ.find(s => s.ast == firstThenStatement).get
        }
        new SymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          programLocation.succ.find(s => s.ast == ast).get
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          programLocation.succ.find(s => s.ast == firstThenStatement).get
        }
        new SymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            programLocation.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
            programLocation.succ.find(s => s.ast == firstThenStatement).get
          }
          return new SymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
        }
        val next = programLocation.succ.find(s => s.ast != elseBranch.head).get
        new SymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
    })
  }

  override def getIfFalseState(): SymbolicState = {
    val ast = programLocation.ast;
    new SymbolicStateNotAssociatedWithAPath(ast match {
      case WhileStmt(guard, thenBranch, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          programLocation.succ.find(s => s.ast != ast).get
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          programLocation.succ.find(s => s.ast != firstThenStatement).get
        }
        new SymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          programLocation.succ.find(s => s.ast != ast).get
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          programLocation.succ.find(s => s.ast != firstThenStatement).get
        }
        new SymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            programLocation.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
            programLocation.succ.find(s => s.ast != firstThenStatement).get
          }
          return new SymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
        }
        val next = programLocation.succ.find(s => s.ast == elseBranch.head).get
        new SymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
    })
  }

}

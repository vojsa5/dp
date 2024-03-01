package microc.symbolic_execution

import microc.ast.{IdentifierDecl, IfStmt, NestedBlockStmt, Not, WhileStmt}
import microc.cfg.CfgNode


class MergedSymbolicState(
                           nextStatement: CfgNode,
                           pathCondition: PathCondition,
                           symbolicStore: SymbolicStore,
                           callStack: List[(CfgNode, List[IdentifierDecl])] = List.empty,
                           var subStates: (SymbolicState, SymbolicState))
  extends SymbolicState(nextStatement, pathCondition, symbolicStore, callStack) {

  override def nextState(): SymbolicState = {
    new MergedSymbolicState(nextStatement.succ.head, pathCondition, symbolicStore, callStack, subStates)
  }

  override def getIfTrueState(): SymbolicState = {
    val ast = nextStatement.ast;
    nextStatement.succ.foreach(
      node => {
        ast match {
          case IfStmt(guard, thenBranch, _, _) =>
            if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {//no statements - go to a statement after else
              return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(guard), symbolicStore.deepCopy(), callStack.map(identity))
            }
            if (thenBranch.asInstanceOf[NestedBlockStmt].body.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(guard), symbolicStore.deepCopy(), callStack.map(identity))
            }
          case WhileStmt(guard, block, _) =>
            if (block.asInstanceOf[NestedBlockStmt].body.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(guard), symbolicStore.deepCopy(), callStack.map(identity))
            }
          //return new SymbolicState(node, pathCondition, symbolicStore.deepCopy(), callStack.map(identity))//TODO not sure if this is correct
          case _ =>
        }
      }
    )
    throw new Exception("This should not happen")
  }

  override def getIfFalseState(): SymbolicState = {
    val ast = nextStatement.ast;
    ast match {
      case WhileStmt(guard, _, loc) =>
        return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), callStack.map(identity))//TODO add to path condition
      case IfStmt(guard, _, None, loc) =>
        return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), callStack.map(identity))
      case IfStmt(guard, _, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        nextStatement.succ.foreach(
          node => {
            if (elseBranch.isEmpty) {//TODO this should maybe be andled by the parser
              return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), callStack.map(identity))
            }
            if (elseBranch.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), callStack.map(identity))
            }
          }
        )
    }
    throw new Exception("This should not happen")
  }
}

package microc.symbolic_execution

import microc.ast.{AndAnd, BinaryOp, Expr, Identifier, IfStmt, NestedBlockStmt, Not, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.Value.{PointerVal, RefVal, Val}





class SymbolicState(val nextStatement: CfgNode, val pathCondition: Expr, val symbolicStore: SymbolicStore = new SymbolicStore()) {


  def updatedVar(variable: PointerVal, value: Val): SymbolicState = {
    symbolicStore.updateRef(variable, value)
    new SymbolicState(nextStatement, pathCondition, symbolicStore)
  }

  def addedNewVar(variable: String): SymbolicState = {
    symbolicStore.addNewVar(variable)
    val ptr = symbolicStore.storage.getAddress
    symbolicStore.addVar(variable, ptr)
    new SymbolicState(nextStatement, pathCondition, symbolicStore)
  }

  def addedVar(variable: String, v: Val): SymbolicState = {
    val ptr = symbolicStore.storage.getAddress
    symbolicStore.storage.addVal(ptr, v)
    symbolicStore.addVar(variable, ptr)
    new SymbolicState(nextStatement, pathCondition, symbolicStore)
  }

  def nextStates(): Array[SymbolicState] = {
    nextStatement.succ.map { node => new SymbolicState(node, pathCondition, symbolicStore)}.toArray
  }

  def goTo(nextStatement: CfgNode): SymbolicState = {
    new SymbolicState(nextStatement, pathCondition, symbolicStore)
  }

  def getSymbolicVal(name: String): Option[RefVal] = {
    symbolicStore.findVar(name)
  }

  def getSymbolicValForId(id: Identifier): Val = {
    symbolicStore.getValForId(id)
  }

  def getIfTrueState(): SymbolicState = {
    val ast = nextStatement.ast;
    nextStatement.succ.foreach(
      node => {
        ast match {
          case IfStmt(guard, thenBranch, _, loc) =>
            if (thenBranch.asInstanceOf[NestedBlockStmt].body.head == node.ast)
              return new SymbolicState(node, BinaryOp(AndAnd, pathCondition, guard, loc), symbolicStore)
          case WhileStmt(guard, block, loc) =>
            if (block.asInstanceOf[NestedBlockStmt].body.head == node.ast)
              return new SymbolicState(node, BinaryOp(AndAnd, pathCondition, guard, loc), symbolicStore)
          case _ =>
        }
      }
    )
    throw new Exception("This should not happen")
  }

  def getIfFalseState(): SymbolicState = {
    val ast = nextStatement.ast;
    nextStatement.succ.foreach(
      node => {
        ast match {
          case IfStmt(guard, _, Some(NestedBlockStmt(elseBranch, loc)), _) =>
            if (elseBranch.head == node.ast) {
              return new SymbolicState(node, BinaryOp(AndAnd, pathCondition, Not(guard, loc), loc), symbolicStore)
            }
          case _ =>
        }
      }
    )
    new SymbolicState(nextStatement.succ.maxBy(node => node.id), pathCondition, symbolicStore)//TODO add to path condition
  }

}

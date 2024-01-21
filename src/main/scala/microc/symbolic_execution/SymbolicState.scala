package microc.symbolic_execution

import microc.ast.{AndAnd, BinaryOp, CodeLoc, Expr, Identifier, IfStmt, NestedBlockStmt, Not, Number, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.Value.{PointerVal, RefVal, Val}





class SymbolicState(val nextStatement: CfgNode, var pathCondition: PathCondition, val symbolicStore: SymbolicStore = new SymbolicStore()) {

  var returnValue: Val = Number(0, CodeLoc(0, 0))

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

  def nextState(): SymbolicState = {
    new SymbolicState(nextStatement.succ.head, pathCondition, symbolicStore)
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
            if (thenBranch.asInstanceOf[NestedBlockStmt].body.head == node.ast) {
              return new SymbolicState(node, new PathCondition(pathCondition.prev, BinaryOp(AndAnd, pathCondition.expr, guard, loc)), symbolicStore.deepCopy())
            }
          case WhileStmt(guard, block, loc) =>
            if (block.asInstanceOf[NestedBlockStmt].body.head == node.ast)
              return new SymbolicState(node, new PathCondition(pathCondition.prev, BinaryOp(AndAnd, pathCondition.expr, guard, loc)), symbolicStore.deepCopy())
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
              return new SymbolicState(node, new PathCondition(pathCondition.prev, BinaryOp(AndAnd, pathCondition.expr, Not(guard, loc), loc)), symbolicStore.deepCopy())
            }
          case _ =>
        }
      }
    )
    new SymbolicState(nextStatement.succ.maxBy(node => node.id), pathCondition, symbolicStore.deepCopy())//TODO add to path condition
  }

}

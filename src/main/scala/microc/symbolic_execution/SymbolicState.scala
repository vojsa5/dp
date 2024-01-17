package microc.symbolic_execution

import microc.ast.{Expr, Identifier, IfStmt, NestedBlockStmt, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.Value.{PointerVal, RefVal, Symbolic, Val}





class SymbolicState(val nextStatement: CfgNode, val pathCondition: Expr, val symbolicStore: SymbolicStore = new SymbolicStore()) {


  def updatedVar(variable: PointerVal, value: Val): SymbolicState = {
    symbolicStore.updateRef(variable, value)
    new SymbolicState(nextStatement, pathCondition, symbolicStore)
  }

  def addedVar(variable: String): SymbolicState = {
    symbolicStore.addNewVar(variable)
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
          case IfStmt(_, thenBranch, _, _) =>
            if (thenBranch.asInstanceOf[NestedBlockStmt].body.head == node.ast)
              return new SymbolicState(node, pathCondition, symbolicStore)
          case WhileStmt(_, block, _) =>
            if (block.asInstanceOf[NestedBlockStmt].body.head == node.ast)
              return new SymbolicState(node, pathCondition, symbolicStore)
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
          case IfStmt(_, thenBranch, _, _) =>
            if (thenBranch != node.ast)
              return new SymbolicState(node, pathCondition, symbolicStore)
          case WhileStmt(_, block, _) =>
            if (block != node.ast)
              return new SymbolicState(node, pathCondition, symbolicStore)
        }
      }
    )
    throw new Exception("This should not happen")
  }
}

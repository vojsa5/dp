package microc.symbolic_execution

import microc.ast.{AndAnd, BinaryOp, CodeLoc, Equal, Expr, Identifier, IfStmt, NestedBlockStmt, Not, Null, Number, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.Value.{NullRef, PointerVal, RefVal, Symbolic, Val}





class SymbolicState(var nextStatement: CfgNode, var pathCondition: PathCondition, val symbolicStore: SymbolicStore = new SymbolicStore(), var callStack: List[CfgNode] = List.empty) {

  var returnValue: Val = Number(0, CodeLoc(0, 0))

  def updatedVar(variable: PointerVal, value: Val): SymbolicState = {
    symbolicStore.updateRef(variable, value)
    new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack)
  }

  def addedNewVar(variable: String): SymbolicState = {
    //symbolicStore.addNewVar(variable)
    val ptr = symbolicStore.storage.getAddress
    symbolicStore.addVar(variable, ptr)
    new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack)
  }

  def addedVar(variable: String, v: Val): SymbolicState = {
    val ptr = symbolicStore.storage.getAddress
    symbolicStore.storage.addVal(ptr, v)
    symbolicStore.addVar(variable, ptr)
    new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack)
  }

  def addedAlloc(v: Val): PointerVal = {
    val ptr = symbolicStore.storage.getAddress
    symbolicStore.storage.addVal(ptr, v)
    ptr
  }

  def nextStates(): Array[SymbolicState] = {
    nextStatement.succ.map { node => new SymbolicState(node, pathCondition, symbolicStore, callStack)}.toArray
  }

  def nextState(): SymbolicState = {
    new SymbolicState(nextStatement.succ.head, pathCondition, symbolicStore, callStack)
  }

  def goTo(nextStatement: CfgNode): SymbolicState = {
    new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack)
  }

  def getSymbolicVal(name: String): Option[RefVal] = {
    symbolicStore.findVar(name)
  }

  def getVal(ptr: PointerVal): Option[Val] = {
    symbolicStore.getVal(ptr)
  }

  def getSymbolicValForId(id: Identifier): Val = {
    symbolicStore.getValForId(id)
  }

  def loadVariablesToExpr(expr: Expr): Expr = {
    expr match {
      case id@Identifier(name, loc) =>
        getSymbolicValForId(id) match {
          case v: Expr => v
          case _ => throw new Exception("This should not happen")
        }
      case Not(expr, loc) =>
        Not(loadVariablesToExpr(expr), loc)
      case _ =>
        throw new Exception("This should not happen")
    }
  }

  def addToPathCondition(expr: Expr): PathCondition = {
    val pathConditionNewExpr = loadVariablesToExpr(expr)
    pathConditionNewExpr match {
      case Number(value, _) if value == 1 =>
        this.pathCondition
      case BinaryOp(Equal, Number(value1, _), Number(value2, _), _) if value1 == 1 && value2 == 1 =>
        this.pathCondition
      case _ =>
        new PathCondition(pathCondition.prev, BinaryOp(AndAnd, pathCondition.expr, pathConditionNewExpr, expr.loc))

    }
  }

  def getIfTrueState(): SymbolicState = {
    val ast = nextStatement.ast;
    nextStatement.succ.foreach(
      node => {
        ast match {
          case IfStmt(guard, thenBranch, _, _) =>
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

  def getIfFalseState(): SymbolicState = {
    val ast = nextStatement.ast;
    nextStatement.succ.foreach(
      node => {
        ast match {
          case IfStmt(guard, _, Some(NestedBlockStmt(elseBranch, loc)), _) =>
            if (elseBranch.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), callStack.map(identity))
            }
          case _ =>
        }
      }
    )
    new SymbolicState(nextStatement.succ.maxBy(node => node.id), pathCondition, symbolicStore.deepCopy(), callStack.map(identity))//TODO add to path condition
  }

}

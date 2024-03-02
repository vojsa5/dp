package microc.symbolic_execution

import microc.ast.{AndAnd, BinaryOp, CodeLoc, Equal, Expr, Identifier, IdentifierDecl, IfStmt, Loc, NestedBlockStmt, Not, Null, Number, OrOr, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.Value.{NullRef, PointerVal, RefVal, Symbolic, SymbolicExpr, SymbolicVal, UninitializedRef, Val}

import scala.collection.mutable





class SymbolicState(
                     var nextStatement: CfgNode,
                     var pathCondition: PathCondition,
                     var symbolicStore: SymbolicStore,
                     var callStack: List[(CfgNode, List[IdentifierDecl])] = List.empty,
                     var variableDecls: List[IdentifierDecl] = List.empty
                   ) {

  var returnValue: Val = Number(0, CodeLoc(0, 0))

  def deepCopy(): SymbolicState = {
    new SymbolicState(this.nextStatement, this.pathCondition, this.symbolicStore.deepCopy(), this.callStack, this.variableDecls)
  }

  def updatedVar(variable: PointerVal, value: Val): SymbolicState = {
    symbolicStore.updateRef(variable, value)
    new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls)
  }

  def addedNewVar(variable: IdentifierDecl): SymbolicState = {
    symbolicStore.addNewVar(variable.name)
    variableDecls = variableDecls.appended(variable)
    new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls)
  }

  def addedVar(variable: String, v: Val): SymbolicState = {
    val ptr = symbolicStore.addNewVar(variable)
    symbolicStore.storage.addVal(ptr, v)
    new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls)
  }

  def addedAlloc(v: Val): PointerVal = {
    val ptr = symbolicStore.storage.getAddress
    symbolicStore.storage.addVal(ptr, v)
    ptr
  }

  def nextStates(): Array[SymbolicState] = {
    nextStatement.succ.map { node => new SymbolicState(node, pathCondition, symbolicStore, callStack, variableDecls)}.toArray
  }

  def nextState(): SymbolicState = {
    new SymbolicState(nextStatement.succ.head, pathCondition, symbolicStore, callStack, variableDecls)
  }

  def goTo(nextStatement: CfgNode, variableDecls: List[IdentifierDecl]): SymbolicState = {
    new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls)
  }

  def getSymbolicValOpt(name: String): Option[RefVal] = {
    symbolicStore.findVar(name)
  }

  def containsVar(name: String): Boolean = {
    symbolicStore.contains(name)
  }

  def getVal(ptr: PointerVal): Option[Val] = {
    symbolicStore.getValOfPtr(ptr)
  }

  def getSymbolicVal(name: String, loc: Loc, allowReturnNonInitialized: Boolean = false): Val = {
    val res = symbolicStore.getVal(name, loc, allowReturnNonInitialized)
    if (allowReturnNonInitialized) {
      res match {
        case UninitializedRef => return SymbolicVal(CodeLoc(0, 0))
        case _ =>
      }
    }
    res
  }

  def addedLoopTrace(trace: (Expr, mutable.HashMap[String, Expr => Expr])): SymbolicState = {
    new SymbolicState(nextStatement.succ.maxBy(node => node.id), new PathCondition(None, BinaryOp(AndAnd, pathCondition.expr, trace._1, CodeLoc(0, 0))), symbolicStore, callStack, variableDecls)
  }

  def loadVariablesToExpr(expr: Expr): Expr = {
    expr match {
      case Identifier(name, loc) =>
        getSymbolicVal(name, loc) match {
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
//    pathConditionNewExpr match {
//      case Number(value, _) if value == 1 =>
//        this.pathCondition
//      case BinaryOp(Equal, Number(value1, _), Number(value2, _), _) if value1 == 1 && value2 == 1 =>
//        this.pathCondition
//      case _ =>
        new PathCondition(Some(pathCondition), BinaryOp(AndAnd, pathCondition.expr, pathConditionNewExpr, expr.loc))

    //}
  }

  def getIfTrueState(): SymbolicState = {
    val ast = nextStatement.ast;
    nextStatement.succ.foreach(
      node => {
        ast match {
          case IfStmt(guard, thenBranch, _, _) =>
            if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {//no statements - go to a statement after else
                return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(guard), symbolicStore.deepCopy(), callStack.map(identity), variableDecls)
            }
            if (thenBranch.asInstanceOf[NestedBlockStmt].body.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(guard), symbolicStore.deepCopy(), callStack.map(identity), variableDecls)
            }
          case WhileStmt(guard, block, _) =>
            if (block.asInstanceOf[NestedBlockStmt].body.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(guard), symbolicStore.deepCopy(), callStack.map(identity), variableDecls)
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
    ast match {
      case WhileStmt(guard, _, loc) =>
        return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), callStack.map(identity), variableDecls)//TODO add to path condition
      case IfStmt(guard, _, None, loc) =>
        return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), callStack.map(identity), variableDecls)
      case IfStmt(guard, _, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        nextStatement.succ.foreach(
          node => {
            if (elseBranch.isEmpty) {//TODO this should maybe be andled by the parser
              return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), callStack.map(identity), variableDecls)
            }
            if (elseBranch.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), callStack.map(identity), variableDecls)
            }
          }
        )
    }
    throw new Exception("This should not happen")
  }

  def applyChange(changes: mutable.HashMap[String, Expr => Val]): SymbolicState = {
    for (change <- changes) {
      getSymbolicVal(change._1, CodeLoc(0, 0)) match {
        case SymbolicExpr(expr, _) => {
          val newVal = change._2(expr)
          addedVar(change._1, newVal)
        }
        case _ =>
      }
    }
    this
  }

  def stateEquals(other: SymbolicState): Boolean = {
    this.symbolicStore.storeEquals(other.symbolicStore)
  }

  def mergeStates(other: SymbolicState): SymbolicState = {
    new SymbolicState(
      nextStatement,
      new PathCondition(None, BinaryOp(OrOr, this.pathCondition.expr, other.pathCondition.expr, CodeLoc(0, 0))),
      symbolicStore = symbolicStore.mergeStores(other.symbolicStore, pathCondition).get,
      callStack = this.callStack,
      variableDecls = this.variableDecls
    )
  }

}

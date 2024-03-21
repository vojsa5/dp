package microc.symbolic_execution

import microc.ast.{AndAnd, BinaryOp, CodeLoc, Decl, Equal, Expr, Identifier, IdentifierDecl, IfStmt, Loc, NestedBlockStmt, Not, Null, Number, OrOr, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.Value.{NullRef, PointerVal, Symbolic, SymbolicExpr, SymbolicVal, UninitializedRef, Val}

import scala.collection.mutable





class SymbolicState(
                     var nextStatement: CfgNode,
                     var pathCondition: PathCondition,
                     var symbolicStore: SymbolicStore,
                     var callStack: List[(CfgNode, List[IdentifierDecl])] = List.empty,
                     var variableDecls: List[IdentifierDecl] = List.empty
                   ) {

  var returnValue: Option[Val] = None

  def deepCopy(): SymbolicState = {
    new SymbolicState(this.nextStatement, this.pathCondition, this.symbolicStore.deepCopy(), this.callStack, this.variableDecls)
  }

  def updatedVar(variable: PointerVal, value: Val): SymbolicState = {
    symbolicStore.updateRef(variable, value)
    //new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls)
    this
  }

  def addedNewVar(variable: IdentifierDecl): SymbolicState = {
    symbolicStore.addNewVar(variable.name)
    variableDecls = variableDecls.appended(variable)
    //new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls)
    this
  }

  def addedVar(variable: String, v: Val): SymbolicState = {
    val ptr = symbolicStore.addNewVar(variable)
    symbolicStore.storage.addVal(ptr, v)
    //new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls)
    this
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
    nextStatement = nextStatement.succ.head
    this
    //new SymbolicState(nextStatement.succ.head, pathCondition, symbolicStore, callStack, variableDecls)
  }

  def goTo(nextStatement: CfgNode, variableDecls: List[IdentifierDecl]): SymbolicState = {
    this.nextStatement = nextStatement
    this.variableDecls = variableDecls
    this
    //new SymbolicState(nextStatement, pathCondition, symbolicStore, callStack, variableDecls)
  }

  def getSymbolicValOpt(name: String): Option[PointerVal] = {
    symbolicStore.findVar(name)
  }

  def containsVar(name: String): Boolean = {
    symbolicStore.contains(name)
  }

  def getVal(ptr: PointerVal): Option[Val] = {
    symbolicStore.getValOfPtr(ptr)
  }

  def getSymbolicVal(name: String, loc: Loc, allowReturnNonInitialized: Boolean = false): Val = {
    val res = symbolicStore.getVal(name, loc, this, allowReturnNonInitialized)
    if (allowReturnNonInitialized) {
      res match {
        case UninitializedRef => return SymbolicVal(CodeLoc(0, 0))
        case _ =>
      }
    }
    res
  }

  def addedLoopTrace(trace: (Expr, mutable.HashMap[Expr, Expr => Expr])): SymbolicState = {
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
      case BinaryOp(operator, left, right, loc) =>
        BinaryOp(operator, loadVariablesToExpr(left), loadVariablesToExpr(right), loc)
      case n@Number(_, _) => n
      case _ =>
        throw new Exception("This should not happen")
    }
  }

  def addToPathCondition(expr: Expr): PathCondition = {
    val pathConditionNewExpr = loadVariablesToExpr(expr)
    new PathCondition(Some(pathCondition), BinaryOp(AndAnd, pathCondition.expr, pathConditionNewExpr, expr.loc))
  }

  def getIfTrueState(): SymbolicState = {
    val ast = nextStatement.ast;
    nextStatement.succ.foreach(
      node => {
        ast match {
          case IfStmt(guard, thenBranch, _, _) =>
            if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {//no statements - go to a statement after else
                return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
            }
            if (thenBranch.asInstanceOf[NestedBlockStmt].body.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
            }
          case WhileStmt(guard, block, _) =>
            if (block.asInstanceOf[NestedBlockStmt].body.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
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
        return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)//TODO add to path condition
      case IfStmt(guard, _, None, loc) =>
        return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, _, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        nextStatement.succ.foreach(
          node => {
            if (elseBranch.isEmpty) {//TODO this should maybe be andled by the parser
              return new SymbolicState(nextStatement.succ.maxBy(node => node.id), addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
            }
            if (elseBranch.head == node.ast) {
              return new SymbolicState(node, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
            }
          }
        )
    }
    throw new Exception("This should not happen")
  }

  def applyChanges(changes: mutable.HashMap[String, Expr => Val]): SymbolicState = {
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

  def applyChange(varibale: String, change: Expr => Expr): SymbolicState = {
    addedVar(varibale, SymbolicExpr(change.apply(getSymbolicVal(varibale, CodeLoc(0, 0)).asInstanceOf[Symbolic]), CodeLoc(0, 0)))
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

  def copyCallStack(callStack: List[(CfgNode, List[IdentifierDecl])]): List[(CfgNode, List[IdentifierDecl])] = {
    var res = List[(CfgNode, List[IdentifierDecl])]()
    for (fceCall <- callStack) {
      res = res.appended(fceCall)
    }
    res
  }

  def isSimilarTo(other: SymbolicState, limit: Double, variableSolvingCosts: mutable.HashMap[String, Double]): Boolean = {
    val variablesThatDiffers = other.symbolicStore.getDifferentVariables(other.symbolicStore)
    var cost: Double = 0.0
    for (variable <- variablesThatDiffers) {
      cost += variableSolvingCosts.getOrElse(variable, 0.0)
    }
    cost <= limit
  }

}

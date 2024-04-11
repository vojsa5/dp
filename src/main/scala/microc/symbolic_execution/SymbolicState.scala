package microc.symbolic_execution

import microc.ast.{AndAnd, ArrayAccess, BinaryOp, CodeLoc, Decl, Equal, Expr, FieldAccess, Identifier, IdentifierDecl, IfStmt, Input, Loc, NestedBlockStmt, Not, Null, Number, OrOr, RecordField, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.Value.{ArrVal, NullRef, PointerVal, RecVal, Symbolic, SymbolicExpr, SymbolicVal, UninitializedRef, Val}

import scala.collection.mutable





class SymbolicState(
                     var nextStatement: CfgNode,
                     var pathCondition: Expr,
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

  def setMemoryLocation(location: PointerVal, v: Val): Unit = {
    symbolicStore.storage.addVal(location, v)
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

  def getMemoryLoc(expr: Expr): PointerVal = {
    expr match {
      case Identifier(name, _) =>
        symbolicStore.findVar(name).get
      case ArrayAccess(array, index, loc) =>
        symbolicStore.getValOfPtr(getMemoryLoc(array)) match {
          case Some(ArrVal(elems)) =>
            index match {
              case Number(value, _) =>
                elems(value)
              case _ =>
                throw new Exception("IMPLEMENT")
            }
          case _ =>
            throw new Exception("IMPLEMENT")
        }
      case FieldAccess(record, field, loc) =>
        symbolicStore.getValOfPtr(getMemoryLoc(record)) match {
          case Some(RecVal(fields)) =>
            fields(field)
          case _ =>
            throw new Exception("IMPLEMENT")
        }
    }
  }

  def getValAtMemoryLoc(expr: Expr, allowReturnNonInitialized: Boolean = false): Val = {
    symbolicStore.storage.getVal(getMemoryLoc(expr), allowReturnNonInitialized).get
  }

  def containsVar(name: String): Boolean = {
    symbolicStore.contains(name)
  }

  def getVal(ptr: PointerVal): Option[Val] = {
    symbolicStore.getValOfPtr(ptr)
  }

  def getSymbolicVal(name: String, loc: Loc = CodeLoc(0, 0), allowReturnNonInitialized: Boolean = false): Val = {
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
    nextStatement = nextStatement.succ.maxBy(node => node.id)
    pathCondition = BinaryOp(AndAnd, pathCondition, trace._1, CodeLoc(0, 0))
    this
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
      case in@Input(_) => in
      case f@FieldAccess(_, _, _) =>
        getValAtMemoryLoc(f) match {
          case v: Expr => v
          case _ => throw new Exception("This should not happen")
        }
      case a@ArrayAccess(_, _, _) =>
        getValAtMemoryLoc(a) match {
          case v: Expr => v
          case _ => throw new Exception("This should not happen")
        }
      case _ =>
        println(expr)
        throw new Exception("This should not happen")
    }
  }

  def addToPathCondition(expr: Expr): Expr = {
    val pathConditionNewExpr = loadVariablesToExpr(expr)
    BinaryOp(AndAnd, pathCondition, pathConditionNewExpr, expr.loc)
  }


  def getIfTrueState(): SymbolicState = {
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
        new SymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          nextStatement.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          nextStatement.succ.find(s => s.ast == firstThenStatement).get
        }
        new SymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            nextStatement.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
            nextStatement.succ.find(s => s.ast == firstThenStatement).get
          }
          return new SymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
        }
        val next = nextStatement.succ.find(s => s.ast != elseBranch.head).get
        new SymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
    }
  }

  def getIfFalseState(): SymbolicState = {
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
        new SymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          nextStatement.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          nextStatement.succ.find(s => s.ast != firstThenStatement).get
        }
        new SymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            nextStatement.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
            nextStatement.succ.find(s => s.ast != firstThenStatement).get
          }
          return new SymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
        }
        val next = nextStatement.succ.find(s => s.ast == elseBranch.head).get
        new SymbolicState(next, addToPathCondition(Not(guard, loc)), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
    }
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

  def applyChange(memoryLoc: Expr, change: Expr => Expr, mapping: mutable.HashMap[Val, Expr]): SymbolicState = {
    val ptr = getMemoryLoc(memoryLoc)
    val n = SymbolicExpr(change.apply(symbolicStore.getValOfPtr(ptr).get.asInstanceOf[Symbolic]), CodeLoc(0, 0))
    setMemoryLocation(ptr, Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(Utility.replaceWithMapping(n.asInstanceOf[Symbolic], mapping, this), CodeLoc(0, 0))))
    this
  }

  def stateEquals(other: SymbolicState): Boolean = {
    this.symbolicStore.storeEquals(other.symbolicStore)
  }

  def mergeStates(other: SymbolicState): SymbolicState = {
    new SymbolicState(
      nextStatement,
      BinaryOp(OrOr, this.pathCondition, other.pathCondition, CodeLoc(0, 0)),
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

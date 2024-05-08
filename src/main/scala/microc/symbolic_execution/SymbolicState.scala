package microc.symbolic_execution

import microc.ast.{AndAnd, ArrayAccess, ArrayNode, BinaryOp, CodeLoc, Decl, Deref, Equal, Expr, FieldAccess, Identifier, IdentifierDecl, IfStmt, Input, Loc, NestedBlockStmt, Not, Null, Number, OrOr, RecordField, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.ExecutionException.errorArrayOutOfBounds
import microc.symbolic_execution.Value.{ArrVal, IteVal, NullRef, PointerVal, RecVal, Symbolic, SymbolicExpr, SymbolicVal, UninitializedRef, Val}
import microc.symbolic_execution.optimizations.merging.MergedSymbolicState

import scala.collection.mutable





class SymbolicState(
                     var programLocation: CfgNode,
                     var pathCondition: Expr,
                     var symbolicStore: SymbolicStore,
                     var callStack: List[(CfgNode, List[IdentifierDecl])] = List.empty,
                     var variableDecls: List[IdentifierDecl] = List.empty
                   ) {

  var returnValue: Option[Val] = None

  def associatedPathsCount(): Int = {
    1
  }

  def tookToLongToMerge(): Boolean = false

  def deepCopy(): SymbolicState = {
    new SymbolicState(this.programLocation, this.pathCondition, this.symbolicStore.deepCopy(), this.callStack, this.variableDecls)
  }

  def getProgramLocation(): CfgNode = {
    programLocation
  }

  def updateMemoryLocation(variable: PointerVal, value: Val): SymbolicState = {
    symbolicStore.updateRef(variable, value)
    this
  }

  def addVar(variable: IdentifierDecl): SymbolicState = {
    symbolicStore.addNewVar(variable.name)
    variableDecls = variableDecls.appended(variable)
    this
  }

  def updateVar(variable: String, v: Val): SymbolicState = {
    val ptr = symbolicStore.addNewVar(variable)
    symbolicStore.storage.addVal(ptr, v)
    this
  }

  def addVal(v: Val): PointerVal = {
    val ptr = symbolicStore.storage.getAddress
    symbolicStore.storage.addVal(ptr, v)
    ptr
  }

  def step(): SymbolicState = {
    programLocation = programLocation.succ.head
    this
  }

  def goTo(nextStatement: CfgNode, variableDecls: List[IdentifierDecl]): SymbolicState = {
    this.programLocation = nextStatement
    this.variableDecls = variableDecls
    this
  }

  def getSymbolicValOpt(name: String): Option[PointerVal] = {
    symbolicStore.findVar(name)
  }

  def getMemoryLoc(expr: Expr): PointerVal = {
    expr match {
      case Identifier(name, _) =>
        symbolicStore.findVar(name).get
      case Deref(pointer, loc) =>
        symbolicStore.getValOfPtr(getMemoryLoc(pointer)) match {
          case Some(p: PointerVal) =>
            p
          case _ => throw new Exception("this should never happen.")
        }
      case ArrayAccess(array, index, loc) =>
        symbolicStore.getValOfPtr(getMemoryLoc(array)) match {
          case Some(ArrVal(elems)) =>
            index match {
              case Number(value, _) =>
                if (value >= elems.length) {
                  throw errorArrayOutOfBounds(loc, elems.length, value, this)
                }
                elems(value)
              case _ =>
                throw new Exception("this should never happen")
            }
          case _ =>
            throw new Exception("this should never happen")
        }
      case FieldAccess(record, field, loc) =>
        symbolicStore.getValOfPtr(getMemoryLoc(record)) match {
          case Some(RecVal(fields)) =>
            fields(field)
          case _ =>
            throw new Exception("this should never happen")
        }
      case _ =>
        throw new Exception("this should never happen")
    }
  }

  def getValAtMemoryLoc(expr: Expr, allowReturnNonInitialized: Boolean = false): Val = {
    symbolicStore.storage.getVal(getMemoryLoc(expr), allowReturnNonInitialized).get
  }

  def containsVar(name: String): Boolean = {
    symbolicStore.contains(name)
  }

  def getValOnMemoryLocation(ptr: PointerVal, allowReturnNonInitialized: Boolean = false): Option[Val] = {
    symbolicStore.getValOfPtr(ptr, allowReturnNonInitialized)
  }

  def getValueOfVar(name: String, loc: Loc = CodeLoc(0, 0), allowReturnNonInitialized: Boolean = false): Val = {
    val res = symbolicStore.getVal(name, loc, this, allowReturnNonInitialized)
    if (allowReturnNonInitialized) {
      res match {
        case UninitializedRef => return SymbolicVal(CodeLoc(0, 0))
        case _ =>
      }
    }
    res
  }

  def addLoopTrace(trace: (Expr, mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr], mutable.HashSet[Expr])): SymbolicState = {
    if (programLocation.succ.nonEmpty) {
      programLocation = programLocation.succ.maxBy(node => node.id)
      pathCondition = BinaryOp(AndAnd, pathCondition, trace._1, CodeLoc(0, 0))
    }
    this
  }

  def loadVariablesToExpr(expr: Expr): Expr = {
    expr match {
      case Identifier(name, loc) =>
        getValueOfVar(name, loc) match {
          case v: Expr => v
          case _ => throw new Exception("This should not happen")
        }
      case Not(expr, loc) =>
        Not(loadVariablesToExpr(expr), loc)
      case BinaryOp(operator, left, right, loc) =>
        BinaryOp(operator, loadVariablesToExpr(left), loadVariablesToExpr(right), loc)
      case n@Number(_, _) => n
      case in@Input(_) => in
      case d@Deref(_, _) =>
        getValAtMemoryLoc(d) match {
          case v: Expr => v
          case _ => throw new Exception("This should not happen")
        }
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
    val pathConditionNewExpr = Utility.removeIteVal(loadVariablesToExpr(expr), this)
    Utility.simplifyArithExpr(BinaryOp(AndAnd, pathCondition, pathConditionNewExpr, expr.loc))
  }


  def getIfTrueState(): SymbolicState = {
    val ast = programLocation.ast;
    ast match {
      case WhileStmt(guard, thenBranch, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          if (!programLocation.succ.exists(s => s.ast == ast)) {
            programLocation.succ.find(s => s.id - programLocation.id == 0.5).get
          }
          else {
            programLocation.succ.find(s => s.ast == ast).get
          }
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          programLocation.succ.find(s => s.ast == firstThenStatement).get
        }
        new SymbolicState(next, addToPathCondition(guard), symbolicStore.deepCopy(), copyCallStack(callStack), variableDecls)
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          programLocation.succ.head
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
    }
  }

  def getIfFalseState(): SymbolicState = {
    val ast = programLocation.ast;
    ast match {
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
          programLocation.succ.head
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
    }
  }

  def applyChanges(changes: mutable.HashMap[String, Expr => Val]): SymbolicState = {
    for (change <- changes) {
      getValueOfVar(change._1, CodeLoc(0, 0)) match {
        case SymbolicExpr(expr, _) => {
          val newVal = change._2(expr)
          updateVar(change._1, newVal)
        }
        case _ =>
      }
    }
    this
  }

  def applyChange(memoryLoc: Expr, change: Expr => SymbolicState => Expr, mapping: mutable.HashMap[Val, Expr]): SymbolicState = {
    val ptr = getMemoryLoc(memoryLoc)
    val n = SymbolicExpr(change.apply(symbolicStore.getValOfPtr(ptr, true).get.asInstanceOf[Symbolic]).apply(this), CodeLoc(0, 0))
    updateMemoryLocation(ptr, Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(Utility.replaceWithMapping(n.asInstanceOf[Symbolic], mapping, this), CodeLoc(0, 0))))
    this
  }

  def stateEquals(other: SymbolicState): Boolean = {
    this.symbolicStore.storeEquals(other.symbolicStore)
  }

  def mergeStates(other: SymbolicState): SymbolicState = {
    val start = System.currentTimeMillis()
    val (symbolicStore, expr) = this.symbolicStore.mergeStores(other.symbolicStore, pathCondition, other.pathCondition).get
    val end = System.currentTimeMillis()
    val res = new MergedSymbolicState(
      programLocation,
      expr,
      symbolicStore,
      callStack = this.callStack,
      variableDecls = this.variableDecls,
      (this, other)
    )
    if (end - start > 50) {
      res.tookTooLongToMerge = true
    }
    res
  }

  def copyCallStack(callStack: List[(CfgNode, List[IdentifierDecl])]): List[(CfgNode, List[IdentifierDecl])] = {
    var res = List[(CfgNode, List[IdentifierDecl])]()
    for (fceCall <- callStack) {
      res = res.appended(fceCall)
    }
    res
  }

  def isSimilarTo(other: SymbolicState, limit: Double, variableSolvingCosts: mutable.HashMap[String, Double]): Boolean = {
    val variablesThatDiffers = symbolicStore.getDifferentVariables(other.symbolicStore)
    var cost: Double = 0.0
    for (variable <- variablesThatDiffers) {
      cost += variableSolvingCosts.getOrElse(variable, 0.0)
    }
    cost < limit
  }

}

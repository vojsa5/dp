package microc.symbolic_execution

import microc.symbolic_execution.Statistics
import microc.ProgramException
import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, AstNode, BinaryOp, BinaryOperator, CallFuncExpr, CodeLoc, Deref, Divide, Equal, Expr, FieldAccess, FunDecl, GreaterEqual, GreaterThan, Identifier, IdentifierDecl, IfStmt, Input, Loc, LowerEqual, LowerThan, Minus, NestedBlockStmt, Not, NotEqual, Null, Number, OrOr, OutputStmt, Plus, Program, Record, ReturnStmt, StmtInNestedBlock, Times, VarRef, VarStmt, WhileStmt}
import microc.cfg.{CfgNode, CfgStmtNode, ProgramCfg}
import microc.cli.Reporter
import microc.symbolic_execution.ExecutionException.{errorArrayOutOfBounds, errorDivByZero, errorIncompatibleTypes, errorNonArrayAccess, errorNonExistingFieldAccess, errorNonFunctionApplication, errorNonIntArithmetics, errorNonIntReturn, errorNonPointerDereference, errorNonRecordFieldAccess, errorNotAssignableExpression, errorNullDereference, errorRecordNestedFields, errorUninitializedReference}
import microc.symbolic_execution.Value.{ArrVal, FunVal, IteVal, NullRef, PointerVal, RecVal, Symbolic, SymbolicExpr, SymbolicVal, Val}
import com.microsoft.z3._

import scala.collection.mutable

case class ExecutionException(message: String, loc: Loc, symbolicState: SymbolicState) extends ProgramException(message + "\nloc: " + symbolicState.nextStatement.ast) {
  override def format(reporter: Reporter): String = reporter.formatError("execution", message + " loc: " + symbolicState.nextStatement.ast, loc)
}

object ExecutionException {
  def errorMissingMainFunction(program: Program, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Missing main function, declared functions are ${program.funs.map(_.name)}", program.loc, symbolicState)

  def errorNonRecordFieldAccess(loc: Loc, value: String, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-record ($value) field access", loc, symbolicState)

  def errorNonExistingFieldAccess(loc: Loc, rec: String, field: String, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-existing field ($field) access in $rec", loc, symbolicState)

  def errorNullDereference(loc: Loc, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Null-pointer pointer dereference", loc, symbolicState)

  def errorNonPointerDereference(loc: Loc, value: String, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-pointer ($value) pointer dereference", loc, symbolicState)

  def errorNonIntCondition(loc: Loc, value: String, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-integer ($value) condition guard", loc, symbolicState)

  def errorNonIntReturn(fun: FunDecl, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-integer return from function ${fun.name}", fun.block.ret.expr.loc, symbolicState)

  def errorNonIntOutput(loc: Loc, value: String, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-integer ($value) output", loc, symbolicState)

  def errorNonIntInput(loc: Loc, value: String, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-integer ($value) input", loc, symbolicState)

  def errorNonIntArithmetics(loc: Loc, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-integer arithmetic operation", loc, symbolicState)

  def errorUninitializedReference(loc: Loc, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Uninitialized variable", loc, symbolicState)

  def errorNonFunctionApplication(loc: Loc, value: String, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-function ($value) application", loc, symbolicState)

  def errorRecordNestedFields(loc: Loc, symbolicState: SymbolicState): ExecutionException =
    ExecutionException("Nested records are not supported, use pointers", loc, symbolicState)

  def errorNotAssignableExpression(expr: Expr, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Expression is not assignable ($expr)", expr.loc, symbolicState)

  def errorInvalidArgumentList(loc: Loc, fun: FunDecl, actual: Int, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Invalid argument list: expected ${fun.params.size}, got: $actual", loc, symbolicState)

  def errorDivByZero(loc: Loc, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Division by zero", loc, symbolicState)

  def errorIncompatibleTypes(loc: Loc, left: String, right: String, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Incompatible types, cannot assign $right into $left", loc, symbolicState)

  def errorArrayOutOfBounds(loc: Loc, length: Int, index: Int, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Array out of bounds (length: $length, index: $index)", loc, symbolicState)

  def errorArrayOutOfBounds(loc: Loc, length: Int, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Array out of bounds (length: $length, index symbolic)", loc, symbolicState)

  def errorNonArrayAccess(loc: Loc, value: String, symbolicState: SymbolicState): ExecutionException =
    ExecutionException(s"Non-array ($value) element access", loc, symbolicState)


}


class SymbolicExecutor(program: ProgramCfg,
                       subsumption: Option[PathSubsumption] = None,
                       ctx: Context = new Context(),
                       searchStrategy: SearchStrategy = new BFSSearchStrategy,
                       stateHistory: Option[StateHistory] = None,
                       covered: Option[mutable.HashSet[CfgNode]] = None,
                       printStats: Boolean = true
                      ) {

  val solver = new ConstraintSolver(ctx)
  var statistics = new Statistics()
  var currentPathStopped = false
  private var functionDeclarations: Map[String, FunVal] = Map.empty
  var loops: mutable.HashMap[CfgNode, Identifier] = mutable.HashMap.empty
  var subsumptionLoopVar = 1
  var inSubsumptionIteration = false

  def createSubsumptionLoopVar(): Identifier = {
    val rightSide = Identifier("_l" + subsumptionLoopVar.toString, CodeLoc(0, 0))
    subsumptionLoopVar += 1
    rightSide
  }


  for (fun <- program.function) {
    val fceName = fun.ast.asInstanceOf[FunDecl].name
    if (fun.ast.asInstanceOf[FunDecl].name != "main") {
      functionDeclarations = functionDeclarations.updated(fceName, FunVal(fun.ast.asInstanceOf[FunDecl]))
    }
  }



  def run(): Int = {
    val initialState = new SymbolicState(program.getFce("main"), PathCondition.initial(), new SymbolicStore(functionDeclarations))
    stateHistory match {
      case Some(history) =>
        history.initial = initialState
      case None =>
    }
    searchStrategy.addState(initialState)
    var res: Option[Val] = None
    while (searchStrategy.statesCount() != 0) {
      if (printStats) {
        statistics.printStats()
      }
      var path = searchStrategy.getState()
      currentPathStopped = false
      step(path)
      while (path.callStack.nonEmpty && !currentPathStopped) {
        val lastFceCall = path.callStack.last
        path.symbolicStore.popFrame()
        // in the normalized ast, all function calls are in the form of assignments
        lastFceCall._1.ast match {
          case AssignStmt(target, _, _) =>
            getTarget(target, path) match {
              case Some(value) =>
                path.updatedVar(value, path.returnValue.get)
              case None =>
                throw new Exception("evert function whould return a number")
            }

          case _ =>
            throw new Exception("this should never happen")
        }
        path.callStack = path.callStack.dropRight(1)
        path = path.goTo(lastFceCall._1.succ.head, lastFceCall._2)
        step(path)
      }

      statistics.numPaths += 1
      if (path.returnValue.nonEmpty) {
        res = path.returnValue
      }
    }

    if (res.isEmpty) {//TODO look at this
      return 0
    }
    res.get match {//TODO handle returning non number better
      case Number(value, _) =>
        value
      case i: IteVal =>
        0
      case e: SymbolicExpr =>
        0
      case e: SymbolicVal =>
        0
      case _ =>
        throw errorNonIntReturn(program.getFce("main").ast.asInstanceOf[FunDecl], initialState)
    }
  }

  def runFunction(name: String, symbolicState: SymbolicState, args: List[Expr]): Option[Val] = {
    val fce = program.getFce(name)
    symbolicState.callStack = symbolicState.callStack.appended((symbolicState.nextStatement, fce.ast.asInstanceOf[FunDecl].params))
    symbolicState.symbolicStore.pushFrame()
    val tmpNextStatement = symbolicState.nextStatement
    for ((arg, param) <- args.zip(fce.ast.asInstanceOf[FunDecl].params)) {
      symbolicState.addedVar(param.name, evaluate(arg, symbolicState))
    }
    val fceState = symbolicState.goTo(fce, fce.fun.params)
    step(fceState)
    symbolicState.returnValue = fceState.returnValue
    symbolicState.pathCondition = fceState.pathCondition
    symbolicState.symbolicStore = fceState.symbolicStore
    symbolicState.symbolicStore.popFrame()
    symbolicState.callStack = symbolicState.callStack.dropRight(1)
    symbolicState.nextStatement = tmpNextStatement
    symbolicState.returnValue
  }

  def stepOnAssign(assignStmt: AssignStmt, symbolicState: SymbolicState): Unit = {
    assignStmt match {
      case AssignStmt(FieldAccess(record, field, loc), right, _) =>
        val assigned = evaluate(right, symbolicState)
        evaluate(record, symbolicState) match {
          case RecVal(fields) if fields.contains(field) => symbolicState.updatedVar(fields(field), assigned)
          case RecVal(fields) =>
            throw errorNonExistingFieldAccess(loc, RecVal(fields).toString, field, symbolicState)
          case IteVal(RecVal(fields1), RecVal(fields2), _, _) if fields1.contains(field) && fields2.contains(field) => {
            symbolicState.updatedVar(fields1(field), assigned)
            symbolicState.updatedVar(fields2(field), assigned)
          }
          case _ =>
            throw errorNotAssignableExpression(record, symbolicState: SymbolicState)
        }
      case AssignStmt(lhs, rhs, _) =>
        getTarget(lhs, symbolicState) match {
          case None =>
            currentPathStopped = true
          case Some(inner) =>
            symbolicState.updatedVar(inner, evaluate(rhs, symbolicState))
        }
    }
  }

  def stepOnLoop(symbolicState: SymbolicState): Unit = {
    val loop: CfgNode = symbolicState.nextStatement
    val loopAst = loop.ast.asInstanceOf[WhileStmt]
    if (subsumption.nonEmpty) {
      if (!loops.contains(loop)) {
        val loopIter = createSubsumptionLoopVar()
        loops.put(loop, loopIter)
        solver.solveCondition(symbolicState.pathCondition.expr, loopAst.guard, symbolicState) match {
          case Status.SATISFIABLE | Status.UNKNOWN =>
            val nextState = symbolicState.getIfTrueState()
            var goOutOfSubsumptionIteration = false
            if (!inSubsumptionIteration) {
              inSubsumptionIteration = true
              goOutOfSubsumptionIteration = true
            }
            val loopIterCond = BinaryOp(LowerThan, loopIter, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0))
            val lastLoopStmt = loop.pred.maxBy(node => node.id)
            subsumption.get.addAnnotationsToALoop(program.nodes.filter(node => node.id > loop.id && node.id <= lastLoopStmt.id).toList, loopIterCond)
            //subsumption.get.addAnnotation(loop, loopIterCond)
            val decreaseLoopIter = AssignStmt(loopIter, BinaryOp(Minus, loopIter, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0))
            val lastBody = loopAst.block.asInstanceOf[NestedBlockStmt].body
            val body = lastBody.appended(decreaseLoopIter)
            loop.ast = WhileStmt(loopAst.guard, NestedBlockStmt(body, loopAst.block.loc), loopAst.loc)

            val newStmt = new CfgStmtNode(lastLoopStmt.id + 0.5, decreaseLoopIter)

            lastLoopStmt.succ.remove(loop)
            lastLoopStmt.succ.add(newStmt)
            loop.pred.remove(lastLoopStmt)
            loop.pred.add(newStmt)
            newStmt.succ.add(loop)
            newStmt.pred.add(lastLoopStmt)

            nextState.addedVar(loops(loop).name, Number(0, CodeLoc(0, 0)))

            step(nextState)

            subsumption.get.replaceSubsumptionIdentifier(
              program.nodes.filter(node => node.id >= loop.id && node.id <= newStmt.id).toList,
              loopIter,
              Number(0, CodeLoc(0, 0))
            )

//            lastLoopStmt.succ.clear()
//            lastLoopStmt.succ.addAll(tmpSuccs)
//            lastLoopStmt.succ.foreach(s => {
//              s.pred.remove(newStmt)
//              s.pred.add(lastLoopStmt)
//              newStmt.succ.add(s)
//            })

            lastLoopStmt.succ.add(loop)
            lastLoopStmt.succ.remove(newStmt)
            loop.pred.add(lastLoopStmt)
            loop.pred.remove(newStmt)


//            symbolicState.pathCondition = nextState.pathCondition.prev.get
            symbolicState.returnValue = nextState.returnValue
//            symbolicState.symbolicStore = nextState.symbolicStore

            loop.ast = loopAst

            subsumption.get.computeAnnotation(symbolicState.nextStatement, true)
            if (subsumption.get.checkSubsumption(symbolicState)) {
              statistics.stoppedWithSubsumption += 1
              currentPathStopped = true
              return
            }

            if (goOutOfSubsumptionIteration) {
              inSubsumptionIteration = false
            }
            else {
              null
            }

          case Status.UNSATISFIABLE =>//TODO look at this
            subsumption.get.computeAnnotation(symbolicState.nextStatement)
        }
      }
    }
    var whileLeavingState: Option[SymbolicState] = None
    solver.solveCondition(symbolicState.pathCondition.expr, Not(loopAst.guard, loopAst.guard.loc), symbolicState) match {
      case Status.SATISFIABLE | Status.UNKNOWN =>
        val nextState = symbolicState.getIfFalseState()
        //searchStrategy.addState(nextState)
        if (stateHistory.nonEmpty) {
          stateHistory.get.addNode(symbolicState, nextState)
        }
        step(nextState)
        whileLeavingState = Some(nextState)
      case Status.UNSATISFIABLE =>
        currentPathStopped = true
    }
    if (subsumption.isEmpty) {
      solver.solveCondition(symbolicState.pathCondition.expr, loopAst.guard, symbolicState) match {
        case Status.SATISFIABLE | Status.UNKNOWN =>
          val nextState = symbolicState.getIfTrueState()
          //        if (inSubsumptionIteration) {
          //          statistics.numPaths += 1
          //          step(nextState)
          //        }
          searchStrategy.addState(nextState)

          if (stateHistory.nonEmpty) {
            stateHistory.get.addState(symbolicState, nextState)
          }

        case Status.UNSATISFIABLE =>
      }
    }
    if (subsumption.nonEmpty) {
      subsumption.get.computeAnnotation(symbolicState.nextStatement)
    }
    if (whileLeavingState.nonEmpty) {
      symbolicState.pathCondition = whileLeavingState.get.pathCondition.prev.get
      symbolicState.returnValue = whileLeavingState.get.returnValue
      symbolicState.symbolicStore = whileLeavingState.get.symbolicStore
    }
  }

  def step(symbolicState: SymbolicState): Unit = {
    if (covered.nonEmpty) {
      covered.get.add(symbolicState.nextStatement)
    }
    val statement = symbolicState.nextStatement
    val ast = symbolicState.nextStatement.ast
    println(statement)
    if (subsumption.nonEmpty) {
      if (subsumption.get.checkSubsumption(symbolicState)) {
        statistics.stoppedWithSubsumption += 1
        return
      }
    }
    val newStateOpt = evaluateStatement(ast, symbolicState)
    newStateOpt match {
      case Some(_) =>
      case None => return
    }
    val newState = newStateOpt.get
    if (currentPathStopped) {
      return
    }
    val nextState = newState.nextState()
    step(nextState)
    if (subsumption.nonEmpty) {
      ast match {
        case stmt: AssignStmt if Utility.statementCanCauseError(stmt) =>
          println("KKKKKKKK", statement.id)
        case _ =>
          subsumption.get.computeAnnotation(statement)
      }
    }
    //symbolicState.returnValue = nextState.returnValue
    //symbolicState.symbolicStore = nextState.symbolicStore//TODO maybe comment this???
  }


  def evaluateStatement(ast: AstNode, symbolicState: SymbolicState): Option[SymbolicState] = {
    var newState = symbolicState
    ast match {
      case FunDecl(_, _, _, _) =>
      case VarStmt(decls, _) =>
        newState = decls.foldLeft(symbolicState) {
          (state, decl) =>
            state.addedNewVar(decl)
        }
      case a@AssignStmt(_, _, _) =>
        stepOnAssign(a, symbolicState)
      case IfStmt(guard, _, _, _) =>
        var ifState: Option[SymbolicState] = None
        solver.solveCondition(symbolicState.pathCondition.expr, guard, symbolicState) match {
          case Status.SATISFIABLE | Status.UNKNOWN =>
            val nextState = symbolicState.getIfTrueState()
            if (stateHistory.nonEmpty) {
              stateHistory.get.addNode(symbolicState, nextState)
            }
            step(nextState)
            ifState = Some(nextState)
          case Status.UNSATISFIABLE =>
            currentPathStopped = true
        }

        solver.solveCondition(symbolicState.pathCondition.expr, Not(guard, guard.loc), symbolicState) match {
          case Status.SATISFIABLE | Status.UNKNOWN =>
            val path = symbolicState.getIfFalseState()
            if (stateHistory.nonEmpty) {
              stateHistory.get.addState(symbolicState, path)
            }
            if (subsumption.nonEmpty) {
              currentPathStopped = false
              step(path)
              subsumption.get.computeAnnotation(symbolicState.nextStatement)
              statistics.numPaths += 1
            }
            else {
              searchStrategy.addState(path)
            }
          case Status.UNSATISFIABLE =>
            if (subsumption.nonEmpty) {
              subsumption.get.computeAnnotation(symbolicState.nextStatement)
            }
        }
        if (ifState.nonEmpty) {
          symbolicState.pathCondition = ifState.get.pathCondition
          //symbolicState.pathCondition = ifState.get.pathCondition.prev.get
          symbolicState.returnValue = ifState.get.returnValue
          symbolicState.symbolicStore = ifState.get.symbolicStore
        }
        return None
      case loop@WhileStmt(_, _, _) =>
        stepOnLoop(symbolicState)
        return None
      case ReturnStmt(expr, _) =>
        symbolicState.returnValue = Some(evaluate(expr, symbolicState))
        if (subsumption.nonEmpty) {
          subsumption.get.addAnnotation(symbolicState.nextStatement, Number(1, CodeLoc(0, 0)))
        }
        return None
      case OutputStmt(expr, _) =>
        evaluate(expr, symbolicState)
    }
    Some(newState)
  }


  private def compareValues(operator: BinaryOperator, val1: Val, val2: Val, symbolicState: SymbolicState, loc: Loc): Val = {
    (val1, val2) match {
      case (Number(l, _), Number(r, _)) =>
        operator match {
          case Plus => Number(l + r, loc)
          case Minus => Number(l - r, loc)
          case Times => Number(l * r, loc)
          case Divide =>
            if (r == 0) {
              throw errorDivByZero(loc, symbolicState)
            }
            Number(l / r, loc)
          case Equal => Number(if (l == r) 1 else 0, loc)
          case NotEqual => Number(if (l != r) 1 else 0, loc)
          case GreaterThan => Number(if (l > r) 1 else 0, loc)
          case GreaterEqual => Number(if (l >= r) 1 else 0, loc)
          case LowerThan => Number(if (l < r) 1 else 0, loc)
          case LowerEqual => Number(if (l <= r) 1 else 0, loc)
          case AndAnd => Number(if (l != 0 && r != 0) 1 else 0, loc)
          case OrOr => Number(if (l != 0 || r != 0) 1 else 0, loc)
        }

      case (e1: Symbolic, e2: Symbolic) =>
        operator match {
          case Plus => SymbolicExpr(BinaryOp(Plus, e1, e2, loc), loc)
          case Minus => SymbolicExpr(BinaryOp(Minus, e1, e2, loc), loc)
          case Times => SymbolicExpr(BinaryOp(Times, e1, e2, loc), loc)
          case Divide => {
            e2 match {
              case Number(v, _) =>
                if (v == 0) {
                  throw errorDivByZero(loc, symbolicState)
                }
                SymbolicExpr(BinaryOp(Divide, e1, e2, loc), loc)
              case _ =>
                solver.solveConstraint(
                  solver.createConstraintWithState(BinaryOp(AndAnd, BinaryOp(Equal, e2, Number(0, loc), loc), symbolicState.pathCondition.expr, loc), symbolicState)) match {
                  case Status.SATISFIABLE =>
                    throw errorDivByZero(loc, symbolicState)
                  case Status.UNSATISFIABLE => SymbolicExpr(BinaryOp(Divide, e1, e2, loc), loc)
                  case Status.UNKNOWN => throw new Exception("IMPLEMENT")
                }
            }

          }
          case Equal =>
            SymbolicExpr(BinaryOp(Equal, e1, e2, loc), loc)
          case NotEqual => SymbolicExpr(BinaryOp(NotEqual, e1, e2, loc), loc)
          case GreaterThan => SymbolicExpr(BinaryOp(GreaterThan, e1, e2, loc), loc)
          case GreaterEqual => SymbolicExpr(BinaryOp(GreaterEqual, e1, e2, loc), loc)
          case LowerThan => SymbolicExpr(BinaryOp(LowerThan, e1, e2, loc), loc)
          case LowerEqual => SymbolicExpr(BinaryOp(LowerEqual, e1, e2, loc), loc)
          case AndAnd => SymbolicExpr(BinaryOp(AndAnd, e1, e2, loc), loc)
          case OrOr => SymbolicExpr(BinaryOp(OrOr, e1, e2, loc), loc)
        }
      case (NullRef, NullRef) => Number(1, loc)
      case (PointerVal(address1), PointerVal(address2)) => if (address1 == address2) Number(1, loc) else Number(0, loc)
      case (PointerVal(_), NullRef) => Number(0, loc)
      case (NullRef, PointerVal(_)) => Number(0, loc)
      case (IteVal(trueState, falseState, expr, loc), other) =>
        IteVal(
          compareValues(operator, trueState, other, symbolicState, loc),
          compareValues(operator, falseState, other, symbolicState, loc),
          expr,
          loc
        )
      case (other, IteVal(trueState, falseState, expr, loc)) =>
        IteVal(
          compareValues(operator, trueState, other, symbolicState, loc),
          compareValues(operator, falseState, other, symbolicState, loc),
          expr,
          loc
        )
      case _ =>
        throw errorNonIntArithmetics(loc, symbolicState)
    }
  }

  def loadArray(arr: ArrayNode, symbolicState: SymbolicState): ArrVal = {
    var prev: Val = null
    val elems = arr.elems
    val vals = elems.map { e =>
      val v = evaluate(e, symbolicState)
      if (prev != null && !prev.getClass.isAssignableFrom(v.getClass)) {
        throw errorIncompatibleTypes(e.loc, prev.toString, v.toString, symbolicState)
      }
      else {
        prev = v
      }
      symbolicState.addedAlloc(v)
    }.toArray
    ArrVal(vals)
  }

  def evaluate(expr: Expr, symbolicState: SymbolicState): Val = {
    expr match {
      case BinaryOp(operator, left, right, loc) =>
        (operator, evaluate(left, symbolicState), evaluate(right, symbolicState)) match {
          case (Equal, NullRef, NullRef) => Number(1, loc)
          case (Equal, PointerVal(address1), PointerVal(address2)) => if (address1.equals(address2)) Number(1, loc) else Number(0, loc)
          case (Equal, PointerVal(_), NullRef) => Number(0, loc)
          case (Equal, NullRef, PointerVal(_)) => Number(0, loc)
          case (op, val1, val2) => compareValues(op, val1, val2, symbolicState, loc)
        }
      case Not(expr, loc) =>
        evaluate(expr, symbolicState) match {
          case Number(value, _) => Number(if (value == 0) 1 else 0, loc)
          case v@SymbolicVal(_) => SymbolicExpr(Not(v, loc), loc)
          case SymbolicExpr(value, _) => SymbolicExpr(Not(value, loc), loc)
          case _ => throw errorNonIntArithmetics(loc, symbolicState)
        }
      case Number(value, loc) => Number(value, loc)
      case id@Identifier(_, _) =>
        symbolicState.getSymbolicVal(id.name, id.loc)
      case Input(loc) =>
        SymbolicVal(loc)
      case CallFuncExpr(targetFun, args, loc) =>
        targetFun match {
          case Identifier(name, _) => {
            runFunction(name, symbolicState, args) match {
              case Some(res) => res
              case None => {
                symbolicState.returnValue = None
                Number(0, CodeLoc(0, 0))
              }
            }
          }
          case _ => throw errorNonFunctionApplication(loc, targetFun.toString, symbolicState)
        }
      case VarRef(id, _) =>
        symbolicState.getSymbolicValOpt(id.name).get
      case Null(_) => NullRef
      case Alloc(expr, _) =>
        symbolicState.addedAlloc(evaluate(expr, symbolicState))
      case Deref(pointer, loc) =>
        evaluate(pointer, symbolicState) match {
          case PointerVal(address) =>
            symbolicState.getVal(PointerVal(address)).get
          case NullRef =>
            throw errorNullDereference(loc, symbolicState)
          case IteVal(trueState: PointerVal, falseState: PointerVal, expr, loc) =>
            IteVal(symbolicState.getVal(trueState).get, symbolicState.getVal(falseState).get, expr, loc)
          case IteVal(trueState, falseState, expr, loc) if falseState == NullRef || trueState == NullRef =>
            throw errorNullDereference(loc, symbolicState)
          case e =>
            throw errorNonPointerDereference(loc, e.toString, symbolicState)
        }
      case a@ArrayNode(_, _) =>
        loadArray(a, symbolicState)
      case ArrayAccess(array, index, loc) =>
        evaluate(array, symbolicState) match {
          case ArrVal(elems) => {
            evaluate(index, symbolicState) match {
              case Number(value, _) =>
                if (value >= elems.length || value < 0) {
                  throw errorArrayOutOfBounds(loc, elems.length, value, symbolicState)
                }
                symbolicState.getVal(elems(value)) match {
                  case Some(v) => v
                  case None =>
                    throw errorUninitializedReference(loc, symbolicState)
                }
              case s: Symbolic =>
                solver.solveConstraint(
                  solver.createConstraintWithState(
                    BinaryOp(
                      OrOr,
                      BinaryOp(AndAnd, BinaryOp(LowerThan, s, Number(0, loc), loc), symbolicState.pathCondition.expr, loc),
                      BinaryOp(AndAnd, BinaryOp(GreaterEqual, s, Number(elems.length, loc), loc), symbolicState.pathCondition.expr, loc),
                      loc)
                    , symbolicState)) match {
                  case Status.SATISFIABLE =>
                    throw errorArrayOutOfBounds(loc, elems.length, symbolicState)
                  case Status.UNSATISFIABLE | Status.UNKNOWN =>
                    for (i <- elems.indices) {
                      solver.solveConstraint(
                        solver.createConstraintWithState(BinaryOp(Equal, s, Number(i, CodeLoc(0, 0)), loc), symbolicState)) match {
                          case Status.SATISFIABLE =>
                            val newState = symbolicState.deepCopy()
                            getTarget(index, newState) match {
                              case Some(ptr) =>
                                newState.updatedVar(ptr, Number(i, CodeLoc(0, 0)))
                              case None =>
                                throw new Exception("this should never happen.")
                            }
                            if (subsumption.nonEmpty) {
                              //TODO take return value???
                              step(newState)
                            }
                            else {
                              searchStrategy.addState(newState)
                            }
                            if (stateHistory.nonEmpty) {
                              stateHistory.get.addState(symbolicState, newState)
                            }
                          case _ =>
                      }
                    }
                    currentPathStopped = true
                    symbolicState.returnValue = None
                    Number(0, CodeLoc(0, 0))
                }
              case _ => throw errorNonIntArithmetics(loc, symbolicState)
            }
          }
          case _ =>
            throw errorNonArrayAccess(loc, evaluate(array, symbolicState).toString, symbolicState)
        }
      case Record(fields, loc) =>
        val fieldsMap: mutable.HashMap[String, PointerVal] = mutable.HashMap.empty
        fields.foreach(field =>
          evaluate(field.expr, symbolicState) match {
            case RecVal(_) => throw errorRecordNestedFields(field.expr.loc, symbolicState)
            case res =>
              symbolicState.addedVar(field.name, res)
              fieldsMap.update(field.name, symbolicState.getSymbolicValOpt(field.name).get)
          }
        )
        RecVal(fieldsMap)
      case FieldAccess(record, field, loc) =>
        evaluate(record, symbolicState) match {
          case RecVal(fields) =>
            fields.get(field) match {
              case Some(PointerVal(res)) =>
                symbolicState.getVal(PointerVal(res)) match {
                  case Some(r) => r
                  case None =>
                    throw new Exception("IMPLEMENT")
                }
              case None => throw errorNonExistingFieldAccess(loc, RecVal(fields).toString, field, symbolicState)
            }
          case v => throw errorNonRecordFieldAccess(loc, v.toString, symbolicState)
        }
    }
  }


  private def getTarget(expr: Expr, symbolicState: SymbolicState): Option[PointerVal] = {
    expr match {
      case Identifier(name, loc) =>
        symbolicState.getSymbolicValOpt(name) match {
          case Some(PointerVal(address)) => Some(PointerVal(address))
          case _ if functionDeclarations.contains(name) =>
            throw errorNonPointerDereference(loc, functionDeclarations(name).toString, symbolicState)
          case _ =>
            throw errorUninitializedReference(loc, symbolicState)
        }
      case Deref(pointer, loc) =>
        val inner = getTarget(pointer, symbolicState)
        inner match {
          case None => return None
          case _ =>
        }
        symbolicState.getVal(inner.get) match {
          case Some(PointerVal(address)) => Some(PointerVal(address))
          case Some(NullRef) => throw errorNullDereference(loc, symbolicState)
          case Some(v) => throw errorNonPointerDereference(pointer.loc, v.toString, symbolicState)
          case None => throw errorUninitializedReference(pointer.loc, symbolicState)
        }
      case ArrayAccess(array, index, loc) =>
        evaluate(array, symbolicState) match {
          case ArrVal(elems) =>
            evaluate(index, symbolicState) match {
              case Number(value, _) =>
                if (value >= elems.length || value < 0) {
                  throw errorArrayOutOfBounds(loc, elems.length, value, symbolicState)
                }
                symbolicState.getVal(elems(value)) match {
                  case Some(_) => Some(elems(value))
                  case None => throw errorUninitializedReference(loc, symbolicState)
                }
              case s: Symbolic =>
                solver.solveConstraint(
                  solver.createConstraintWithState(
                    BinaryOp(
                      OrOr,
                      BinaryOp(AndAnd, BinaryOp(LowerThan, s, Number(0, loc), loc), symbolicState.pathCondition.expr, loc),
                      BinaryOp(AndAnd, BinaryOp(GreaterEqual, s, Number(elems.length, loc), loc), symbolicState.pathCondition.expr, loc),
                      loc),
                    symbolicState)) match {
                  case Status.SATISFIABLE =>
                    throw errorArrayOutOfBounds(loc, elems.length, symbolicState)
                  case Status.UNSATISFIABLE | Status.UNKNOWN =>
                    for (i <- elems.indices) {
                      solver.solveConstraint(solver.createConstraintWithState(BinaryOp(Equal, s, Number(i, CodeLoc(0, 0)), loc), symbolicState)) match {
                        case Status.SATISFIABLE =>
                          val newState = symbolicState.deepCopy()
                          getTarget(index, newState) match {
                            case Some(ptr) =>
                              newState.updatedVar(ptr, Number(i, CodeLoc(0, 0)))
                            case None =>
                              throw new Exception("this should never happen.")
                          }
                          if (subsumption.nonEmpty) {
                            //TODO take return value???
                            step(newState)
                          }
                          else {
                            searchStrategy.addState(newState)
                          }
                        case _ =>
                      }
                    }
                    symbolicState.returnValue = None
                    None
                }
              case _ => throw errorNonIntArithmetics(loc, symbolicState)
            }
          case _ => throw errorNonArrayAccess(loc, evaluate(array, symbolicState).toString, symbolicState)
        }
      case e =>
        throw errorNotAssignableExpression(e, symbolicState)
    }
  }

  def isConditionBounded(expr: Expr, symbolicState: SymbolicState): Boolean = {
    expr match {
      case BinaryOp(_, lhs, rhs, _) => isConditionBounded(lhs, symbolicState) || isConditionBounded(rhs, symbolicState)
      case Not(expr, _) => isConditionBounded(expr, symbolicState)
      case id@Identifier(_, _) =>
        symbolicState.getSymbolicVal(id.name, id.loc) match {
          case SymbolicVal(_) => true
          case SymbolicExpr(_, _) => true
          case _ => false
        }
      case Alloc(expr, _) => isConditionBounded(expr, symbolicState)
      case Deref(pointer, _) => isConditionBounded(pointer, symbolicState)
      case ArrayNode(elems, _) => elems.exists(isConditionBounded(_, symbolicState))
      case ArrayAccess(array, index, _) => isConditionBounded(array, symbolicState) || isConditionBounded(index, symbolicState)
      case _ => false
    }
  }


}

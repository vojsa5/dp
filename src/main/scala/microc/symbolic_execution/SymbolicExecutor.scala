package microc.symbolic_execution

import microc.symbolic_execution.Statistics
import microc.ProgramException
import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, AstNode, BinaryOp, BinaryOperator, CallFuncExpr, CodeLoc, Deref, Divide, Equal, Expr, FieldAccess, FunDecl, GreaterEqual, GreaterThan, Identifier, IdentifierDecl, IfStmt, Input, Loc, LowerEqual, LowerThan, Minus, NestedBlockStmt, Not, NotEqual, Null, Number, OrOr, OutputStmt, Plus, Program, Record, ReturnStmt, StmtInNestedBlock, Times, VarRef, VarStmt, WhileStmt}
import microc.cfg.{CfgNode, CfgStmtNode, ProgramCfg}
import microc.cli.Reporter
import microc.symbolic_execution.ExecutionException.{errorArrayOutOfBounds, errorDivByZero, errorIncompatibleTypes, errorNonArrayAccess, errorNonExistingFieldAccess, errorNonFunctionApplication, errorNonIntArithmetics, errorNonIntReturn, errorNonPointerDereference, errorNonRecordFieldAccess, errorNotAssignableExpression, errorNullDereference, errorRecordNestedFields, errorUninitializedReference}
import microc.symbolic_execution.Value.{ArrVal, FunVal, IteVal, NullRef, PointerVal, RecVal, Symbolic, SymbolicExpr, SymbolicVal, Val}
import com.microsoft.z3._
import microc.symbolic_execution.optimizations.subsumption.PathSubsumption

import scala.collection.mutable

case class ExecutionException(message: String, loc: Loc, symbolicState: SymbolicState) extends ProgramException(message + "\nloc: " + symbolicState.programLocation.ast) {
  override def format(reporter: Reporter): String = reporter.formatError("execution", message + " loc: " + symbolicState.programLocation.ast, loc)
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

/**
 * Executes programs symbolically by interpreting a program's control flow graph (CFG).
 * Symbolic execution explores multiple paths by using mathematical symbols to represent variable values,
 * which is useful for handling branches, loops, and function calls.
 *
 * @param program The CFG of the program to be executed symbolically.
 * @param subsumption Optional mechanism to optimize execution by eliminating redundant paths.
 * @param ctx Z3 Context used for handling symbolic expressions and constraints.
 * @param searchStrategy Strategy for exploring execution paths (e.g., BFS).
 * @param executionTree
 * @param covered Optional set to track CFG nodes that have been explored.
 * @param createITEAtSymbolicArrayAccess Flag to decide if ITE expressions should be created at symbolic array accesses.
 * @param printStats Boolean to enable or disable the printing of execution statistics.
 */


class SymbolicExecutor(program: ProgramCfg,
                       subsumption: Option[PathSubsumption] = None,
                       ctx: Context = new Context(),
                       searchStrategy: SearchStrategy = new BFSSearchStrategy,
                       executionTree: Option[ExecutionTree] = None,
                       covered: Option[mutable.HashSet[CfgNode]] = None,
                       createITEAtSymbolicArrayAccess: Boolean = false,
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


  /**
   * Runs symbolic execution starting from the 'main' function of the program.
   * @return Retuns the number that the last explored path returns from main.
   */


  def run(): Int = {
    val initialState = new SymbolicState(program.getFce("main"), Number(1, CodeLoc(0, 0)), new SymbolicStore(functionDeclarations))
    executionTree match {
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
            getTargetMemoryCell(target, path) match {
              case Some(value) =>
                path.updateMemoryLocation(value, path.returnValue.get)
              case None =>
                throw new Exception("evert function whould return a number")
            }

          case _ =>
            throw new Exception("this should never happen")
        }
        path.callStack = path.callStack.dropRight(1)
        path.goTo(lastFceCall._1.succ.head, lastFceCall._2)
        step(path)
      }
      //println(path.associatedPathsCount())
      statistics.numPaths += path.associatedPathsCount()
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
    val changes = mutable.HashMap[String, Val]()
    for ((arg, param) <- args.zip(fce.ast.asInstanceOf[FunDecl].params)) {
      changes.put(param.name, evaluate(arg, symbolicState))
    }
    symbolicState.callStack = symbolicState.callStack.appended((symbolicState.programLocation, fce.ast.asInstanceOf[FunDecl].params))
    symbolicState.symbolicStore.pushFrame()
    val tmpNextStatement = symbolicState.programLocation
    for ((name, v) <- changes) {
      symbolicState.updateVar(name, v)
    }
    symbolicState.goTo(fce, fce.fun.params)
    step(symbolicState)
    symbolicState.symbolicStore.popFrame()
    symbolicState.callStack = symbolicState.callStack.dropRight(1)
    symbolicState.programLocation = tmpNextStatement
    symbolicState.returnValue
  }

  def stepOnAssign(assignStmt: AssignStmt, symbolicState: SymbolicState, ignoreErrors: Boolean = false): Unit = {
    assignStmt match {
      case AssignStmt(FieldAccess(record, field, loc), right, _) =>
        val assigned = evaluate(right, symbolicState)
        evaluate(record, symbolicState) match {
          case RecVal(fields) if fields.contains(field) => symbolicState.updateMemoryLocation(fields(field), assigned)
          case RecVal(fields) =>
            throw errorNonExistingFieldAccess(loc, RecVal(fields).toString, field, symbolicState)
          case IteVal(ptrRec1, ptrRec2, _, _) =>
            (symbolicState.getValOnMemoryLocation(ptrRec1), symbolicState.getValOnMemoryLocation(ptrRec2)) match {
              case (Some(RecVal(fields1)), Some(RecVal(fields2))) if fields1.contains(field) && fields2.contains(field) =>
                symbolicState.updateMemoryLocation(fields1(field), assigned)
                symbolicState.updateMemoryLocation(fields2(field), assigned)
              case _ =>
                throw errorNotAssignableExpression(record, symbolicState: SymbolicState)
            }
          case _ =>
            throw new Exception("this should never happen.")
        }
      case AssignStmt(lhs, rhs, _) =>
        getTargetMemoryCell(lhs, symbolicState) match {
          case None =>
            currentPathStopped = true
          case Some(inner) =>
            symbolicState.updateMemoryLocation(inner, evaluate(rhs, symbolicState, ignoreErrors))
        }
    }
  }

  def stepOnLoop(symbolicState: SymbolicState): Unit = {
    val loop: CfgNode = symbolicState.programLocation
    val loopAst = loop.ast.asInstanceOf[WhileStmt]
    if (subsumption.nonEmpty) {
      if (!loops.contains(loop)) {
        val loopIter = createSubsumptionLoopVar()
        loops.put(loop, loopIter)
        solver.solveCondition(symbolicState.pathCondition, loopAst.guard, symbolicState) match {
          case Status.SATISFIABLE | Status.UNKNOWN =>
            val nextState = symbolicState.getIfTrueState()
            var goOutOfSubsumptionIteration = false
            if (!inSubsumptionIteration) {
              inSubsumptionIteration = true
              goOutOfSubsumptionIteration = true
            }
            val loopIterCond = BinaryOp(LowerEqual, loopIter, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0))
            val lastLoopStmt = loop.pred.maxBy(node => node.id)
            subsumption.get.addAnnotations(program.nodes.filter(node => node.id > loop.id && node.id <= lastLoopStmt.id).toList, loopIterCond)
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

            nextState.addVar(IdentifierDecl(loops(loop).name, CodeLoc(0, 0)))
            nextState.updateVar(loops(loop).name, Number(1, CodeLoc(0, 0)))

            step(nextState)

            subsumption.get.performInduction(
              program.nodes.filter(node => node.id >= loop.id && node.id <= newStmt.id).toList,
              loopIter,
              nextState,
              this,
              loop
            )

            lastLoopStmt.succ.add(loop)
            lastLoopStmt.succ.remove(newStmt)
            loop.pred.add(lastLoopStmt)
            loop.pred.remove(newStmt)


//            symbolicState.pathCondition = nextState.pathCondition.prev.get
            symbolicState.returnValue = nextState.returnValue
//            symbolicState.symbolicStore = nextState.symbolicStore

            loop.ast = loopAst

            subsumption.get.computeAnnotationFromSuccessors(symbolicState.programLocation, true)
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
            subsumption.get.computeAnnotationFromSuccessors(symbolicState.programLocation)
        }
      }
    }
    var whileLeavingState: Option[SymbolicState] = None
    solver.solveCondition(symbolicState.pathCondition, Not(loopAst.guard, loopAst.guard.loc), symbolicState) match {
      case Status.SATISFIABLE | Status.UNKNOWN =>
        val nextState = symbolicState.getIfFalseState()
        if (executionTree.nonEmpty) {
          executionTree.get.addNode(symbolicState, nextState)
        }
        step(nextState)
        whileLeavingState = Some(nextState)
      case Status.UNSATISFIABLE =>
        currentPathStopped = true
    }
    solver.solveCondition(symbolicState.pathCondition, loopAst.guard, symbolicState) match {
      case Status.SATISFIABLE | Status.UNKNOWN =>
        val nextState = symbolicState.getIfTrueState()
        if (executionTree.nonEmpty) {
          executionTree.get.addState(symbolicState, nextState)
        }
        if (inSubsumptionIteration) {
          statistics.numPaths += 1
          step(nextState)
        }
        else {
          searchStrategy.addState(nextState)
        }

      case Status.UNSATISFIABLE =>
    }
    if (subsumption.nonEmpty && inSubsumptionIteration) {
      subsumption.get.computeAnnotationFromSuccessors(symbolicState.programLocation)
    }
    if (whileLeavingState.nonEmpty) {
      symbolicState.pathCondition = whileLeavingState.get.pathCondition
      symbolicState.returnValue = whileLeavingState.get.returnValue
      symbolicState.symbolicStore = whileLeavingState.get.symbolicStore
    }
  }

  def step(symbolicState: SymbolicState): Unit = {
    if (covered.nonEmpty) {
      covered.get.add(symbolicState.programLocation)
    }
    val statement = symbolicState.programLocation
    val ast = symbolicState.programLocation.ast
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
    newState.step()
    step(newState)
    if (subsumption.nonEmpty) {
      ast match {
        case stmt: AssignStmt if Utility.statementCanCauseError(stmt) =>
        case _ =>
          subsumption.get.computeAnnotationFromSuccessors(statement)
      }
    }
  }


  def evaluateStatement(ast: AstNode, symbolicState: SymbolicState): Option[SymbolicState] = {
    var newState = symbolicState
    ast match {
      case FunDecl(_, _, _, _) =>
      case VarStmt(decls, _) =>
        newState = decls.foldLeft(symbolicState) {
          (state, decl) =>
            state.addVar(decl)
        }
      case a@AssignStmt(_, _, _) =>
        stepOnAssign(a, symbolicState)
      case IfStmt(guard, _, _, _) =>
        var ifState: Option[SymbolicState] = None
        solver.solveCondition(symbolicState.pathCondition, guard, symbolicState) match {
          case Status.SATISFIABLE | Status.UNKNOWN =>
            val nextState = symbolicState.getIfTrueState()
            if (executionTree.nonEmpty) {
              executionTree.get.addNode(symbolicState, nextState)
            }
            step(nextState)
            ifState = Some(nextState)
          case Status.UNSATISFIABLE =>
            currentPathStopped = true
        }

        solver.solveCondition(symbolicState.pathCondition, Not(guard, guard.loc), symbolicState) match {
          case Status.SATISFIABLE | Status.UNKNOWN =>
            val path = symbolicState.getIfFalseState()
            if (executionTree.nonEmpty) {
              executionTree.get.addState(symbolicState, path)
            }
            if (subsumption.nonEmpty) {
              currentPathStopped = false
              step(path)
              subsumption.get.computeAnnotationFromSuccessors(symbolicState.programLocation)
              statistics.numPaths += 1
            }
            else {
              searchStrategy.addState(path)
            }
          case Status.UNSATISFIABLE =>
            if (subsumption.nonEmpty) {
              subsumption.get.computeAnnotationFromSuccessors(symbolicState.programLocation)
            }
        }
        if (ifState.nonEmpty) {
          symbolicState.pathCondition = ifState.get.pathCondition
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
          subsumption.get.addAnnotation(symbolicState.programLocation, Number(1, CodeLoc(0, 0)))
        }
        return None
      case OutputStmt(expr, _) =>
        evaluate(expr, symbolicState)
    }
    Some(newState)
  }


  private def computeBinaryOperation(operator: BinaryOperator, val1: Val, val2: Val, symbolicState: SymbolicState, loc: Loc, ignoreErrors: Boolean): Val = {
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
      case (NullRef, NullRef) => Number(1, loc)
      case (PointerVal(address1), PointerVal(address2)) => if (address1 == address2) Number(1, loc) else Number(0, loc)
      case (PointerVal(_), NullRef) => Number(0, loc)
      case (NullRef, PointerVal(_)) => Number(0, loc)
      case (IteVal(trueState, falseState, expr, loc), other) =>
        IteVal(
          symbolicState.addVal(computeBinaryOperation(operator, symbolicState.getValOnMemoryLocation(trueState).get, other, symbolicState, loc, ignoreErrors)),
          symbolicState.addVal(computeBinaryOperation(operator, symbolicState.getValOnMemoryLocation(falseState).get, other, symbolicState, loc, ignoreErrors)),
          expr,
          loc
        )
      case (other, IteVal(trueState, falseState, expr, loc)) =>
        IteVal(
          symbolicState.addVal(computeBinaryOperation(operator, symbolicState.getValOnMemoryLocation(trueState).get, other, symbolicState, loc, ignoreErrors)),
          symbolicState.addVal(computeBinaryOperation(operator, symbolicState.getValOnMemoryLocation(falseState).get, other, symbolicState, loc, ignoreErrors)),
          expr,
          loc
        )
      case (e1: Symbolic, e2: Symbolic) =>
        operator match {
          case Plus => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(Plus, e1, e2, loc), loc))
          case Minus => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(Minus, e1, e2, loc), loc))
          case Times => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(Times, e1, e2, loc), loc))
          case Divide => {
            if (ignoreErrors) {
              return SymbolicExpr(BinaryOp(operator, val1.asInstanceOf[Symbolic], val2.asInstanceOf[Symbolic], loc), loc)
            }
            e2 match {
              case Number(v, _) =>
                if (v == 0) {
                  throw errorDivByZero(loc, symbolicState)
                }
                Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(Divide, e1, e2, loc), loc))
              case _ =>
                solver.solveConstraint(
                  solver.createConstraint(BinaryOp(AndAnd, BinaryOp(Equal, e2, Number(0, loc), loc), symbolicState.pathCondition, loc), symbolicState)) match {
                  case Status.UNSATISFIABLE => SymbolicExpr(BinaryOp(Divide, e1, e2, loc), loc)
                  case _ =>
                    throw errorDivByZero(loc, symbolicState)
                }
            }

          }
          case Equal => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(Equal, e1, e2, loc), loc))
          case NotEqual => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(NotEqual, e1, e2, loc), loc))
          case GreaterThan => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(GreaterThan, e1, e2, loc), loc))
          case GreaterEqual => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(GreaterEqual, e1, e2, loc), loc))
          case LowerThan => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(LowerThan, e1, e2, loc), loc))
          case LowerEqual => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(LowerEqual, e1, e2, loc), loc))
          case AndAnd => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(AndAnd, e1, e2, loc), loc))
          case OrOr => Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(BinaryOp(OrOr, e1, e2, loc), loc))
        }

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
      symbolicState.addVal(v)
    }.toArray
    ArrVal(vals)
  }

  def evaluate(expr: Expr, symbolicState: SymbolicState, ignoreErrors: Boolean = false): Val = {
    expr match {
      case BinaryOp(operator, left, right, loc) =>
        (operator, evaluate(left, symbolicState, ignoreErrors), evaluate(right, symbolicState, ignoreErrors)) match {
          case (Equal, NullRef, NullRef) => Number(1, loc)
          case (Equal, PointerVal(address1), PointerVal(address2)) => if (address1.equals(address2)) Number(1, loc) else Number(0, loc)
          case (Equal, PointerVal(_), NullRef) => Number(0, loc)
          case (Equal, NullRef, PointerVal(_)) => Number(0, loc)
          case (op, val1, val2) => computeBinaryOperation(op, val1, val2, symbolicState, loc, ignoreErrors)
        }
      case Not(expr, loc) =>
        evaluate(expr, symbolicState, ignoreErrors) match {
          case Number(value, _) => Number(if (value == 0) 1 else 0, loc)
          case v@SymbolicVal(_) => SymbolicExpr(Not(v, loc), loc)
          case SymbolicExpr(value, _) => SymbolicExpr(Not(value, loc), loc)
          case IteVal(trueState, falseState, expr, loc) =>
            IteVal(symbolicState.addVal(symbolicState.getValOnMemoryLocation(trueState).get), symbolicState.addVal(symbolicState.getValOnMemoryLocation(falseState).get), expr, loc)
          case _ =>
            throw errorNonIntArithmetics(loc, symbolicState)
        }
      case Number(value, loc) => Number(value, loc)
      case id@Identifier(_, _) =>
        symbolicState.getValueOfVar(id.name, id.loc)
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
        symbolicState.addVal(evaluate(expr, symbolicState, ignoreErrors))
      case Deref(pointer, loc) =>
        evaluate(pointer, symbolicState, ignoreErrors) match {
          case PointerVal(address) =>
            symbolicState.getValOnMemoryLocation(PointerVal(address)).get
          case NullRef =>
            throw errorNullDereference(loc, symbolicState)
          case IteVal(trueState: PointerVal, falseState: PointerVal, expr, loc) =>
            IteVal(symbolicState.addVal(symbolicState.getValOnMemoryLocation(trueState).get), symbolicState.addVal(symbolicState.getValOnMemoryLocation(falseState).get), expr, loc)
          case IteVal(trueState, falseState, expr, loc) if symbolicState.getValOnMemoryLocation(falseState).get == NullRef || symbolicState.getValOnMemoryLocation(trueState).get == NullRef =>
            throw errorNullDereference(loc, symbolicState)
          case e =>
            throw errorNonPointerDereference(loc, e.toString, symbolicState)
        }
      case a@ArrayNode(_, _) =>
        loadArray(a, symbolicState)
      case ArrayAccess(array, index, loc) =>
        evaluate(array, symbolicState, ignoreErrors) match {
          case ArrVal(elems) => {
            evaluate(index, symbolicState, ignoreErrors) match {
              case Number(value, _) =>
                if (value >= elems.length || value < 0) {
                  throw errorArrayOutOfBounds(loc, elems.length, value, symbolicState)
                }
                symbolicState.getValOnMemoryLocation(elems(value)) match {
                  case Some(v) => v
                  case None =>
                    throw errorUninitializedReference(loc, symbolicState)
                }
              case s: Symbolic =>
                solver.solveConstraint(
                  solver.createConstraint(
                    BinaryOp(
                      OrOr,
                      BinaryOp(AndAnd, BinaryOp(LowerThan, s, Number(0, loc), loc), symbolicState.pathCondition, loc),
                      BinaryOp(AndAnd, BinaryOp(GreaterEqual, s, Number(elems.length, loc), loc), symbolicState.pathCondition, loc),
                      loc)
                    , symbolicState)) match {
                  case Status.SATISFIABLE | Status.UNKNOWN =>
                    throw errorArrayOutOfBounds(loc, elems.length, symbolicState)
                  case Status.UNSATISFIABLE =>
                    if (createITEAtSymbolicArrayAccess) {
                      var v: Val = null
                      var ptr2: PointerVal = null
                      for (i <- elems.indices) {
                        solver.solveConstraint(
                          solver.createConstraint(BinaryOp(Equal, s, Number(i, CodeLoc(0, 0)), loc), symbolicState)) match {
                          case Status.SATISFIABLE =>
                            val ptr = symbolicState.getMemoryLoc(ArrayAccess(array, Number(i, CodeLoc(0, 0)), loc))
                            if (v == null) {
                              v = symbolicState.getValOnMemoryLocation(ptr).get
                              ptr2 = ptr
                            }
                            else {
                              v match {
                                case _: IteVal =>
                                  v = IteVal(symbolicState.addVal(v), ptr, BinaryOp(Equal, s, Number(i, CodeLoc(0, 0)), loc), loc)
                                case _ =>
                                  v = IteVal(ptr2, ptr, BinaryOp(Equal, s, Number(i, CodeLoc(0, 0)), loc), loc)
                              }
                            }
                          case _ =>
                        }
                      }
                      if (v == null) {
                        throw new Exception("this should never happen")
                      }
                      v
                    }
                    else {
                      for (i <- elems.indices) {
                        solver.solveConstraint(
                          solver.createConstraint(BinaryOp(Equal, s, Number(i, CodeLoc(0, 0)), loc), symbolicState)) match {
                          case Status.SATISFIABLE =>
                            val newState = new SymbolicStateNotAssociatedWithAPath(symbolicState)
                            getTargetMemoryCell(index, newState) match {
                              case Some(ptr) =>
                                newState.updateMemoryLocation(ptr, Number(i, CodeLoc(0, 0)))
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
                            if (executionTree.nonEmpty) {
                              executionTree.get.addState(symbolicState, newState)
                            }
                          case _ =>
                        }
                      }
                      currentPathStopped = true
                      symbolicState.returnValue = None
                      Number(0, CodeLoc(0, 0))
                    }
                }
              case _ => throw errorNonIntArithmetics(loc, symbolicState)
            }
          }
          case _ =>
            throw errorNonArrayAccess(loc, evaluate(array, symbolicState, ignoreErrors).toString, symbolicState)
        }
      case Record(fields, loc) =>
        val fieldsMap: mutable.HashMap[String, PointerVal] = mutable.HashMap.empty
        fields.foreach(field =>
          evaluate(field.expr, symbolicState, ignoreErrors) match {
            case RecVal(_) => throw errorRecordNestedFields(field.expr.loc, symbolicState)
            case res =>
              symbolicState.updateVar(field.name, res)
              fieldsMap.update(field.name, symbolicState.getSymbolicValOpt(field.name).get)
          }
        )
        RecVal(fieldsMap)
      case FieldAccess(record, field, loc) =>
        evaluate(record, symbolicState, ignoreErrors) match {
          case RecVal(fields) =>
            fields.get(field) match {
              case Some(PointerVal(res)) =>
                symbolicState.getValOnMemoryLocation(PointerVal(res)).get
              case None => throw errorNonExistingFieldAccess(loc, RecVal(fields).toString, field, symbolicState)
            }
          case v => throw errorNonRecordFieldAccess(loc, v.toString, symbolicState)
        }
    }
  }


  private def getTargetMemoryCell(expr: Expr, symbolicState: SymbolicState): Option[PointerVal] = {
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
        val inner = getTargetMemoryCell(pointer, symbolicState)
        inner match {
          case None => return None
          case _ =>
        }
        symbolicState.getValOnMemoryLocation(inner.get) match {
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
                symbolicState.getValOnMemoryLocation(elems(value)) match {
                  case Some(_) => Some(elems(value))
                  case None => throw errorUninitializedReference(loc, symbolicState)
                }
              case s: Symbolic =>
                solver.solveConstraint(
                  solver.createConstraint(
                    BinaryOp(
                      OrOr,
                      BinaryOp(AndAnd, BinaryOp(LowerThan, s, Number(0, loc), loc), symbolicState.pathCondition, loc),
                      BinaryOp(AndAnd, BinaryOp(GreaterEqual, s, Number(elems.length, loc), loc), symbolicState.pathCondition, loc),
                      loc),
                    symbolicState)) match {
                  case Status.SATISFIABLE =>
                    throw errorArrayOutOfBounds(loc, elems.length, symbolicState)
                  case Status.UNSATISFIABLE | Status.UNKNOWN =>
                    if (createITEAtSymbolicArrayAccess) {
                      var ptr: PointerVal = null
                      for (i <- elems.indices) {
                        solver.solveConstraint(
                          solver.createConstraint(BinaryOp(Equal, s, Number(i, CodeLoc(0, 0)), loc), symbolicState)) match {
                          case Status.SATISFIABLE =>
                            val ptr2 = symbolicState.getMemoryLoc(ArrayAccess(array, Number(i, CodeLoc(0, 0)), loc))
                            if (ptr == null) {
                              ptr = ptr2
                            }
                            else {
                              ptr = symbolicState.addVal(IteVal(ptr2, ptr, BinaryOp(Equal, s, Number(i, CodeLoc(0, 0)), loc), loc))
                            }
                          case _ =>
                        }
                      }
                      if (ptr == null) {
                        throw new Exception("this should never happen.")
                      }
                      Some(ptr)
                    }
                    else {
                      for (i <- elems.indices) {
                        solver.solveConstraint(solver.createConstraint(BinaryOp(Equal, s, Number(i, CodeLoc(0, 0)), loc), symbolicState)) match {
                          case Status.SATISFIABLE =>
                            val newState = new SymbolicStateNotAssociatedWithAPath(symbolicState)
                            getTargetMemoryCell(index, newState) match {
                              case Some(ptr) =>
                                newState.updateMemoryLocation(ptr, Number(i, CodeLoc(0, 0)))
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
                }
              case _ => throw errorNonIntArithmetics(loc, symbolicState)
            }
          case other =>
            throw errorNonArrayAccess(loc, evaluate(array, symbolicState).toString, symbolicState)
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
        symbolicState.getValueOfVar(id.name, id.loc) match {
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

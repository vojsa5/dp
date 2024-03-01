package microc.symbolic_execution

import microc.symbolic_execution.Statistics
import microc.ProgramException
import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, AstNode, BinaryOp, BinaryOperator, CallFuncExpr, CodeLoc, Deref, Divide, Equal, Expr, FieldAccess, FunDecl, GreaterEqual, GreaterThan, Identifier, IdentifierDecl, IfStmt, Input, Loc, LowerEqual, LowerThan, Minus, NestedBlockStmt, Not, NotEqual, Null, Number, OutputStmt, Plus, Program, Record, ReturnStmt, StmtInNestedBlock, Times, VarRef, VarStmt, WhileStmt}
import microc.cfg.{CfgNode, CfgStmtNode, ProgramCfg}
import microc.cli.Reporter
import microc.symbolic_execution.ExecutionException.{errorArrayOutOfBounds, errorDivByZero, errorIncompatibleTypes, errorNonArrayAccess, errorNonExistingFieldAccess, errorNonFunctionApplication, errorNonIntArithmetics, errorNonIntReturn, errorNonPointerDereference, errorNonRecordFieldAccess, errorNotAssignableExpression, errorNullDereference, errorPossibleDivByZero, errorRecordNestedFields, errorUninitializedReference}
import microc.symbolic_execution.Value.{ArrVal, FunVal, IteVal, NullRef, PointerVal, RecVal, Symbolic, SymbolicExpr, SymbolicVal, Val}
import com.microsoft.z3._

import scala.collection.mutable

case class ExecutionException(message: String, loc: Loc) extends ProgramException(message) {
  override def format(reporter: Reporter): String = reporter.formatError("execution", message, loc)
}

object ExecutionException {
  def errorMissingMainFunction(program: Program): ExecutionException =
    ExecutionException(s"Missing main function, declared functions are ${program.funs.map(_.name)}", program.loc)

  def errorIO(loc: Loc, cause: Throwable): ExecutionException =
    ExecutionException(s"I/O error ${cause.getMessage}", loc)

  def errorNonRecordFieldAccess(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-record ($value) field access", loc)

  def errorNonExistingFieldAccess(loc: Loc, rec: String, field: String): ExecutionException =
    ExecutionException(s"Non-existing field ($field) access in $rec", loc)

  def errorNullDereference(loc: Loc): ExecutionException =
    ExecutionException(s"Null-pointer pointer dereference", loc)

  def errorNonPointerDereference(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-pointer ($value) pointer dereference", loc)

  def errorNonIntCondition(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-integer ($value) condition guard", loc)

  def errorNonIntReturn(fun: FunDecl): ExecutionException =
    ExecutionException(s"Non-integer return from function ${fun.name}", fun.block.ret.expr.loc)

  def errorNonIntOutput(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-integer ($value) output", loc)

  def errorNonIntInput(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-integer ($value) input", loc)

  def errorNonIntArithmetics(loc: Loc): ExecutionException =
    ExecutionException(s"Non-integer arithmetic operation", loc)

  def errorUninitializedReference(loc: Loc): ExecutionException =
    ExecutionException(s"Uninitialized variable", loc)

  def errorNonFunctionApplication(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-function ($value) application", loc)

  def errorRecordNestedFields(loc: Loc): ExecutionException =
    ExecutionException("Nested records are not supported, use pointers", loc)

  def errorNotAssignableExpression(expr: Expr): ExecutionException =
    ExecutionException(s"Expression is not assignable ($expr)", expr.loc)

  def errorInvalidArgumentList(loc: Loc, fun: FunDecl, actual: Int): ExecutionException =
    ExecutionException(s"Invalid argument list: expected ${fun.params.size}, got: $actual", loc)

  def errorDivByZero(loc: Loc): ExecutionException =
    ExecutionException(s"Division by zero", loc)

  def errorPossibleDivByZero(loc: Loc): ExecutionException =
    ExecutionException(s"Possible Division by zero", loc)

  def errorIncompatibleTypes(loc: Loc, left: String, right: String): ExecutionException =
    ExecutionException(s"Incompatible types, cannot assign $right into $left", loc)

  def errorArrayOutOfBounds(loc: Loc, length: Int, index: Int): ExecutionException =
    ExecutionException(s"Array out of bounds (length: $length, index: $index)", loc)

  def errorNonArrayAccess(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-array ($value) element access", loc)


}


class SymbolicExecutor(program: ProgramCfg,
                       subsumption: Option[PathSubsumption] = None,
                       ctx: Context = new Context(),
                       searchStrategy: SearchStrategy = new BFSSearchStrategy,
                       useSummarization: Boolean = false
                      ) {

  val solver = new ConstraintSolver(ctx)
  var statistics = new Statistics()
  var currentPathStopped = false
  var finalBacktracking = false
  var backTrackingPath: Option[SymbolicState] = None
  var pathsToNodesToAddAnotations: mutable.HashMap[SymbolicState, mutable.Queue[CfgNode]] = mutable.HashMap.empty
  private var functionDeclarations: Map[String, FunVal] = Map.empty
  var loops: mutable.HashMap[CfgNode, Identifier] = mutable.HashMap.empty
  var subsumptionLoopVar = 1

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
    searchStrategy.addState(new SymbolicState(program.getFce("main"), PathCondition.initial(), new SymbolicStore(functionDeclarations)))
    var res: Option[Val] = None
    while (searchStrategy.statesCount() != 0) {
      statistics.printStats()
      var path = searchStrategy.getState()
      currentPathStopped = false
      System.out.println(path.nextStatement.ast)
      step(path)
//      if (subsumption.nonEmpty) {
//        subsumption.get.addAnnotation(path.nextStatement, solver.createConstraintWithState(path.pathCondition.expr, path))
//      }
//      path.pathCondition = path.pathCondition.prev.get
      while (path.callStack.nonEmpty && !currentPathStopped) {
        val lastFceCall = path.callStack.last
        path.symbolicStore.popFrame()
        // in the normalized ast, all function calls are in the form of assignments
        lastFceCall._1.ast match {
          case AssignStmt(target, _, _) =>
            path.updatedVar(getTarget(target, path), path.returnValue)
          case _ =>
            throw new Exception("this should never happen")
        }
        path.callStack = path.callStack.dropRight(1)
        path = path.goTo(lastFceCall._1.succ.head, lastFceCall._2)
        step(path)
      }
      for (node <- pathsToNodesToAddAnotations.getOrElse(path, mutable.Queue.empty)) {
        if (!currentPathStopped && subsumption.nonEmpty) {
          subsumption.get.computeAnnotation(node)
        }
      }

      statistics.numPaths += 1
      res = Some(path.returnValue)
    }
    res.get match {
      case Number(value, _) => value
      case i: IteVal =>
        0
      case _ =>
        throw errorNonIntReturn(program.getFce("main").ast.asInstanceOf[FunDecl])
    }
  }

  def runFunction(name: String, symbolicState: SymbolicState, args: List[Expr]): Val = {
    val fce = program.getFce(name)
    symbolicState.callStack = symbolicState.callStack.appended((symbolicState.nextStatement, fce.ast.asInstanceOf[FunDecl].params))
    symbolicState.symbolicStore.pushFrame()
    for ((arg, param) <- args.zip(fce.ast.asInstanceOf[FunDecl].params)) {
      symbolicState.addedVar(param.name, evaluate(arg, symbolicState))
    }
    val fceState = symbolicState.goTo(fce, fce.fun.params)
    step(fceState)
    symbolicState.returnValue = fceState.returnValue
    symbolicState.symbolicStore = fceState.symbolicStore
    symbolicState.symbolicStore.popFrame()
    symbolicState.callStack = symbolicState.callStack.dropRight(1)
    symbolicState.returnValue

//    fceState.symbolicStore.popFrame()
//    fceState.callStack = fceState.callStack.dropRight(1)
//    fceState.returnValue
  }

  def addAnotations(node: CfgNode, minId: Int, maxId: Int, annotation: Expr): Unit = {
    if (node.id < maxId && node.id > minId) {
      subsumption.get.addAnnotation(node, annotation)
      node.succ.foreach(s => addAnotations(s, minId, maxId, annotation))
    }
  }

  def stepOnLoop(symbolicState: SymbolicState): Unit = {
    val loop: CfgNode = symbolicState.nextStatement
    val loopAst = loop.ast.asInstanceOf[WhileStmt]
    System.out.println(loopAst.guard)
    if (subsumption.nonEmpty) {
      if (!loops.contains(loop)) {
        val loopIter = createSubsumptionLoopVar()
        val loopIterCond = BinaryOp(LowerThan, loopIter, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0))
        val succs = loop.succ
        val maxSucc = succs.maxBy(node => node.id).id
        for (s <- succs) {
          addAnotations(s, loop.id, maxSucc, loopIterCond)
        }
        subsumption.get.addAnnotation(loop, loopIterCond)
        val decreaseLoopIter = AssignStmt(loopIter, BinaryOp(Minus, loopIter, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0))
        val lastBody = loopAst.block.asInstanceOf[NestedBlockStmt].body
        val body = lastBody.appended(decreaseLoopIter)
        loop.ast = WhileStmt(loopAst.guard, NestedBlockStmt(body, loopAst.block.loc), loopAst.loc)
        loops.put(loop, loopIter)

        val lastLoopStmt = loop.pred.maxBy(node => node.id)
        val newStmt = new CfgStmtNode(-(subsumptionLoopVar - 1), decreaseLoopIter)
        lastLoopStmt.succ.foreach(s => {
          s.pred.remove(lastLoopStmt)
          s.pred.add(newStmt)
          newStmt.succ.add(s)
        })
        lastLoopStmt.succ.clear()
        lastLoopStmt.succ.add(newStmt)
        newStmt.pred.add(lastLoopStmt)
        null
      }
      symbolicState.addedVar(loops(loop).name, Number(0, CodeLoc(0, 0)))
    }
    solver.solveCondition(symbolicState.pathCondition.expr, loopAst.guard, symbolicState) match {
      case Status.SATISFIABLE =>
        val nextState = symbolicState.getIfTrueState()
        step(nextState)
        symbolicState.pathCondition = nextState.pathCondition.prev.get
        symbolicState.returnValue = nextState.returnValue
      case Status.UNKNOWN =>
        throw new Exception("IMPLEMENT")
      case Status.UNSATISFIABLE =>
        currentPathStopped = true
    }
    solver.solveCondition(symbolicState.pathCondition.expr, Not(loopAst.guard, loopAst.guard.loc), symbolicState) match {
      case Status.SATISFIABLE =>

        val path = symbolicState.getIfFalseState()
        searchStrategy.addState(path)
        if (subsumption.nonEmpty) {
          subsumption.get.addAnnotation(symbolicState.nextStatement, Not(loopAst.guard, loopAst.guard.loc))
        }
        finalBacktracking = false
        pathsToNodesToAddAnotations.put(path, mutable.Queue.empty)
        backTrackingPath = Some(path)
        return
      case Status.UNKNOWN =>
        throw new Exception("IMPLEMENT")
      case Status.UNSATISFIABLE =>
    }
  }

  def step(symbolicState: SymbolicState): Unit = {
    var newState = symbolicState
    val ast = symbolicState.nextStatement.ast
    if (subsumption.nonEmpty) {
      if (!subsumption.get.checkSubsumption(symbolicState.nextStatement, symbolicState.pathCondition.expr, symbolicState)) {
        statistics.stoppedWithSubsumption += 1
        finalBacktracking = true
        currentPathStopped = true
        return
      }
    }
    ast match {
      case FunDecl(_, _, _, _) =>
      case VarStmt(decls, _) =>
        newState = decls.foldLeft(symbolicState) {
          (state, decl) =>
            state.addedNewVar(decl)
        }
//      case nested@NestedBlockStmt(stmts, _) =>
//        symbolicState.symbolicStore.pushFrame()
//        //symbolicState.nextStatement = nested.body.head
//        step(symbolicState)
//        symbolicState.symbolicStore.popFrame()
//        return
      case AssignStmt(FieldAccess(record, field, loc), right, _) =>
        val assigned = evaluate(right, symbolicState)
        evaluate(record, symbolicState) match {
          case RecVal(fields) if fields.contains(field) => fields.update(field, assigned)
          case RecVal(fields) =>
            throw errorNonExistingFieldAccess(loc, RecVal(fields).toString, field)
          case IteVal(RecVal(fields1), RecVal(fields2), _, _)
            if fields1.contains(field) && fields2.contains(field) => {
            fields1.update(field, assigned)
            fields2.update(field, assigned)
          }
          case _ =>
            throw errorNotAssignableExpression(record)
        }
      case AssignStmt(lhs, rhs, _) =>
        symbolicState.updatedVar(getTarget(lhs, symbolicState), evaluate(rhs, symbolicState))
      case IfStmt(guard, _, _, _) =>
        var ifState: Option[SymbolicState] = None
        solver.solveCondition(symbolicState.pathCondition.expr, guard, symbolicState) match {
          case Status.SATISFIABLE =>
            val nextState = symbolicState.getIfTrueState()
            step(nextState)
            if (subsumption.nonEmpty) {
              subsumption.get.addAnnotation(symbolicState.nextStatement, guard)
            }
            ifState = Some(nextState)
          case Status.UNKNOWN =>
            throw new Exception("IMPLEMENT")
          case Status.UNSATISFIABLE =>
            currentPathStopped = true
        }

//        if (subsumption.nonEmpty) {
//          val annotation = solver.createConstraintWithState(BinaryOp(AndAnd, symbolicState.pathCondition.expr, guard, guard.loc), symbolicState)
//          subsumption.get.addAnnotation(symbolicState.nextStatement, annotation)
//        }

        solver.solveCondition(symbolicState.pathCondition.expr, Not(guard, guard.loc), symbolicState) match {
          case Status.SATISFIABLE =>
            val path = symbolicState.getIfFalseState()
            searchStrategy.addState(path)
            if (subsumption.nonEmpty) {
              subsumption.get.addAnnotation(symbolicState.nextStatement, Not(guard, guard.loc))
            }
            finalBacktracking = false
            pathsToNodesToAddAnotations.put(path, mutable.Queue.empty)
            backTrackingPath = Some(path)
          case Status.UNKNOWN =>
            throw new Exception("IMPLEMENT")
          case Status.UNSATISFIABLE =>
        }
        if (ifState.nonEmpty) {
          symbolicState.pathCondition = ifState.get.pathCondition.prev.get
          symbolicState.returnValue = ifState.get.returnValue
          symbolicState.symbolicStore = ifState.get.symbolicStore
        }

//        if (subsumption.nonEmpty) {
//          val annotation = solver.createConstraintWithState(BinaryOp(AndAnd, symbolicState.pathCondition.expr, Not(guard, guard.loc), guard.loc), symbolicState)
//          subsumption.get.addAnnotation(symbolicState.nextStatement, annotation)
//        }
        return
      case loop@WhileStmt(_, _, _) =>
        stepOnLoop(symbolicState)
        return
      case ReturnStmt(expr, _) =>
        finalBacktracking = true
        symbolicState.returnValue = evaluate(expr, symbolicState)
        return
      case OutputStmt(expr, _) =>
        evaluate(expr, symbolicState)
    }
    if (currentPathStopped) {
      return
    }
    val nextState = newState.nextState()
    step(nextState)
    if (subsumption.nonEmpty) {
      if (finalBacktracking) {
        if (!currentPathStopped) {
          subsumption.get.computeAnnotation(symbolicState.nextStatement)
        }
      }
      else {
          pathsToNodesToAddAnotations(backTrackingPath.get).enqueue(symbolicState.nextStatement)
      }
    }
    symbolicState.returnValue = nextState.returnValue
    symbolicState.symbolicStore = nextState.symbolicStore
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
              throw errorDivByZero(loc)
            }
            Number(l / r, loc)
          case Equal => Number(if (l == r) 1 else 0, loc)
          case NotEqual => Number(if (l != r) 1 else 0, loc)
          case GreaterThan => Number(if (l > r) 1 else 0, loc)
          case GreaterEqual => Number(if (l >= r) 1 else 0, loc)
          case LowerThan => Number(if (l < r) 1 else 0, loc)
          case LowerEqual => Number(if (l <= r) 1 else 0, loc)
        }

      case (e1: Symbolic, e2: Symbolic) =>
        operator match {
          case Plus => SymbolicExpr(BinaryOp(Plus, e1, e2, loc), loc)
          case Minus => SymbolicExpr(BinaryOp(Minus, e1, e2, loc), loc)
          case Times => SymbolicExpr(BinaryOp(Times, e1, e2, loc), loc)
          case Divide => {
            solver.solveConstraint(
              solver.createConstraintWithState(BinaryOp(AndAnd, BinaryOp(Equal, e2, Number(0, loc), loc), symbolicState.pathCondition.expr, loc), symbolicState)) match {
              case Status.SATISFIABLE =>
                throw errorPossibleDivByZero(loc)
              case Status.UNSATISFIABLE => SymbolicExpr(BinaryOp(Divide, e1, e2, loc), loc)
              case Status.UNKNOWN => throw new Exception("IMPLEMENT")
            }
          }
          case Equal => SymbolicExpr(BinaryOp(Equal, e1, e2, loc), loc)
          case NotEqual => SymbolicExpr(BinaryOp(NotEqual, e1, e2, loc), loc)
          case GreaterThan => SymbolicExpr(BinaryOp(GreaterThan, e1, e2, loc), loc)
          case GreaterEqual => SymbolicExpr(BinaryOp(GreaterEqual, e1, e2, loc), loc)
          case LowerThan => SymbolicExpr(BinaryOp(LowerThan, e1, e2, loc), loc)
          case LowerEqual => SymbolicExpr(BinaryOp(LowerEqual, e1, e2, loc), loc)
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
        throw errorNonIntArithmetics(loc)
    }
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
          case _ => throw errorNonIntArithmetics(loc)
        }
      case Number(value, loc) => Number(value, loc)
      case id@Identifier(_, _) =>
        symbolicState.getSymbolicVal(id.name, id.loc)
      case Input(loc) => SymbolicVal(loc)
      case CallFuncExpr(targetFun, args, loc) =>
        targetFun match {
          case Identifier(name, _) => {
            val r = runFunction(name, symbolicState, args)
            r
          }
          case _ => throw errorNonFunctionApplication(loc, targetFun.toString)
        }
      case VarRef(id, _) =>
        symbolicState.getSymbolicValOpt(id.name).get
      case Null(_) => NullRef
      case Alloc(expr, _) =>
        symbolicState.addedAlloc(evaluate(expr, symbolicState))
      case Deref(pointer, loc) =>
        val d = evaluate(pointer, symbolicState)
        evaluate(pointer, symbolicState) match {
          case PointerVal(address) =>
            symbolicState.getVal(PointerVal(address)).get
          case NullRef =>
            throw errorNullDereference(loc)
          case IteVal(trueState: PointerVal, falseState: PointerVal, expr, loc) =>
            IteVal(symbolicState.getVal(trueState).get, symbolicState.getVal(falseState).get, expr, loc)
          case e =>
            throw errorNonPointerDereference(loc, e.toString)
        }
      case ArrayNode(elems, _) =>
        var prev: Val = null
        val vals = elems.map { e =>
          val v = evaluate(e, symbolicState)
          if (prev != null && !prev.getClass.isAssignableFrom(v.getClass)) {
            throw errorIncompatibleTypes(e.loc, prev.toString, v.toString)
          } else {
            prev = v
          }
          symbolicState.addedAlloc(v)
        }.toArray
        ArrVal(vals)
      case ArrayAccess(array, index, loc) =>
        evaluate(array, symbolicState) match {
          case ArrVal(elems) => {
            evaluate(index, symbolicState) match {
              case Number(value, _) =>
                if (value >= elems.length || value < 0) {
                  throw errorArrayOutOfBounds(loc, value, elems.length)
                }
                symbolicState.getVal(elems(value)) match {
                  case Some(v) => v
                  case None => throw errorUninitializedReference(loc)
                }
              case _ => throw errorNonIntArithmetics(loc)
            }
          }
          case _ => throw errorNonArrayAccess(loc, evaluate(array, symbolicState).toString)
        }
      case Record(fields, loc) =>
        val fieldsMap: mutable.HashMap[String, Val] = mutable.HashMap.empty
        fields.foreach(field =>
          evaluate(field.expr, symbolicState) match {
            case RecVal(_) => throw errorRecordNestedFields(field.expr.loc)
            case res => fieldsMap.update(field.name, res)
          }
        )
        RecVal(fieldsMap)
      case FieldAccess(record, field, loc) =>
        evaluate(record, symbolicState) match {
          case RecVal(fields) =>
            fields.get(field) match {
              case Some(res) => res
              case None => throw errorNonExistingFieldAccess(loc, RecVal(fields).toString, field)
            }
          case v => throw errorNonRecordFieldAccess(loc, v.toString)
        }
    }
  }

  private def getTarget(expr: Expr, symbolicState: SymbolicState): PointerVal = {
    expr match {
      case Identifier(name, loc) =>
        symbolicState.getSymbolicValOpt(name) match {
          case Some(PointerVal(address)) => PointerVal(address)
          case _ if functionDeclarations.contains(name) =>
            throw errorNonPointerDereference(loc, functionDeclarations(name).toString)
          case _ =>
            throw errorUninitializedReference(loc)
        }
      case Deref(pointer, loc) =>
        val i = symbolicState.getVal(getTarget(pointer, symbolicState))
        i match {
          case Some(PointerVal(address)) => PointerVal(address)
          case Some(NullRef) => throw errorNullDereference(loc)
          case Some(v) => throw errorNonPointerDereference(pointer.loc, v.toString)
          case None => throw errorUninitializedReference(pointer.loc)
        }
      case ArrayAccess(array, index, loc) =>
        val i = evaluate(index, symbolicState);
        i match {
          case Number(value, _) =>
            evaluate(array, symbolicState) match {
              case ArrVal(elems) if value >= elems.length || value < 0 =>
                throw errorArrayOutOfBounds(loc, value, elems.length)
              case ArrVal(elems) => symbolicState.getVal(elems(value)) match {
                case Some(PointerVal(address)) => PointerVal(address)
                case Some(n@Number(_, _)) => elems(value)
                case None => throw errorUninitializedReference(loc)
                case _ => throw new Exception("IMPLEMENT")
              }
              case _ => throw errorNonArrayAccess(index.loc, evaluate(array, symbolicState).toString)
            }
          case _ => throw errorNonIntArithmetics(loc)
        }
      case e => throw errorNotAssignableExpression(e)
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

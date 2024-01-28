package microc.symbolic_execution

import microc.ProgramException
import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, BinaryOp, CallFuncExpr, CodeLoc, Deref, Divide, Equal, Expr, FunDecl, GreatThan, Identifier, IfStmt, Input, Loc, Minus, NestedBlockStmt, Not, NotEqual, Null, Number, OutputStmt, Plus, Program, ReturnStmt, Times, VarRef, VarStmt, WhileStmt}
import microc.cfg.ProgramCfg
import microc.cli.Reporter
import microc.symbolic_execution.ExecutionException.{errorArrayOutOfBounds, errorDivByZero, errorIncompatibleTypes, errorNonArrayAccess, errorNonFunctionApplication, errorNonIntArithmetics, errorNonIntReturn, errorNonPointerDereference, errorNotAssignableExpression, errorNullDereference, errorPossibleDivByZero, errorUninitializedReference}
import microc.symbolic_execution.Value.{ArrVal, NullRef, PointerVal, Symbolic, SymbolicExpr, SymbolicVal, Val}
import com.microsoft.z3.{ArrayExpr, _}

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


class SymbolicExecutor(program: ProgramCfg) {

  val solver = new ConstraintSolver()
  var unfinishedPaths: Set[SymbolicState] = Set()

  def run(): Int = {


    unfinishedPaths += new SymbolicState(program.getFce("main"), PathCondition.initial())
    var res: Option[Val] = None
    while (unfinishedPaths.nonEmpty) {
      val path = unfinishedPaths.head
      unfinishedPaths = unfinishedPaths.tail
      step(path)
      while (path.callStack.nonEmpty) {
        val lastFceCall = path.callStack.last
        path.symbolicStore.popFrame()
        // in the normalized ast, all function calls are in the form of assignments
        lastFceCall.ast match {
          case AssignStmt(target, _, _) =>
            path.updatedVar(getTarget(target, path), path.returnValue)
        }
        path.callStack = path.callStack.dropRight(1)
        path.nextStatement = lastFceCall.succ.head
        step(path)
      }
      res = Some(path.returnValue)
    }
    res.get match {
      case Number(value, _) => value
      case _ => throw errorNonIntReturn(program.getFce("main").ast.asInstanceOf[FunDecl])
    }
  }

  def runFunction(name: String, symbolicState: SymbolicState, args: List[Expr]): Val = {
    val fce = program.getFce(name)
    symbolicState.callStack = symbolicState.callStack.appended(symbolicState.nextStatement)
    symbolicState.symbolicStore.pushFrame()
    symbolicState.pathCondition = new PathCondition(Some(symbolicState.pathCondition), BinaryOp(Equal, Number(1, CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
    for ((arg, param) <- args.zip(fce.ast.asInstanceOf[FunDecl].params)) {
      symbolicState.addedVar(param.name, evaluate(arg, symbolicState))
    }
    val fceState = symbolicState.goTo(fce)
    step(fceState)
    symbolicState.returnValue = fceState.returnValue
    //symbolicState.pathCondition = symbolicState.pathCondition.prev.get
    symbolicState.symbolicStore.popFrame()
    symbolicState.callStack = symbolicState.callStack.dropRight(1)
    symbolicState.returnValue
  }

  def stepOnLoop(symbolicState: SymbolicState, loop: WhileStmt): Unit = {
    solver.solveCondition(symbolicState.pathCondition.expr, loop.guard, symbolicState) match {
      case Status.SATISFIABLE =>
        val nextState = symbolicState.getIfTrueState()
        step(nextState)
        symbolicState.returnValue = nextState.returnValue
      case Status.UNKNOWN =>
        throw new Exception("IMPLEMENT")
      case Status.UNSATISFIABLE =>
    }
    solver.solveCondition(symbolicState.pathCondition.expr, Not(loop.guard, loop.guard.loc), symbolicState) match {
      case Status.SATISFIABLE =>
        unfinishedPaths += symbolicState.getIfFalseState()
        return
      case Status.UNKNOWN =>
        throw new Exception("IMPLEMENT")
      case Status.UNSATISFIABLE =>
    }
  }

  def step(symbolicState: SymbolicState): Unit = {
    var newState = symbolicState
    val ast = symbolicState.nextStatement.ast
    ast match {
      case FunDecl(_, _, _, _) =>
      case VarStmt(decls, _) =>
        newState = decls.foldLeft(symbolicState) {
          (state, decl) =>
            state.addedNewVar(decl.name)
        }
//      case nested@NestedBlockStmt(stmts, _) =>
//        symbolicState.symbolicStore.pushFrame()
//        //symbolicState.nextStatement = nested.body.head
//        step(symbolicState)
//        symbolicState.symbolicStore.popFrame()
//        return
      case AssignStmt(lhs, rhs, _) =>
        symbolicState.updatedVar(getTarget(lhs, symbolicState), evaluate(rhs, symbolicState))
      case IfStmt(guard, _, _, _) =>
        solver.solveCondition(symbolicState.pathCondition.expr, guard, symbolicState) match {
          case Status.SATISFIABLE =>
            val nextState = symbolicState.getIfTrueState()
            step(nextState)
            symbolicState.returnValue = nextState.returnValue
          case Status.UNKNOWN =>
            throw new Exception("IMPLEMENT")
          case Status.UNSATISFIABLE =>
        }

        solver.solveCondition(symbolicState.pathCondition.expr, Not(guard, guard.loc), symbolicState) match {
          case Status.SATISFIABLE =>
            //val nextState = symbolicState.getIfFalseState()
            //step(nextState)
            //symbolicState.returnValue = nextState.returnValue
            //return
            unfinishedPaths += symbolicState.getIfFalseState()
            return
          case Status.UNKNOWN =>
            throw new Exception("IMPLEMENT")
          case Status.UNSATISFIABLE =>
            return
        }
      case loop@WhileStmt(_, _, _) =>
        stepOnLoop(symbolicState, loop)
        return
      case ReturnStmt(expr, _) =>
        symbolicState.returnValue = evaluate(expr, symbolicState)
        return
      case OutputStmt(expr, _) =>
        val value = evaluate(expr, symbolicState)
        value match {
          case Number(value, _) =>
            System.out.println(value)
          case SymbolicVal(_) =>
            System.out.println("Symbolic value")
        }
    }
    //newState.nextStates().foreach(step)
    val nextState = symbolicState.nextState()
    step(nextState)
    symbolicState.returnValue = nextState.returnValue
  }

  def evaluate(expr: Expr, symbolicState: SymbolicState): Val = {
    expr match {
      case BinaryOp(operator, left, right, loc) =>
        (evaluate(left, symbolicState), evaluate(right, symbolicState)) match {
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
              case GreatThan => Number(if (l > r) 1 else 0, loc)
            }
          case (e1: Symbolic, e2: Symbolic) =>
              operator match {
                case Plus => SymbolicExpr(BinaryOp(Plus, e1, e2, loc), loc)
                case Minus => SymbolicExpr(BinaryOp(Minus, e1, e2, loc), loc)
                case Times => SymbolicExpr(BinaryOp(Times, e1, e2, loc), loc)
                case Divide => {
                  solver.solveConstraint(
                    solver.createConstraint(BinaryOp(AndAnd, BinaryOp(Equal, e2, Number(0, loc), loc), symbolicState.pathCondition.expr, loc), symbolicState)) match {
                    case Status.SATISFIABLE => throw errorPossibleDivByZero(loc)
                    case Status.UNSATISFIABLE => SymbolicExpr(BinaryOp(Divide, e1, e2, loc), loc)
                    case Status.UNKNOWN => throw new Exception("IMPLEMENT")
                  }
                }
                case Equal => SymbolicExpr(BinaryOp(Equal, e1, e2, loc), loc)
                case NotEqual => SymbolicExpr(BinaryOp(NotEqual, e1, e2, loc), loc)
                case GreatThan => SymbolicExpr(BinaryOp(GreatThan, e1, e2, loc), loc)
              }
          case (NullRef, NullRef) => Number(1, loc)
          case (PointerVal(address1), PointerVal(address2)) => if (address1 == address2) Number(1, loc) else Number(0, loc)
          case (PointerVal(_), NullRef) => Number(0, loc)
          case (NullRef, PointerVal(_)) => Number(0, loc)
          case _ => throw errorNonIntArithmetics(loc)
        }
      case Number(value, loc) => Number(value, loc)
      case id@Identifier(_, _) =>
        symbolicState.getSymbolicValForId(id)
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
        symbolicState.getSymbolicVal(id.name).get
      case Null(_) => NullRef
      case Alloc(expr, _) =>
        symbolicState.addedAlloc(evaluate(expr, symbolicState))
      case Deref(pointer, loc) =>
        evaluate(pointer, symbolicState) match {
          case PointerVal(address) => symbolicState.getVal(PointerVal(address)).get
          case NullRef => throw errorNullDereference(loc)
          case _ => throw errorNonPointerDereference(loc, evaluate(pointer, symbolicState).toString)
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
        val i = evaluate(index, symbolicState);
        i match {
          case Number(value, _) =>
            evaluate(array, symbolicState) match {
              case ArrVal(elems) if value >= elems.length || value < 0 =>
                throw errorArrayOutOfBounds(loc, value, elems.length)
              case ArrVal(elems) =>
                val o = symbolicState.getVal(elems(value))
                  symbolicState.getVal(elems(value)) match {
                    case Some(v) => v
                    case None => throw errorUninitializedReference(loc)
                }
              case _ => throw errorNonArrayAccess(loc, evaluate(array, symbolicState).toString)
            }
          case _ => throw errorNonIntArithmetics(loc)
        }
    }
  }

  private def getTarget(expr: Expr, symbolicState: SymbolicState): PointerVal = {
    expr match {
      case Identifier(name, loc) =>
        symbolicState.getSymbolicVal(name) match {
          case Some(PointerVal(address)) => PointerVal(address)
          case _ => throw errorUninitializedReference(loc)
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


  /*private def getTarget(expr: Expr, stackFrames: StackFrames): RefVal = {
    expr match {
      case Deref(pointer, loc) =>
        storage.get(
          getTarget(pointer, stackFrames)
        ) match {
          case Some(PointerVal(address)) => PointerVal(address)
          case Some(NullRef) => throw errorNullDereference(loc)
          case Some(v) => throw errorNonPointerDereference(pointer.loc, v)
          case None => throw errorUninitializedReference(pointer.loc)
        }
      case Identifier(name, loc) =>
        stackFrames.find(name) match {
          case Some(PointerVal(address)) => PointerVal(address)
          case _ if functionDeclarations.contains(name) => throw errorNonPointerDereference(loc, functionDeclarations(name))
          case _ => throw errorUninitializedReference(loc)
        }
      case e => throw errorNotAssignableExpression(e)
    }
  }*/




}

package microc.symbolic_execution

import com.microsoft.z3.{ArithExpr, ArithSort, BoolExpr, Context, IntExpr, IntNum, Status}
import microc.ast.{AndAnd, BinaryOp, CodeLoc, Divide, Equal, Expr, GreaterEqual, GreaterThan, Identifier, LowerEqual, LowerThan, Minus, Not, NotEqual, Null, Number, OrOr, Plus, Times}
import microc.symbolic_execution.Value.{IteVal, Symbolic, SymbolicExpr, SymbolicVal, UninitializedRef, Val}

import scala.collection.mutable

class ConstraintSolver(val ctx: Context) {


  def solveCondition(pathCondition: Expr, guard: Expr, symbolicState: SymbolicState): Status = {
    val ifPathCondition = BinaryOp(AndAnd, pathCondition, guard, guard.loc)
    val ifConstraint = createConstraintWithState(ifPathCondition, symbolicState)
    solveConstraint(ifConstraint)
  }


  def solveConstraint(constraint: com.microsoft.z3.Expr[_]): Status = {
    val solver = ctx.mkSolver()
    constraint match {
      case cond: BoolExpr => solver.add(cond)
      case cond: IntNum => solver.add(getCondition(cond))
    }
    solver.check()
  }


  def createConstraint(expr: Expr): com.microsoft.z3.Expr[_] = {
    expr match {
      case Not(expr, _) =>
        ctx.mkNot(getCondition(createConstraint(expr)))
      case BinaryOp(operator, left, right, _) =>
        operator match {
          case Plus => ctx.mkAdd(
            createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
            createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Minus => ctx.mkSub(
            createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
            createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Times => ctx.mkMul(
            createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
            createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Divide => ctx.mkDiv(
            createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
            createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Equal =>
            ctx.mkEq(
              createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
              createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
            )
          case NotEqual =>
            ctx.mkNot(
              ctx.mkEq(
                createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
                createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
              )
            )
          case GreaterThan =>
            ctx.mkGt(
              createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
              createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
            )
          case LowerThan =>
            ctx.mkLt(
              createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
              createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
            )
          case GreaterEqual =>
            ctx.mkGe(
              createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
              createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
            )
          case LowerEqual =>
            ctx.mkLe(
              createConstraint(left).asInstanceOf[ArithExpr[ArithSort]],
              createConstraint(right).asInstanceOf[ArithExpr[ArithSort]]
            )
          case AndAnd =>
            ctx.mkAnd(getCondition(createConstraint(left)), getCondition(createConstraint(right)))
          case OrOr =>
            ctx.mkOr(getCondition(createConstraint(left)), getCondition(createConstraint(right)))
        }
      case Identifier(name, loc) => ctx.mkIntConst(name)
      case Number(value, _) => ctx.mkInt(value)
      case v@SymbolicVal(_) => ctx.mkIntConst(v.name)
      case SymbolicExpr(expr, _) => createConstraint(expr)
      case Null(_) => ctx.mkInt(0)
    }
  }


  def valToExpr(v: Val, state: SymbolicState): com.microsoft.z3.Expr[_] = {
    v match {
      case Number(value, _) =>
        ctx.mkInt(value)
      case v@SymbolicVal(_) =>
        ctx.mkIntConst(v.name)
      case SymbolicExpr(expr, _) =>
        createConstraintWithState(expr, state)
      case IteVal(val1, val2, cond, _) =>
        ctx.mkITE(
          getCondition(createConstraintWithState(cond, state)),
          valToExpr(val1, state),
          valToExpr(val2, state)
        )
      case UninitializedRef => //TODO merge with symbolic val generation
        ctx.mkIntConst(Utility.generateRandomString())
      case _ =>
        throw new Exception("IMPLEMENT")
    }
  }


  def createConstraintWithState(expr: Expr, state: SymbolicState, allowNonInitializedVals: Boolean = false): com.microsoft.z3.Expr[_] = {
    expr match {
      case Not(expr, _) =>
          ctx.mkNot(getCondition(createConstraintWithState(expr, state, allowNonInitializedVals)))
      case BinaryOp(operator, left, right, _) =>
        operator match {
          case Plus => ctx.mkAdd(
            createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
            createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Minus => ctx.mkSub(
            createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
            createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Times => ctx.mkMul(
            createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
            createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Divide => ctx.mkDiv(
            createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
            createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Equal =>
            ctx.mkEq(
              createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
            )
          case NotEqual =>
            ctx.mkNot(
              ctx.mkEq(
                createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
                createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
              )
            )
          case GreaterThan =>
            ctx.mkGt(
              createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
            )
          case LowerThan =>
            ctx.mkLt(
              createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
            )
          case GreaterEqual =>
            ctx.mkGe(
              createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
            )
          case LowerEqual =>
            ctx.mkLe(
              createConstraintWithState(left, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state, allowNonInitializedVals).asInstanceOf[ArithExpr[ArithSort]]
            )
          case AndAnd =>
            ctx.mkAnd(
              getCondition(createConstraintWithState(left, state, allowNonInitializedVals)),
              getCondition(createConstraintWithState(right, state, allowNonInitializedVals))
            )
          case OrOr =>
            ctx.mkOr(
              getCondition(createConstraintWithState(left, state, allowNonInitializedVals)),
              getCondition(createConstraintWithState(right, state, allowNonInitializedVals))
            )
        }
      case Identifier(name, loc) =>
        valToExpr(state.getSymbolicVal(name, loc, allowNonInitializedVals), state)
      case Number(value, _) => ctx.mkInt(value)
      case v@SymbolicVal(_) => ctx.mkIntConst(v.name)
      case SymbolicExpr(expr, _) => createConstraintWithState(expr, state, allowNonInitializedVals)
      case Null(_) => ctx.mkInt(0)
      case IteVal(trueState, falseState, expr, _) =>
        ctx.mkITE(
          getCondition(createConstraintWithState(expr, state, allowNonInitializedVals)),
          valToExpr(trueState, state),
          valToExpr(falseState, state)
        )
    }
  }


  def applyVal(v: Val, state: SymbolicState, allowReturnNonInitialized: Boolean = false): Expr = {
    v match {
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyTheState(expr, state, allowReturnNonInitialized)
      case IteVal(val1, val2, cond, loc) =>
        (applyVal(val1, state), applyVal(val2, state)) match {
          case (a: Symbolic, b: Symbolic) => IteVal(a, b, applyTheState(cond, state, allowReturnNonInitialized), loc)
          case (a: Symbolic, b) => IteVal(a, SymbolicExpr(b, loc), applyTheState(cond, state, allowReturnNonInitialized), loc)
          case (a, b: Symbolic) => IteVal(SymbolicExpr(a, loc), b, applyTheState(cond, state, allowReturnNonInitialized), loc)
          case (a, b) => IteVal(SymbolicExpr(a, loc), SymbolicExpr(b, loc), applyTheState(cond, state, allowReturnNonInitialized), loc)
        }
      case _ =>
        throw new Exception("IMPLEMENT")
    }
  }


  def applyTheState(expr: Expr, state: SymbolicState, allowReturnNonInitialized: Boolean = false): Expr = {
    var res = expr match {
      case Not(expr, loc) =>
        Not(applyTheState(expr, state, allowReturnNonInitialized), loc)
      case BinaryOp(operator, left, right, loc) => BinaryOp(operator, applyTheState(left, state, allowReturnNonInitialized), applyTheState(right, state, allowReturnNonInitialized), loc)
      case Identifier(name, loc) => applyVal(state.getSymbolicVal(name, loc, allowReturnNonInitialized), state, allowReturnNonInitialized)
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyTheState(expr, state, allowReturnNonInitialized)
    }
    if (res != expr) {
      res = applyTheState(res, state, allowReturnNonInitialized)
    }
    res
  }

  def applyTheStateOnce(expr: Expr, state: SymbolicState, allowReturnNonInitialized: Boolean = false): Expr = {
    expr match {
      case Not(expr, loc) =>
        Not(applyTheStateOnce(expr, state, allowReturnNonInitialized), loc)
      case BinaryOp(operator, left, right, loc) => BinaryOp(operator, applyTheStateOnce(left, state, allowReturnNonInitialized), applyTheStateOnce(right, state, allowReturnNonInitialized), loc)
      case Identifier(name, loc) =>
        val i = state.getSymbolicVal(name, loc, allowReturnNonInitialized)
        state.getSymbolicVal(name, loc, allowReturnNonInitialized) match {
          case n: Number => n
          case s: SymbolicVal => s
          case e: SymbolicExpr => e.value
          case _ => throw new Exception("IMPLEMENT")
        }
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyTheStateOnce(expr, state, allowReturnNonInitialized)
    }
  }

  def applyTheStateWithChangesAsFunctions(expr: Expr, symbolicState: SymbolicState, changes: mutable.HashMap[String, Expr => Expr]): Expr = {
    var res = expr match {
      case Not(expr, loc) =>
        Not(applyTheStateWithChangesAsFunctions(expr, symbolicState, changes), loc)
      case BinaryOp(operator, left, right, loc) => BinaryOp(operator, applyTheStateWithChangesAsFunctions(left, symbolicState, changes), applyTheStateWithChangesAsFunctions(right, symbolicState, changes), loc)
      case id@Identifier(name, loc) =>
        if (changes.contains(name) && Utility.varIsFromOriginalProgram(name)) {
          symbolicState.getSymbolicVal(name, loc, true) match {
            case SymbolicExpr(expr, _) => changes(name).apply(expr)
            case UninitializedRef => SymbolicVal(CodeLoc(0, 0))
            case _ =>
              id
          }
        }
        else {
          applyVal(symbolicState.getSymbolicVal(name, loc), symbolicState)
        }
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyTheStateWithChangesAsFunctions(expr, symbolicState, changes)
    }
    if (res != expr) {
      res = applyTheStateWithChangesAsFunctions(res, symbolicState, changes)
    }
    res
  }

  def getCondition(expr: com.microsoft.z3.Expr[_]): BoolExpr = {
    expr match {
      case op: BoolExpr => op
      case op: IntExpr => ctx.mkEq(op, ctx.mkInt(1))
      case op: IntNum =>
        ctx.mkEq(op, ctx.mkInt(1))
    }
  }

}

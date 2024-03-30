package microc.symbolic_execution

import com.microsoft.z3.{ArithExpr, ArithSort, BoolExpr, Context, IntExpr, IntNum, Status}
import microc.ast.{AndAnd, ArrayAccess, ArrayNode, BinaryOp, CodeLoc, Deref, Divide, Equal, Expr, FieldAccess, GreaterEqual, GreaterThan, Identifier, Input, LowerEqual, LowerThan, Minus, Not, NotEqual, Null, Number, OrOr, Plus, Times}
import microc.symbolic_execution.Value.{ArrVal, IteVal, NullRef, PointerVal, RecVal, Symbolic, SymbolicExpr, SymbolicVal, UninitializedRef, Val}

import scala.collection.mutable

class ConstraintSolver(val ctx: Context) {


  def solveCondition(pathCondition: Expr, guard: Expr, symbolicState: SymbolicState): Status = {
    val ifPathCondition = BinaryOp(AndAnd, pathCondition, guard, guard.loc)
    val ifConstraint = createConstraintWithState(ifPathCondition, symbolicState)
    solveConstraint(ifConstraint)
  }


  def solveConstraint(constraint: com.microsoft.z3.Expr[_]): Status = {
    val solver = ctx.mkSolver()
    solver.add(getCondition(constraint))
    solver.check()
  }


  def createConstraint(expr: Expr): com.microsoft.z3.Expr[_] = {
    expr match {
      case Not(expr, _) =>
        val numExpr = createConstraint(expr).asInstanceOf[ArithExpr[ArithSort]]
        val zero = ctx.mkInt(0)
        val one = ctx.mkInt(1)
        ctx.mkITE(ctx.mkEq(numExpr, zero), one, zero)
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


  def valToExpr(v: Val, state: SymbolicState, allowNonInitializedVals: Boolean = false): com.microsoft.z3.Expr[_] = {
    v match {
      case Number(value, _) =>
        ctx.mkInt(value)
      case v@SymbolicVal(_) =>
        ctx.mkIntConst(v.name)
      case SymbolicExpr(expr, _) =>
        createConstraintWithState(expr, state, allowNonInitializedVals)
      case IteVal(val1, val2, cond, _) =>
        ctx.mkITE(
          getCondition(createConstraintWithState(cond, state, allowNonInitializedVals)),
          valToExpr(val1, state, allowNonInitializedVals),
          valToExpr(val2, state, allowNonInitializedVals)
        )
      case UninitializedRef => //TODO merge with symbolic val generation
        ctx.mkIntConst(Utility.generateRandomString())
      case PointerVal(address) => ctx.mkInt(address)
      case NullRef => ctx.mkInt(0)
      case _ =>
        throw new Exception("IMPLEMENT")
    }
  }


  def createConstraintWithState(expr: Expr, state: SymbolicState, allowNonInitializedVals: Boolean = false): com.microsoft.z3.Expr[_] = {
    expr match {
      case Not(expr, _) =>
        val zero = ctx.mkInt(0)
        val one = ctx.mkInt(1)

        val innerResult = createConstraintWithState(expr, state, allowNonInitializedVals)
        val cond = innerResult match {
          case boolExpr: BoolExpr => boolExpr
          case numExpr: ArithExpr[_] =>
            ctx.mkNot( ctx.mkEq (numExpr, zero) )
        }
        ctx.mkITE(cond, zero, one)
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
              createConstraintWithState(left, state, allowNonInitializedVals),
              createConstraintWithState(right, state, allowNonInitializedVals)
            )
          case NotEqual =>
            ctx.mkNot(
              ctx.mkEq(
                createConstraintWithState(left, state, allowNonInitializedVals),
                createConstraintWithState(right, state, allowNonInitializedVals)
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
        valToExpr(state.getSymbolicVal(name, loc, allowNonInitializedVals), state, allowNonInitializedVals)
      case Number(value, _) => ctx.mkInt(value)
      case v@SymbolicVal(_) => ctx.mkIntConst(v.name)
      case SymbolicExpr(expr, _) => createConstraintWithState(expr, state, allowNonInitializedVals)
      case Null(_) => ctx.mkInt(0)
      case IteVal(trueState, falseState, expr, _) =>
        ctx.mkITE(
          getCondition(createConstraintWithState(expr, state, allowNonInitializedVals)),
          valToExpr(trueState, state, allowNonInitializedVals),
          valToExpr(falseState, state, allowNonInitializedVals)
        )
      case Input(_) =>
        ctx.mkIntConst(SymbolicVal(CodeLoc(0, 0)).name)
      case NullRef =>
        ctx.mkInt(0)
      case RecVal(_) =>
        ctx.mkInt(1)
      case PointerVal(_) =>
        ctx.mkInt(1)
      case ArrVal(_) =>
        ctx.mkInt(1)
      case a@ArrayAccess(_, _, _) =>
        valToExpr(getTarget(a, state, allowNonInitializedVals), state)
      case d@Deref(_, _) =>
        valToExpr(getTarget(d, state, allowNonInitializedVals), state)
      case FieldAccess(record, field, loc) =>
        val rec = getTarget(record, state, allowNonInitializedVals)
        rec match {
          case RecVal(fields) =>
            valToExpr(fields(field), state, allowNonInitializedVals)
          case _ =>
            throw new Exception("IMPLEMENT")
        }
      case _ =>
        throw new Exception("IMPLEMENT")
    }
  }

  private def getTarget(expr: Expr, symbolicState: SymbolicState, allowNonInitializedVals: Boolean): Val = {
    getTargetInner(expr, symbolicState) match {
      case v: Val => v
      case e: Expr =>
        SymbolicExpr(e, e.loc)
    }
  }

  private def getTargetInner(expr: Expr, symbolicState: SymbolicState): Expr = {
    expr match {
      case Identifier(name, loc) =>
        symbolicState.getSymbolicVal(name, loc).asInstanceOf[Symbolic]
      case ArrayAccess(array, index, loc) =>
        index match {
          case Number(value, _) =>
            val arr = getTargetInner(array, symbolicState)
            arr match {
              case ArrayNode(elems, _) =>
                elems(value)
              case ArrVal(elems) =>
                symbolicState.getVal(elems(value)).get.asInstanceOf[Symbolic]
              case _ =>
                throw new Exception("IMPLEMENT")
          case _ =>
            throw new Exception("IMPLEMENT")
            }
        }
      case Deref(pointer, loc) =>
        getTargetInner(pointer, symbolicState) match {
          case p@PointerVal(_) =>
            symbolicState.getVal(p).get.asInstanceOf[Symbolic]
          case _ =>
            throw new Exception("IMPLEMENT")
        }
      case a@ArrayNode(_, _) => a
      case _ =>
        throw new Exception("IMPLEMENT")
    }
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
          Utility.applyVal(symbolicState.getSymbolicVal(name, loc), symbolicState)
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
      case op: IntExpr => ctx.mkNot(ctx.mkEq(op, ctx.mkInt(0)))
      case op: IntNum =>
        ctx.mkNot(ctx.mkEq(op, ctx.mkInt(0)))
    }
  }

}

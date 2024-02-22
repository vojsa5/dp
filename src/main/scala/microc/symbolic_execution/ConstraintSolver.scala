package microc.symbolic_execution

import com.microsoft.z3.{ArithExpr, ArithSort, BoolExpr, Context, IntExpr, IntNum, Status}
import microc.ast.{AndAnd, BinaryOp, Divide, Equal, Expr, GreaterEqual, GreaterThan, Identifier, LowerEqual, LowerThan, Minus, Not, NotEqual, Null, Number, OrOr, Plus, Times}
import microc.symbolic_execution.Value.{IteVal, Symbolic, SymbolicExpr, SymbolicVal, Val}

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
      case _ => throw new Exception("IMPLEMENT")
    }
  }


  def createConstraintWithState(expr: Expr, state: SymbolicState): com.microsoft.z3.Expr[_] = {
    expr match {
      case Not(expr, _) =>
          ctx.mkNot(getCondition(createConstraintWithState(expr, state)))
      case BinaryOp(operator, left, right, _) =>
        operator match {
          case Plus => ctx.mkAdd(
            createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
            createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Minus => ctx.mkSub(
            createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
            createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Times => ctx.mkMul(
            createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
            createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Divide => ctx.mkDiv(
            createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
            createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Equal =>
            ctx.mkEq(
              createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
            )
          case NotEqual =>
            ctx.mkNot(
              ctx.mkEq(
                createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
                createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
              )
            )
          case GreaterThan =>
            ctx.mkGt(
              createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
            )
          case LowerThan =>
            ctx.mkLt(
              createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
            )
          case GreaterEqual =>
            ctx.mkGe(
              createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
            )
          case LowerEqual =>
            ctx.mkLe(
              createConstraintWithState(left, state).asInstanceOf[ArithExpr[ArithSort]],
              createConstraintWithState(right, state).asInstanceOf[ArithExpr[ArithSort]]
            )
          case AndAnd =>
            ctx.mkAnd(getCondition(createConstraintWithState(left, state)), getCondition(createConstraintWithState(right, state)))
          case OrOr =>
            ctx.mkOr(getCondition(createConstraintWithState(left, state)), getCondition(createConstraintWithState(right, state)))
        }
      case Identifier(name, loc) =>
        valToExpr(state.getSymbolicVal(name, loc), state)
      case Number(value, _) => ctx.mkInt(value)
      case v@SymbolicVal(_) => ctx.mkIntConst(v.name)
      case SymbolicExpr(expr, _) => createConstraintWithState(expr, state)
      case Null(_) => ctx.mkInt(0)
    }
  }


  def applyVal(v: Val, state: SymbolicState): Expr = {
    v match {
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyTheState(expr, state)
      case IteVal(val1, val2, cond, loc) =>
        (applyVal(val1, state), applyVal(val2, state)) match {
          case (a: Symbolic, b: Symbolic) => IteVal(a, b, applyTheState(cond, state), loc)
          case (a: Symbolic, b) => IteVal(a, SymbolicExpr(b, loc), applyTheState(cond, state), loc)
          case (a, b: Symbolic) => IteVal(SymbolicExpr(a, loc), b, applyTheState(cond, state), loc)
          case (a, b) => IteVal(SymbolicExpr(a, loc), SymbolicExpr(b, loc), applyTheState(cond, state), loc)
        }
      case _ => throw new Exception("IMPLEMENT")
    }
  }


  def applyTheState(expr: Expr, state: SymbolicState): Expr = {
    expr match {
      case Not(expr, loc) =>
        Not(applyTheState(expr, state), loc)
      case BinaryOp(operator, left, right, loc) => BinaryOp(operator, applyTheState(left, state), applyTheState(right, state), loc)
      case Identifier(name, loc) => applyVal(state.getSymbolicVal(name, loc), state)
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyTheState(expr, state)
    }
  }

  def applyTheState2(expr: Expr, symbolicState: SymbolicState, changes: mutable.HashMap[String, Expr => Expr]): Expr = {
    expr match {
      case Not(expr, loc) =>
        Not(applyTheState2(expr, symbolicState, changes), loc)
      case BinaryOp(operator, left, right, loc) => BinaryOp(operator, applyTheState2(left, symbolicState, changes), applyTheState2(right, symbolicState, changes), loc)
      case id@Identifier(name, loc) =>
        if (changes.contains(name)) {
          symbolicState.getSymbolicVal(name, loc) match {
            case SymbolicExpr(expr, _) =>
              changes(name).apply(expr) match {
                case n@Number(_, _) => n
                case v@SymbolicVal(_) => v
                case SymbolicExpr(expr, loc) => SymbolicExpr(expr, loc)
              }
            case _ =>
              id
          }
        }
        else {
          id
        }
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyTheState2(expr, symbolicState, changes)
    }
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

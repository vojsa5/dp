package microc.symbolic_execution

import com.microsoft.z3.{ArithExpr, ArithSort, BoolExpr, Context, IntExpr, IntNum, Status}
import microc.ast.{AndAnd, BinaryOp, Divide, Equal, Expr, GreaterThan, Identifier, LowerThan, Minus, Not, NotEqual, Number, OrOr, Plus, Times}
import microc.symbolic_execution.Value.{SymbolicExpr, SymbolicVal}

class ConstraintSolver(val ctx: Context) {


  def solveCondition(pathCondition: Expr, guard: Expr, symbolicState: SymbolicState): Status = {
    val ifPathCondition = BinaryOp(AndAnd, pathCondition, guard, guard.loc)
    val ifConstraint = createConstraintWithState(ifPathCondition, symbolicState)
    solveConstraint(ifConstraint)
  }


  def solveConstraint(constraint: com.microsoft.z3.Expr[_]): Status = {
    System.out.println(constraint)
    val solver = ctx.mkSolver()
    constraint match {
      case cond: BoolExpr => solver.add(cond)
    }
    solver.check()
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
          case AndAnd =>
            ctx.mkAnd(getCondition(createConstraintWithState(left, state)), getCondition(createConstraintWithState(right, state)))
          case OrOr =>
            ctx.mkOr(getCondition(createConstraintWithState(left, state)), getCondition(createConstraintWithState(right, state)))
        }
      case Identifier(name, loc) =>
        state.getSymbolicValForId(Identifier(name, loc)) match {
          case Number(value, _) =>
            ctx.mkInt(value)
          case v@SymbolicVal(_) =>
            ctx.mkIntConst(v.name)
          case SymbolicExpr(expr, _) =>
            createConstraintWithState(expr, state)
          case _ => throw new Exception("IMPLEMENT")
        }
      case Number(value, _) => ctx.mkInt(value)
      case v@SymbolicVal(_) => ctx.mkIntConst(v.name)
      case SymbolicExpr(expr, _) => createConstraintWithState(expr, state)
    }
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
          case AndAnd =>
            ctx.mkAnd(getCondition(createConstraint(left)), getCondition(createConstraint(right)))
          case OrOr =>
            ctx.mkOr(getCondition(createConstraint(left)), getCondition(createConstraint(right)))
        }
      case Identifier(name, _) => ctx.mkIntConst(name)
      case Number(value, _) => ctx.mkInt(value)
      case v@SymbolicVal(_) => ctx.mkIntConst(v.name)
      case SymbolicExpr(expr, _) => createConstraint(expr)
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

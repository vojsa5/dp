package microc.symbolic_execution

import com.microsoft.z3.{ArithExpr, ArithSort, BoolExpr, Context, IntNum, Status}
import microc.ast.{AndAnd, BinaryOp, CodeLoc, Divide, Equal, Expr, GreatThan, Identifier, Minus, Not, NotEqual, Number, OrOr, Plus, Times}
import microc.interpreter.Value.IntVal
import microc.symbolic_execution.Value.{SymbolicExpr, SymbolicVal, Val}

class ConstraintSolver() {

  val ctx = new Context()


  def solveCondition(pathCondition: Expr, guard: Expr, symbolicState: SymbolicState): Status = {
    val ifPathCondition = BinaryOp(AndAnd, pathCondition, guard, guard.loc)
    val ifConstraint = createConstraint(ifPathCondition, symbolicState)
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


  def createConstraint(expr: Expr, state: SymbolicState): com.microsoft.z3.Expr[_] = {
    expr match {
      case Not(expr, _) =>
          ctx.mkNot(getCondition(createConstraint(expr, state)))
      case BinaryOp(operator, left, right, _) =>
        operator match {
          case Plus => ctx.mkAdd(
            createConstraint(left, state).asInstanceOf[ArithExpr[ArithSort]],
            createConstraint(right, state).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Minus => ctx.mkSub(
            createConstraint(left, state).asInstanceOf[ArithExpr[ArithSort]],
            createConstraint(right, state).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Times => ctx.mkMul(
            createConstraint(left, state).asInstanceOf[ArithExpr[ArithSort]],
            createConstraint(right, state).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Divide => ctx.mkDiv(
            createConstraint(left, state).asInstanceOf[ArithExpr[ArithSort]],
            createConstraint(right, state).asInstanceOf[ArithExpr[ArithSort]]
          )
          case Equal =>
            ctx.mkEq(
              createConstraint(left, state).asInstanceOf[ArithExpr[ArithSort]],
              createConstraint(right, state).asInstanceOf[ArithExpr[ArithSort]]
            )
          case NotEqual =>
            ctx.mkNot(
              ctx.mkEq(
                createConstraint(left, state).asInstanceOf[ArithExpr[ArithSort]],
                createConstraint(right, state).asInstanceOf[ArithExpr[ArithSort]]
              )
            )
          case GreatThan =>
            ctx.mkGt(
              createConstraint(left, state).asInstanceOf[ArithExpr[ArithSort]],
              createConstraint(right, state).asInstanceOf[ArithExpr[ArithSort]]
            )
          case AndAnd =>
            ctx.mkAnd(getCondition(createConstraint(left, state)), getCondition(createConstraint(right, state)))
          case OrOr =>
            ctx.mkOr(getCondition(createConstraint(left, state)), getCondition(createConstraint(right, state)))
        }
      case Identifier(name, loc) =>
        state.getSymbolicValForId(Identifier(name, loc)) match {
          case Number(value, _) => ctx.mkInt(value)
          case v@SymbolicVal(_) => ctx.mkIntConst(v.name)
          case SymbolicExpr(expr, _) => createConstraint(expr, state)
          case _ => throw new Exception("IMPLEMENT")
        }
      case Number(value, _) => ctx.mkInt(value)
      case v@SymbolicVal(_) => ctx.mkIntConst(v.name)
      case SymbolicExpr(expr, _) => createConstraint(expr, state)
    }
  }

  def getCondition(expr: com.microsoft.z3.Expr[_]): BoolExpr = {
    expr match {
      case op: BoolExpr => op
      case op: IntNum =>
        ctx.mkEq(op, ctx.mkInt(1))
    }
  }

}

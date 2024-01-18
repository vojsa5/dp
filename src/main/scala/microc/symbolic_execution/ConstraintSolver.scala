package microc.symbolic_execution

import com.microsoft.z3.{ArithExpr, ArithSort, BoolExpr, Context, Status}
import microc.ast.{AndAnd, BinaryOp, Divide, Equal, Expr, GreatThan, Identifier, Minus, Not, Number, OrOr, Plus, Times}
import microc.symbolic_execution.Value.{SymbolicExpr, SymbolicVal}

class ConstraintSolver() {

  val ctx = new Context()


  def solveCondition(pathCondition: Expr, guard: Expr, symbolicState: SymbolicState): Status = {
    val ifPathCondition = BinaryOp(AndAnd, pathCondition, guard, guard.loc)
    val ifConstraint = createConstraint(ifPathCondition, symbolicState)
    solveConstraint(ifConstraint)
  }


  def solveConstraint(constraint: com.microsoft.z3.Expr[_]): Status = {
    val solver = ctx.mkSolver()
    constraint match {
      case cond: BoolExpr => solver.add(cond)
    }
    solver.check()
  }


  def createConstraint(expr: Expr, state: SymbolicState): com.microsoft.z3.Expr[_] = {
    expr match {
      case Not(expr, loc) =>
        createConstraint(expr, state) match {
          case op: BoolExpr => ctx.mkNot(op)
        }
      case BinaryOp(operator, left, right, loc) =>
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
          case GreatThan =>
            ctx.mkGt(
              createConstraint(left, state).asInstanceOf[ArithExpr[ArithSort]],
              createConstraint(right, state).asInstanceOf[ArithExpr[ArithSort]]
            )
          case AndAnd =>
            (createConstraint(left, state), createConstraint(right, state)) match {
              case (l: BoolExpr, r: BoolExpr) => ctx.mkAnd(l, r)
            }
          case OrOr =>
            (createConstraint(left, state), createConstraint(right, state)) match {
              case (l: BoolExpr, r: BoolExpr) => ctx.mkOr(l, r)
            }
        }
      case Identifier(name, loc) =>
        state.getSymbolicValForId(Identifier(name, loc)) match {
          case Number(value, _) => ctx.mkInt(value)
          case SymbolicVal(_) => ctx.mkIntConst(name)
          case SymbolicExpr(expr, _) => createConstraint(expr, state)
          case _ => throw new Exception("IMPLEMENT")
        }
      case Number(value, _) => ctx.mkInt(value)
      case SymbolicVal(loc) => ctx.mkIntConst(loc.toString)
      case SymbolicExpr(expr, _) => createConstraint(expr, state)
    }
  }

}

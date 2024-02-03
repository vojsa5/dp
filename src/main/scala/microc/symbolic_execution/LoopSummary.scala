package microc.symbolic_execution

import microc.ast.{AssignStmt, BinaryOp, CodeLoc, Divide, Expr, Identifier, IfStmt, Minus, Not, Number, Plus, Stmt, Times, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}
import microc.symbolic_execution.LoopSummary.simplifyArithExpr
import microc.symbolic_execution.Value.Symbolic

import java.util

object LoopSummary {

  def simplifyArithExpr(expr: Expr): Expr = {
    expr match {
      case n@Number(_, _) => n
      case BinaryOp(operator, left, right, loc) =>
        (simplifyArithExpr(left), simplifyArithExpr(right)) match {
          case (Number(value, loc), Number(value2, _)) =>
            operator match {
              case Plus => Number(value + value2, loc)
              case Minus => Number(value - value2, loc)
              case Times => Number(value * value2, loc)
              case Divide => Number(value / value2, loc)
            }
          case (a, b) =>
            BinaryOp(operator, a, b, loc)
        }
      case other => other
    }
  }
}


class LoopSummary(program: ProgramCfg) extends SymbolicExecutor(program) {

  val thetas = new util.HashMap[String, Symbolic]()

  def executeBackbones(): Unit = {

  }

  def executeBackbone(): Unit = {

  }

  def computeSummary(loop: CfgNode): Unit = {
    val symbolicState = new SymbolicState(loop, PathCondition.initial())
    step(symbolicState)
  }

  override def stepOnLoop(symbolicState: SymbolicState, loop: WhileStmt): Unit = {
    val nextState = symbolicState.getIfFalseState()
    step(nextState)
    symbolicState.returnValue = nextState.returnValue
  }

  def computeVariableChange(stmts: List[Stmt]): Map[String, (Expr, Int) => Expr] = {
    var variableChange = Map[String, (Expr, Int) => Expr]()
    val num_it_variable = "TODO make this dynamic"
    for (stmt <- stmts) {
      stmt match {
        case AssignStmt(id, expr, _) =>
          expr match {
            case BinaryOp(Plus, Identifier(name, loc1), n@Number(_, loc2), _) =>
              variableChange += (name -> ((x, iterations) => simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, Number(iterations, loc2), n, loc2), loc1))))
            case BinaryOp(Minus, Identifier(name, loc1), Number(value, loc2), _) =>
              variableChange += (name -> ((x, iterations) => simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, Number(iterations, loc2), Number(-value, loc2), loc2), loc1))))
            case _ =>
          }
        case _ =>
      }
    }
    variableChange
  }

  def getAllPathsInALoop(stmt: CfgNode): List[Path] = {
    var paths = List[Path]()
    val falsePath = new Path(List.empty, Number(1, stmt.ast.loc))
    paths = paths.appended(falsePath.addedCondition(Not(stmt.ast.asInstanceOf[WhileStmt].guard, stmt.ast.loc)))
    paths = paths.appendedAll(getAllPathsInALoop2(stmt.succ.minBy(node => node.id), stmt.id)
      .map(path => path.addedCondition(stmt.ast.asInstanceOf[WhileStmt].guard))
      )
    paths
  }

  private def getAllPathsInALoop2(stmt: CfgNode, loopId: Int): List[Path] = {
    var paths = List[Path]()
    paths = paths.appended(new Path(List[Stmt](), Number(1, CodeLoc(0, 0))))
    var curr = stmt
    while (curr.id != loopId) {
      curr.ast match {
        case IfStmt(guard, _, _, _) =>
          paths = paths.flatMap(
            path => {
              paths = getAllPathsInALoop2(curr.succ.head, loopId)
                .map(pathContinuation => pathContinuation.addedCondition(guard))
                .map(pathContinuation => path.appendedAsPath(pathContinuation))
              paths = paths.appendedAll(
                getAllPathsInALoop2(curr.succ.tail.head, loopId)
                  .map(pathContinuation => pathContinuation.addedCondition(Not(guard, guard.loc)))
                  .map(pathContinuation => path.appendedAsPath(pathContinuation)))
              paths
            }
          )
          return paths
        case stmt: Stmt =>
          paths = paths.map(path => path.appendedStatement(stmt))
          curr = curr.succ.head
      }
    }
    paths
  }

}

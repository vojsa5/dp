package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.ast.{AndAnd, BinaryOp, CodeLoc, Divide, Expr, GreaterThan, Identifier, LowerThan, Minus, Null, Number, Plus, Times}
import microc.cfg.CfgStmtNode
import microc.symbolic_execution.Value.SymbolicVal
import microc.{Examples, MicrocSupport}
import munit.FunSuite

import scala.util.Random

class PathSubsumptionTest extends FunSuite with MicrocSupport with Examples {

  def generateRandomExpr(): Expr = {
    val randomNumber = Random.nextInt(10)
    randomNumber match {
      case 1 => Number(0, CodeLoc(0, 0))
      case 2 => BinaryOp(Plus, generateRandomExpr(), generateRandomExpr(), CodeLoc(0, 0))
      case 3 => BinaryOp(Minus, generateRandomExpr(), generateRandomExpr(), CodeLoc(0, 0))
      case 4 => BinaryOp(Times, generateRandomExpr(), generateRandomExpr(), CodeLoc(0, 0))
      case 5 => BinaryOp(Divide, generateRandomExpr(), generateRandomExpr(), CodeLoc(0, 0))
      case _ => Null(CodeLoc(0, 0))
    }


  }

  test("subsumption") {
    val context = new Context()
    val constraintSolver = new ConstraintSolver(context)
    var pathSubsumption = new PathSubsumption(constraintSolver, context)
    val node = new CfgStmtNode(1, Null(CodeLoc(0, 0)))
    val symbolicState = new SymbolicState(null, PathCondition.initial())
    for (_ <- 0 to 10) {
      assert(pathSubsumption.checkSubsumption(node, generateRandomExpr(), new SymbolicState(null, PathCondition.initial())))
    }
    for (_ <- 0 to 10) {
      pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
      pathSubsumption.addAnnotation(node, constraintSolver.createConstraintWithState(generateRandomExpr(), symbolicState))
      assert(pathSubsumption.checkSubsumption(node, Number(1, CodeLoc(0, 0)), new SymbolicState(null, PathCondition.initial())))
    }
    for (_ <- 0 to 10) {
      pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
      pathSubsumption.addAnnotation(node, constraintSolver.createConstraintWithState(Number(1, CodeLoc(0, 0)), symbolicState))
      assert(!pathSubsumption.checkSubsumption(node, generateRandomExpr(), new SymbolicState(null, PathCondition.initial())))
    }

    val oldCondition = BinaryOp(
      AndAnd,
      BinaryOp(
        LowerThan,
        Identifier("x", CodeLoc(0, 0)),
        Number(10, CodeLoc(0, 0)),
        CodeLoc(0, 0)
      ),
      BinaryOp(
        GreaterThan,
        Identifier("x", CodeLoc(0, 0)),
        Number(0, CodeLoc(0, 0)),
        CodeLoc(0, 0)
      ),
      CodeLoc(0, 0)
    )
    val newCondition = BinaryOp(
      AndAnd,
      BinaryOp(
        LowerThan,
        Identifier("x", CodeLoc(0, 0)),
        Number(7, CodeLoc(0, 0)),
        CodeLoc(0, 0)
      ),
      BinaryOp(
        GreaterThan,
        Identifier("x", CodeLoc(0, 0)),
        Number(3, CodeLoc(0, 0)),
        CodeLoc(0, 0)
      ),
      CodeLoc(0, 0)
    )
    symbolicState.addedVar("x", SymbolicVal(CodeLoc(0, 0)))
    pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
    pathSubsumption.addAnnotation(
      node,
      constraintSolver.createConstraintWithState(oldCondition, symbolicState)
    )
    assert(!pathSubsumption.checkSubsumption(node, newCondition, symbolicState))
    pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
    pathSubsumption.addAnnotation(
      node,
      constraintSolver.createConstraintWithState(newCondition, symbolicState)
    )
    assert(pathSubsumption.checkSubsumption(node, oldCondition, symbolicState))
  }

}

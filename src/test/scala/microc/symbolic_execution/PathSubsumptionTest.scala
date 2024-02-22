package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.ast.{AndAnd, BinaryOp, CodeLoc, Divide, Expr, GreaterThan, Identifier, LowerThan, Minus, Null, Number, Plus, Times}
import microc.cfg.{CfgStmtNode, IntraproceduralCfgFactory}
import microc.symbolic_execution.Value.SymbolicVal
import microc.{Examples, MicrocSupport}
import munit.FunSuite

import scala.util.Random

class PathSubsumptionTest extends FunSuite with MicrocSupport with Examples {

  def generateRandomExpr(): Expr = {
    Random.nextInt(10) match {
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
    val symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
    symbolicState.addedVar("x", SymbolicVal(CodeLoc(0, 0)))
    for (_ <- 0 to 10) {
      assert(pathSubsumption.checkSubsumption(node, generateRandomExpr(), new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))))
    }
    for (_ <- 0 to 10) {
      pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
      pathSubsumption.addAnnotation(node, constraintSolver.createConstraintWithState(generateRandomExpr(), symbolicState))
      assert(pathSubsumption.checkSubsumption(node, Number(1, CodeLoc(0, 0)), new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))))
    }
    for (_ <- 0 to 10) {
      pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
      pathSubsumption.addAnnotation(node, constraintSolver.createConstraintWithState(Number(1, CodeLoc(0, 0)), symbolicState))
      assert(!pathSubsumption.checkSubsumption(node, generateRandomExpr(), new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))))
    }

    var oldCondition = BinaryOp(
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
    var newCondition = BinaryOp(
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


    oldCondition = BinaryOp(
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
        Number(3, CodeLoc(0, 0)),
        CodeLoc(0, 0)
      ),
      CodeLoc(0, 0)
    )
    newCondition = BinaryOp(
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
        Number(0, CodeLoc(0, 0)),
        CodeLoc(0, 0)
      ),
      CodeLoc(0, 0)
    )
    pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
    pathSubsumption.addAnnotation(
      node,
      constraintSolver.createConstraintWithState(oldCondition, symbolicState)
    )
    assert(pathSubsumption.checkSubsumption(node, newCondition, symbolicState))
    pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
    pathSubsumption.addAnnotation(
      node,
      constraintSolver.createConstraintWithState(newCondition, symbolicState)
    )
    assert(pathSubsumption.checkSubsumption(node, oldCondition, symbolicState))
  }


  test("path stopped by subsumption") {
    val code =
      """
        |main() {
        |  var x,y,z;
        |  x = input;
        |  if (input > 3) {
        |   y = 1;
        |  }
        |  else {
        |   y = 1;
        |  }
        |  z = 9;
        |  return z;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx);
    executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 0)
    assert(executor.statistics.numPaths == 2)
    null
  }


  test("path stopped by subsumption") {
    val code =
      """
        |main() {
        |  var x,y,z;
        |  x = input;
        |  if (input > 3) {
        |   y = 1;
        |  }
        |  else {
        |   y = 1;
        |  }
        |  z = 9;
        |  return z;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx);
    executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 0)
    assert(executor.statistics.numPaths == 2)
    null
  }

}

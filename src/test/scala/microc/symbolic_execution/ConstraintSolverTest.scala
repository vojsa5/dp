package microc.symbolic_execution

import com.microsoft.z3.{Context, Status}
import microc.ast.{CodeLoc, Not, Number}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class ConstraintSolverTest extends FunSuite with MicrocSupport with Examples {

  test("number as boolean") {
    val solver = new ConstraintSolver(new Context())

    solver.solveCondition(Number(1, CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), null) match {
      case Status.SATISFIABLE =>
      case _ =>
        fail("should be satisfiable")
    }
  }


  test("number as boolean - not") {
    val solver = new ConstraintSolver(new Context())

    solver.solveCondition(Number(1, CodeLoc(0, 0)), Not(Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), null) match {
      case Status.SATISFIABLE =>
      case _ =>
        fail("should be satisfiable")
    }
  }
}

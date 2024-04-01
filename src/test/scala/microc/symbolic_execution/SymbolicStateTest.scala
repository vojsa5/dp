package microc.symbolic_execution

import com.microsoft.z3.{Context, Status}
import microc.ast.{AssignStmt, BinaryOp, CodeLoc, Equal, GreaterThan, Identifier, LowerThan, Null, Number}
import microc.cfg.CfgStmtNode
import microc.symbolic_execution.Value.{IteVal, SymbolicVal}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class SymbolicStateTest extends FunSuite with MicrocSupport with Examples {

  test("test ite constraints") {
    var state = new SymbolicState(
      new CfgStmtNode(0, AssignStmt(Identifier("a", CodeLoc(0, 0)), Null(CodeLoc(0, 0)), CodeLoc(0, 0))),
      BinaryOp(Equal, Identifier("x", CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)),
      new SymbolicStore(Map.empty)
    )

    state = state.addedVar(
      "x",
      IteVal(
        Number(1, CodeLoc(0, 0)),
        Number(0, CodeLoc(0, 0)),
        BinaryOp(GreaterThan, Identifier("y", CodeLoc(0, 0)), Number(3, CodeLoc(0, 0)), CodeLoc(0, 0)),
        CodeLoc(0, 0)
      )
    )

    state = state.addedVar(
      "y",
      SymbolicVal(CodeLoc(0, 0))
    )

    val solver = new ConstraintSolver(new Context())
    var constraint = solver.createConstraintWithState(state.pathCondition, state)
    solver.solveConstraint(constraint) match {
      case Status.SATISFIABLE =>
      case _ => assert(false)
    }





    state = new SymbolicState(
      new CfgStmtNode(0, AssignStmt(Identifier("a", CodeLoc(0, 0)), Null(CodeLoc(0, 0)), CodeLoc(0, 0))),
      BinaryOp(Equal, Identifier("x", CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)),
      new SymbolicStore(Map.empty)
    )

    state = state.addedVar(
      "x",
      IteVal(
        Number(1, CodeLoc(0, 0)),
        Number(0, CodeLoc(0, 0)),
        BinaryOp(LowerThan, Identifier("y", CodeLoc(0, 0)), Number(3, CodeLoc(0, 0)), CodeLoc(0, 0)),
        CodeLoc(0, 0)
      )
    )

    state = state.addedVar(
      "y",
      Number(1, CodeLoc(0, 0))
    )

    constraint = solver.createConstraintWithState(state.pathCondition, state)
    solver.solveConstraint(constraint) match {
      case Status.SATISFIABLE =>
      case _ => assert(false)
    }







    state = new SymbolicState(
      new CfgStmtNode(0, AssignStmt(Identifier("a", CodeLoc(0, 0)), Null(CodeLoc(0, 0)), CodeLoc(0, 0))),
      BinaryOp(Equal, Identifier("x", CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)),
      new SymbolicStore(Map.empty)
    )

    state = state.addedVar(
      "x",
      IteVal(
        Number(1, CodeLoc(0, 0)),
        Number(0, CodeLoc(0, 0)),
        BinaryOp(LowerThan, Identifier("y", CodeLoc(0, 0)), Number(3, CodeLoc(0, 0)), CodeLoc(0, 0)),
        CodeLoc(0, 0)
      )
    )

    state = state.addedVar(
      "y",
      Number(5, CodeLoc(0, 0))
    )

    constraint = solver.createConstraintWithState(state.pathCondition, state)
    solver.solveConstraint(constraint) match {
      case Status.UNSATISFIABLE =>
      case _ => assert(false)
    }




  }

}

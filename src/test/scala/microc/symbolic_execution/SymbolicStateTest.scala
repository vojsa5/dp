package microc.symbolic_execution

import com.microsoft.z3.{Context, Status}
import microc.ast.{AssignStmt, BinaryOp, CodeLoc, Equal, GreaterThan, Identifier, IdentifierDecl, LowerThan, Not, Null, Number}
import microc.cfg.CfgStmtNode
import microc.symbolic_execution.Value.{IteVal, PointerVal, SymbolicVal}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class SymbolicStateTest extends FunSuite with MicrocSupport with Examples {

  test("test ite constraints") {
    var state = new SymbolicState(
      new CfgStmtNode(0, AssignStmt(Identifier("a", CodeLoc(0, 0)), Null(CodeLoc(0, 0)), CodeLoc(0, 0))),
      BinaryOp(Equal, Identifier("x", CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)),
      new SymbolicStore(Map.empty)
    )

    state = state.updateVar(
      "x",
      IteVal(
        state.addAlloc(Number(1, CodeLoc(0, 0))),
        state.addAlloc(Number(0, CodeLoc(0, 0))),
        BinaryOp(GreaterThan, Identifier("y", CodeLoc(0, 0)), Number(3, CodeLoc(0, 0)), CodeLoc(0, 0)),
        CodeLoc(0, 0)
      )
    )

    state = state.updateVar(
      "y",
      SymbolicVal(CodeLoc(0, 0))
    )

    val solver = new ConstraintSolver(new Context())
    var constraint = solver.createConstraint(state.pathCondition, state)
    solver.solveConstraint(constraint) match {
      case Status.SATISFIABLE =>
      case _ => assert(false)
    }





    state = new SymbolicState(
      new CfgStmtNode(0, AssignStmt(Identifier("a", CodeLoc(0, 0)), Null(CodeLoc(0, 0)), CodeLoc(0, 0))),
      BinaryOp(Equal, Identifier("x", CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)),
      new SymbolicStore(Map.empty)
    )

    state = state.updateVar(
      "x",
      IteVal(
        state.addAlloc(Number(1, CodeLoc(0, 0))),
          state.addAlloc(Number(0, CodeLoc(0, 0))),
        BinaryOp(LowerThan, Identifier("y", CodeLoc(0, 0)), Number(3, CodeLoc(0, 0)), CodeLoc(0, 0)),
        CodeLoc(0, 0)
      )
    )

    state = state.updateVar(
      "y",
      Number(1, CodeLoc(0, 0))
    )

    constraint = solver.createConstraint(state.pathCondition, state)
    solver.solveConstraint(constraint) match {
      case Status.SATISFIABLE =>
      case _ => assert(false)
    }







    state = new SymbolicState(
      new CfgStmtNode(0, AssignStmt(Identifier("a", CodeLoc(0, 0)), Null(CodeLoc(0, 0)), CodeLoc(0, 0))),
      BinaryOp(Equal, Identifier("x", CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)),
      new SymbolicStore(Map.empty)
    )

    state = state.updateVar(
      "x",
      IteVal(
        state.addAlloc(Number(1, CodeLoc(0, 0))),
        state.addAlloc(Number(0, CodeLoc(0, 0))),
        BinaryOp(LowerThan, Identifier("y", CodeLoc(0, 0)), Number(3, CodeLoc(0, 0)), CodeLoc(0, 0)),
        CodeLoc(0, 0)
      )
    )

    state = state.updateVar(
      "y",
      Number(5, CodeLoc(0, 0))
    )

    constraint = solver.createConstraint(state.pathCondition, state)
    solver.solveConstraint(constraint) match {
      case Status.UNSATISFIABLE =>
      case _ => assert(false)
    }




  }

  test("merge ite in path condition") {
    val ite = IteVal(PointerVal(2), PointerVal(3), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0))
    BinaryOp(GreaterThan, ite, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0))

    val state = new SymbolicState(
      new CfgStmtNode(0, AssignStmt(Identifier("a", CodeLoc(0, 0)), Null(CodeLoc(0, 0)), CodeLoc(0, 0))),
      BinaryOp(GreaterThan, ite, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)),
      new SymbolicStore(Map.empty)
    )
    val sv = SymbolicVal(CodeLoc(0, 0))

    state.addVar(IdentifierDecl("a", CodeLoc(0, 0)))
    state.updateVar("a", Number(1, CodeLoc(0, 0)))
    state.updateVar("a", Number(2, CodeLoc(0, 0)))
    state.updateVar("a", Number(3, CodeLoc(0, 0)))
    state.updateVar("a", sv)

    val state2 = new SymbolicState(
      new CfgStmtNode(0, AssignStmt(Identifier("a", CodeLoc(0, 0)), Null(CodeLoc(0, 0)), CodeLoc(0, 0))),
      Number(1, CodeLoc(0, 0)),
      new SymbolicStore(Map.empty)
    )
    state2.addVar(IdentifierDecl("a", CodeLoc(0, 0)))
    state2.updateVar("a", sv)

    val solver = new ConstraintSolver(new Context())
    var constraint = solver.createConstraint(Not(state.pathCondition, CodeLoc(0, 0)), state)
    println(constraint)
    solver.solveConstraint(constraint) match {
      case Status.UNSATISFIABLE =>
      case _ => assert(false)
    }

    val mergedState = state.mergeStates(state2)

    constraint = solver.createConstraint(Not(mergedState.pathCondition, CodeLoc(0, 0)), mergedState)
    println(constraint)
    solver.solveConstraint(constraint) match {
      case Status.UNSATISFIABLE =>
      case _ => assert(false)
    }
  }

}

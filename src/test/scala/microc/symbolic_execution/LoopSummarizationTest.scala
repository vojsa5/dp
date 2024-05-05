package microc.symbolic_execution

import microc.ast.{AndAnd, ArrayAccess, AssignStmt, BinaryOp, CodeLoc, Equal, Expr, FieldAccess, FunDecl, GreaterThan, Identifier, IdentifierDecl, LowerEqual, LowerThan, NestedBlockStmt, Number, WhileStmt}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.{Examples, MicrocSupport, symbolic_execution}
import munit.FunSuite
import com.microsoft.z3.{BoolExpr, Context, Status}
import microc.symbolic_execution.Value.{ArrVal, PointerVal, RecVal, SymbolicExpr, SymbolicVal, UninitializedRef, Val}
import microc.symbolic_execution.optimizations.Path
import microc.symbolic_execution.optimizations.summarization.{LoopSummarization, PDA, Vertex}

import scala.collection.mutable


class LoopSummarizationTest extends FunSuite with MicrocSupport with Examples {



  test("capture effect of an sequential loop") {
    val code =
      """
        |main() {
        |  var k, i, n, m;
        |  k = 0;
        |  i = 0;
        |  n = input;
        |  m = input;
        |  while (n < m) {
        |   k = k + 5;
        |   i = i + 2;
        |   n = n + 1;
        |  }
        |  return k * i;
        |}
        |""".stripMargin;
    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val summary = new LoopSummarization(cfg).computeVariableChange(stmt.ast.asInstanceOf[WhileStmt].block.asInstanceOf[NestedBlockStmt].body,
      new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty)))
    assert(summary("k").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 50)
    assert(summary("i").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)

    null
  }


  test("get all paths in a sequential loop") {
    val code =
      """
        |main() {
        |  var k, i, n, m;
        |  k = 0;
        |  i = 0;
        |  n = input;
        |  m = input;
        |  while (n < m) {
        |   k = k + 5;
        |   i = i + 2;
        |   n = n + 1;
        |  }
        |  return k * i;
        |}
        |""".stripMargin;
    val ctx = new Context()
    val constraintSolver = new ConstraintSolver(ctx)
    var symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val executor = new LoopSummarization(cfg)
    var stmt: CfgNode = cfg.getFce("main")
    val decls = stmt.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    symbolicState = symbolicState.updateVar("n", SymbolicVal(CodeLoc(1, 0)))
    symbolicState = symbolicState.updateVar("m", SymbolicVal(CodeLoc(2, 0)))
    symbolicState = symbolicState.updateVar("k", Number(0, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("i", Number(0, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("_t1", SymbolicExpr(BinaryOp(LowerThan, Identifier("n", CodeLoc(0, 0)), Identifier("m", CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    symbolicState = symbolicState.updateVar("_t2", UninitializedRef)
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    assert(paths.size == 2)
    var reachedEmpty = false
    for (i <- 0 until 2) {
      if (paths(i).statements.length == 1) {
        if (!reachedEmpty) {
          val n = ctx.mkIntConst("n")
          val m = ctx.mkIntConst("m")
          val comparison = ctx.mkGe(n, m)
          val constraint = ctx.mkEq(constraintSolver.createConstraint(paths(i).condition, symbolicState), comparison)
          val solver = ctx.mkSolver()
          constraint match {
            case cond: BoolExpr => solver.add(cond)
          }
          solver.check() match {
            case Status.SATISFIABLE =>
            case _ => fail("")
          }
          reachedEmpty = true
        }
        else {
          fail("Multiple empty paths in the loop")
        }
      }
      else {
        val path = paths(i)
        assert(path.statements.size == 4)
        assert(path.statements(0).isInstanceOf[AssignStmt])
        assert(path.statements(1).isInstanceOf[AssignStmt])
        assert(path.statements(2).isInstanceOf[AssignStmt])
        assert(path.statements(3).isInstanceOf[AssignStmt])
        val n = ctx.mkIntConst("n")
        val m = ctx.mkIntConst("m")
        val comparison = ctx.mkLt(n, m)
        val constraint = ctx.mkEq(constraintSolver.createConstraint(paths(i).condition, symbolicState), comparison)
        val solver = ctx.mkSolver()
        constraint match {
          case cond: BoolExpr => solver.add(cond)
        }
        solver.check() match {
          case Status.SATISFIABLE =>
          case _ => fail("")
        }
      }
    }
    assert(reachedEmpty)
  }

  test("get all paths in a type1 loop") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;
    val ctx = new Context()
    val constraintSolver = new ConstraintSolver(ctx)
    var symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    symbolicState = symbolicState.updateVar("n", SymbolicVal(CodeLoc(1, 0)))
    symbolicState = symbolicState.updateVar("x", SymbolicVal(CodeLoc(2, 0)))
    symbolicState = symbolicState.updateVar("z", SymbolicVal(CodeLoc(3, 0)))
    symbolicState = symbolicState.updateVar("_t1", SymbolicExpr(BinaryOp(LowerThan, Identifier("x", CodeLoc(0, 0)), Identifier("n", CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    symbolicState = symbolicState.updateVar("_t2", SymbolicExpr(BinaryOp(GreaterThan, Identifier("z", CodeLoc(0, 0)), Identifier("x", CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    symbolicState = symbolicState.updateVar("_t3", UninitializedRef)
    symbolicState = symbolicState.updateVar("_t4", UninitializedRef)
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var main: CfgNode = cfg.getFce("main")
    var stmt = main
    val decls = stmt.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    symbolicState.variableDecls = decls
    val executor = new LoopSummarization(cfg)
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    assert(paths.size == 3)
    var sum = 0
    var path1: Option[Path] = None
    var path2: Option[Path] = None
    var path3: Option[Path] = None
    for (path <- paths) {
      assert(path.statements.size <= 3)
      val change = new LoopSummarization(cfg).computeVariableChange(path.statements, symbolicState)
      if (change.contains("x")) {
        assert(change("x").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 10)
        assert(change("x").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        assert(change("x").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        val x = ctx.mkIntConst("x")
        val n = ctx.mkIntConst("n")
        val comparison1 = ctx.mkLt(x, n)
        val z = ctx.mkIntConst("z")
        val comparison2 = ctx.mkGt(z, x)
        val comparison = ctx.mkAnd(comparison1, comparison2)
        val constraint = ctx.mkEq(constraintSolver.createConstraint(path.condition, symbolicState), comparison)
        val solver = ctx.mkSolver()
        constraint match {
          case cond: BoolExpr => solver.add(cond)
        }
        solver.check() match {
          case Status.SATISFIABLE =>
          case _ => fail("")
        }
        path2 = Some(path)
      }
      else if (change.contains("z")) {
        assert(change("z").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 10)
        assert(change("z").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        assert(change("z").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        val x = ctx.mkIntConst("x")
        val n = ctx.mkIntConst("n")
        val comparison1 = ctx.mkLt(x, n)
        val z = ctx.mkIntConst("z")
        val comparison2 = ctx.mkLe(z, x)
        val comparison = ctx.mkAnd(comparison1, comparison2)
        val constraint = ctx.mkEq(constraintSolver.createConstraint(path.condition, symbolicState), comparison)
        val solver = ctx.mkSolver()
        constraint match {
          case cond: BoolExpr => solver.add(cond)
        }
        solver.check() match {
          case Status.SATISFIABLE =>
          case _ => fail("")
        }
        path1 = Some(path)
      }
      else {
        assert(change.sizeIs == 1)
        val x = ctx.mkIntConst("x")
        val n = ctx.mkIntConst("n")
        val comparison = ctx.mkGe(x, n)
        val constraint = ctx.mkEq(constraintSolver.createConstraint(path.condition, symbolicState), comparison)
        val solver = ctx.mkSolver()
        constraint match {
          case cond: BoolExpr => solver.add(cond)
        }
        solver.check() match {
          case Status.SATISFIABLE =>
          case _ => fail("")
        }
        path3 = Some(path)
      }
      sum = sum + path.statements.size
    }
    //assert(sum == 7)
//    assert(executor.computePathRelationship(path1.get, path2.get, main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)).nonEmpty)
//    assert(executor.computePathRelationship(path1.get, path3.get, main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)).isEmpty)
//    assert(executor.computePathRelationship(path2.get, path1.get, main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)).nonEmpty)
//    assert(executor.computePathRelationship(path2.get, path3.get, main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)).nonEmpty)
//    assert(executor.computePathRelationship(path3.get, path1.get, main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)).isEmpty)
//    assert(executor.computePathRelationship(path3.get, path2.get, main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)).isEmpty)
  }


  test("get all paths in a type2 loop") {
    val code =
      """
        |main() {
        |  var a, i, j;
        |  a = input;
        |  i = input;
        |  j = input;
        |  while (i < 100) {
        |   if (a <= 5) {
        |     a = a + 1;
        |   }
        |   else {
        |     a =  a - 4;
        |   }
        |   if (j < 8) {
        |     j = j + 1;
        |   }
        |   else {
        |     j = j - 3;
        |   }
        |  }
        |  return 1;
        |}
        |""".stripMargin;
    val ctx = new Context()
    val constraintSolver = new ConstraintSolver(ctx)
    var symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    symbolicState = symbolicState.updateVar("a", SymbolicVal(CodeLoc(1, 0)))
    symbolicState = symbolicState.updateVar("i", SymbolicVal(CodeLoc(2, 0)))
    symbolicState = symbolicState.updateVar("j", SymbolicVal(CodeLoc(3, 0)))
    symbolicState = symbolicState.updateVar("_t1", SymbolicExpr(BinaryOp(LowerThan, Identifier("i", CodeLoc(0, 0)), Number(100, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    symbolicState = symbolicState.updateVar("_t2", SymbolicExpr(BinaryOp(LowerEqual, Identifier("a", CodeLoc(0, 0)), Number(5, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    symbolicState = symbolicState.updateVar("_t3", SymbolicExpr(BinaryOp(LowerThan, Identifier("j", CodeLoc(0, 0)), Number(8, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val decls = stmt.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    symbolicState.variableDecls = decls
    val executor = new LoopSummarization(cfg)
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    assert(paths.size == 5)
    var firstBranchEncountered = false
    var secondBranchEncountered = false
    var thirdBranchEncountered = false
    var fourthBranchEncountered = false
    for (path <- paths) {
      val change = new LoopSummarization(cfg).computeVariableChange(path.statements, symbolicState)

      if (!change.contains("j") && !change.contains("a")) {

      }
      else if (change("j").apply(Number(1, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 1 &&
        change("a").apply(Number(1, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 1) {
        assert(change("j").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 10)
        assert(change("j").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        assert(change("j").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        assert(change("a").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 10)
        assert(change("a").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        assert(change("a").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        firstBranchEncountered = true
      }
      else if (change("j").apply(Number(1, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 1 &&
        change("a").apply(Number(1, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -4) {
        assert(change("j").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 10)
        assert(change("j").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        assert(change("j").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        assert(change("a").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -40)
        assert(change("a").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -80)
        assert(change("a").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == -30)
        secondBranchEncountered = true
      }
      else if (change("j").apply(Number(1, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -3 &&
        change("a").apply(Number(1, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 1) {
        assert(change("j").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -30)
        assert(change("j").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -60)
        assert(change("j").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == -20)
        assert(change("a").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 10)
        assert(change("a").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        assert(change("a").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == 20)
        thirdBranchEncountered = true
      }
      else if (change("j").apply(Number(1, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -3 &&
        change("a").apply(Number(1, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -4) {
        assert(change("j").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -30)
        assert(change("j").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -60)
        assert(change("j").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == -20)
        assert(change("a").apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -40)
        assert(change("a").apply(Number(20, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == -80)
        assert(change("a").apply(Number(10, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == -30)
        fourthBranchEncountered = true
      }
      else {
        fail("a path was not matched")
      }
    }
    assert(firstBranchEncountered)
    assert(secondBranchEncountered)
    assert(thirdBranchEncountered)
    assert(fourthBranchEncountered)
  }


//  test("PDA basic") {
//    val code =
//      """
//        |main() {
//        |  var n, x, z;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  while (x < n) {
//        |   if (z > x) {
//        |     x = x + 1;
//        |   }
//        |   else {
//        |     z = z + 1;
//        |   }
//        |  }
//        |  return 1 / (x - z);
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new LoopSummary(cfg)
//    var stmt: CfgNode = cfg.getFce("main")
//    val main = stmt
//
//    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
//
//    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
//    for (decl <- decls) {
//      symbolicState.addedVar(decl.name, SymbolicVal(decl.loc))
//    }
//
//    while (!stmt.ast.isInstanceOf[WhileStmt]) {
//      stmt = stmt.succ.head
//    }
//
//    val paths = executor.getAllPathsInALoop(stmt)
//    var vertices :List[Vertex] = List()
//    for (path <- paths) {
//      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
//
//    }
//    val constraintSolver = new ConstraintSolver(new Context())
//    val pda = PDA(executor, vertices, decls, constraintSolver, Number(1, CodeLoc(0, 0)), symbolicState)
//    pda.initialize()
//    assert(pda.entryStates.size == 3)
//    assert(pda.exitStates.size == 1)
//    assert(pda.edges.size == 3)
//
//    var trace = Trace()
//    val rec = new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]()
//    trace.summarizeTrace(pda, symbolicState, vertices(0), constraintSolver.applyTheState(vertices(0).condition, symbolicState), new mutable.HashMap(), rec)
//    assert(trace.resChanges.isEmpty)
//    trace = Trace()
//    trace.summarizeTrace(pda, symbolicState, vertices(2), Number(1, CodeLoc(0, 0)), new mutable.HashMap(), new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]())
//    assert(trace.resChanges.size >= 0)
//    for (initialX <- 0 to 5) {
//      for (initialIterationCount <- 0 to 5) {
//        val trueRes = initialX + initialIterationCount
//        for (change <- trace.resChanges("x")) {
//          change.apply(Number(initialX, CodeLoc(0, 0))) match {
//            case expr => {
//              val v = LoopSummary.getSymbolicValsFromExpr(expr)
//              assert(v.nonEmpty)
//              LoopSummary.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
//                case Number(value, _) =>
//                  assert(value == trueRes)
//                case _ =>
//                  assert(false)
//              }
//            }
//            case _ =>
//              assert(false)
//          }
//        }
//      }
//    }
//
//    for (initialX <- 0 to 5) {
//      for (initialIterationCount <- 0 to 5) {
//        val trueRes = initialX + initialIterationCount
//        for (change <- trace.resChanges("x")) {
//          change.apply(Number(initialX, CodeLoc(0, 0))) match {
//            case expr => {
//              val v = LoopSummary.getSymbolicValsFromExpr(expr)
//              assert(v.nonEmpty)
//              LoopSummary.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
//                case Number(value, _) =>
//                  assert(value == trueRes)
//                case _ =>
//                  assert(false)
//              }
//            }
//            case _ =>
//              assert(false)
//          }
//        }
//      }
//    }
//
//    null
//  }
//
//
//  test("PDA basic with expr check") {
//    val code =
//      """
//        |main() {
//        |  var n, x, z;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  while (x < n) {
//        |   if (z > x) {
//        |     x = x + 1;
//        |   }
//        |   else {
//        |     z = z + 1;
//        |   }
//        |  }
//        |  return 1 / (x - z);
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new LoopSummary(cfg)
//    var stmt: CfgNode = cfg.getFce("main")
//    val main = stmt
//
//    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
//
//    symbolicState.addedVar("x", Number(3, CodeLoc(0, 0)))
//    symbolicState.addedVar("n", Number(4, CodeLoc(0, 0)))
//    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
//    for (decl <- decls) {
//      if (decl.name != "x" && decl.name != "n") {
//        symbolicState.addedVar(decl.name, SymbolicVal(decl.loc))
//      }
//    }
//
//    while (!stmt.ast.isInstanceOf[WhileStmt]) {
//      stmt.ast match {
//        case AssignStmt(Identifier(name, _), expr, _) =>
//          if (name != "x" && name != "n") {
//            symbolicState.addedVar(name, executor.evaluate(expr, symbolicState))
//          }
//        case _ =>
//      }
//      stmt = stmt.succ.head
//    }
//
//    val paths = executor.getAllPathsInALoop(stmt)
//    var vertices :List[Vertex] = List()
//    for (path <- paths) {
//      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
//
//    }
//    val constraintSolver = new ConstraintSolver(new Context())
//    val pda = PDA(executor, vertices, decls, constraintSolver, Number(1, CodeLoc(0, 0)), symbolicState)
//    pda.initialize()
//    assert(pda.entryStates.size == 2)
//    assert(pda.exitStates.size == 1)
//    assert(pda.edges.size == 3)
//
//    var trace = Trace()
//    val rec = new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]()
//    trace.summarizeTrace(pda, symbolicState, vertices(0), constraintSolver.applyTheState(vertices(0).condition, symbolicState), new mutable.HashMap(), rec)
//    constraintSolver.solveConstraint(constraintSolver.createConstraint(trace.resCondition)) match {
//      case Status.UNSATISFIABLE =>
//      case _ => assert(false)
//    }
//
//    trace = Trace()
//    trace.summarizeTrace(pda, symbolicState, vertices(1), constraintSolver.applyTheState(vertices(1).condition, symbolicState), new mutable.HashMap(), rec)
//    constraintSolver.solveConstraint(constraintSolver.createConstraint(trace.resCondition)) match {
//      case Status.SATISFIABLE =>
//      case _ => assert(false)
//    }
//
//    trace = Trace()
//    trace.summarizeTrace(pda, symbolicState, vertices(2), constraintSolver.applyTheState(vertices(2).condition, symbolicState), new mutable.HashMap(), rec)
//    constraintSolver.solveConstraint(constraintSolver.createConstraint(trace.resCondition)) match {
//      case Status.SATISFIABLE =>
//      case _ => assert(false)
//    }
//  }
//
//
//  test("PDA basic with expr check 2") {
//    val code =
//      """
//        |main() {
//        |  var n, x, z;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  while (x < n) {
//        |   if (z > x) {
//        |     x = x + 1;
//        |   }
//        |   else {
//        |     z = z + 1;
//        |   }
//        |  }
//        |  return 1 / (x - z);
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new LoopSummary(cfg)
//    var stmt: CfgNode = cfg.getFce("main")
//    val main = stmt
//
//    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
//
//    symbolicState.addedVar("x", Number(4, CodeLoc(0, 0)))
//    symbolicState.addedVar("n", Number(3, CodeLoc(0, 0)))
//    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
//    for (decl <- decls) {
//      if (decl.name != "x" && decl.name != "n") {
//        symbolicState.addedVar(decl.name, SymbolicVal(decl.loc))
//      }
//    }
//
//    while (!stmt.ast.isInstanceOf[WhileStmt]) {
//      stmt.ast match {
//        case AssignStmt(Identifier(name, _), expr, _) =>
//          if (name != "x" && name != "n") {
//            symbolicState.addedVar(name, executor.evaluate(expr, symbolicState))
//          }
//        case _ =>
//      }
//      stmt = stmt.succ.head
//    }
//
//    val paths = executor.getAllPathsInALoop(stmt)
//    var vertices: List[Vertex] = List()
//    for (path <- paths) {
//      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
//
//    }
//    val constraintSolver = new ConstraintSolver(new Context())
//    val pda = PDA(executor, vertices, decls, constraintSolver, Number(1, CodeLoc(0, 0)), symbolicState)
//    pda.initialize()
//    assert(pda.entryStates.size == 1)
//    assert(pda.exitStates.size == 1)
//    assert(pda.edges.size == 3)
//
//    var trace = Trace()
//    val rec = new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]()
//
//    trace.summarizeTrace(pda, symbolicState, vertices(0), constraintSolver.applyTheState(vertices(0).condition, symbolicState), new mutable.HashMap(), rec)
//    constraintSolver.solveConstraint(constraintSolver.createConstraint(trace.resCondition)) match {
//      case Status.SATISFIABLE =>
//      case _ => assert(false)
//    }
//
//    trace = Trace()
//    trace.summarizeTrace(pda, symbolicState, vertices(1), constraintSolver.applyTheState(vertices(1).condition, symbolicState), new mutable.HashMap(), rec)
//    constraintSolver.solveConstraint(constraintSolver.createConstraint(trace.resCondition)) match {
//      case Status.UNSATISFIABLE =>
//      case _ => assert(false)
//    }
//    assert(trace.resChanges.isEmpty)
//
//    trace = Trace()
//    trace.summarizeTrace(pda, symbolicState, vertices(2), constraintSolver.applyTheState(vertices(2).condition, symbolicState), new mutable.HashMap(), rec)
//    constraintSolver.solveConstraint(constraintSolver.createConstraint(trace.resCondition)) match {
//      case Status.UNSATISFIABLE =>
//      case _ => assert(false)
//    }
//    assert(trace.resChanges.isEmpty)
//  }
//
//
//  test("PDA more than just incrementation") {
//    val code =
//      """
//        |main() {
//        |  var n, x, z;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  while (x < n) {
//        |   if (z > x) {
//        |     x = x + 5;
//        |   }
//        |   else {
//        |     z = z + 10;
//        |   }
//        |  }
//        |  return 1 / (x - z);
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    var stmt: CfgNode = cfg.getFce("main")
//    val main = stmt
//
//    while (!stmt.ast.isInstanceOf[WhileStmt]) {
//      stmt = stmt.succ.head
//    }
//    val executor = new LoopSummary(cfg)
//    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
//    val paths = executor.getAllPathsInALoop(stmt)
//    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
//    for (decl <- decls) {
//      symbolicState.addedVar(decl.name, SymbolicVal(decl.loc))
//    }
//    var vertices :List[Vertex] = List()
//    for (path <- paths) {
//      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
//    }
//    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState)
//    pda.initialize()
//    assert(pda.entryStates.size == 3)
//    assert(pda.exitStates.size == 1)
//    assert(pda.edges.size == 3)
//
//    var trace = Trace()
//    trace.summarizeTrace(pda, symbolicState, vertices(0), Number(1, CodeLoc(0, 0)), new mutable.HashMap(), new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]())
//    assert(trace.resChanges.isEmpty)
//    trace = Trace()
//    trace.summarizeTrace(pda, symbolicState, vertices(2), Number(1, CodeLoc(0, 0)), new mutable.HashMap(), new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]())
//    assert(trace.resChanges.size >= 0)
//    for (initialX <- 0 to 5) {
//      for (initialIterationCount <- 0 to 5) {
//        val trueRes = initialX + 5 * initialIterationCount
//        for (change <- trace.resChanges("x")) {
//          change.apply(Number(initialX, CodeLoc(0, 0))) match {
//            case expr => {
//              val v = LoopSummary.getSymbolicValsFromExpr(expr)
//              assert(v.nonEmpty)
//              LoopSummary.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
//                case Number(value, _) =>
//                  assert(value == trueRes)
//                case _ =>
//                  assert(false)
//              }
//            }
//            case _ =>
//              assert(false)
//          }
//        }
//      }
//    }
//
//    for (initialX <- 0 to 5) {
//      for (initialIterationCount <- 0 to 5) {
//        val trueRes = initialX + 10 * initialIterationCount
//        for (change <- trace.resChanges("z")) {
//          change.apply(Number(initialX, CodeLoc(0, 0))) match {
//            case expr => {
//              val v = LoopSummary.getSymbolicValsFromExpr(expr)
//              assert(v.nonEmpty)
//              LoopSummary.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
//                case Number(value, _) =>
//                  assert(value == trueRes)
//                case _ =>
//                  assert(false)
//              }
//            }
//            case _ =>
//              assert(false)
//          }
//        }
//      }
//    }
//
//    null
//  }
//
//
//  test("PDA x updated in multiple branches") {
//    val code =
//      """
//        |main() {
//        |  var n, x, z;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  while (x < n) {
//        |   if (z > x) {
//        |     x = x + 1;
//        |   }
//        |   else {
//        |     z = z + 2;
//        |     x = x + 1;
//        |   }
//        |  }
//        |  return 1 / (x - z);
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    var stmt: CfgNode = cfg.getFce("main")
//    val main = stmt
//
//    while (!stmt.ast.isInstanceOf[WhileStmt]) {
//      stmt = stmt.succ.head
//    }
//    val executor = new LoopSummary(cfg)
//    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
//    val paths = executor.getAllPathsInALoop(stmt)
//    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
//    for (decl <- decls) {
//      symbolicState.addedVar(decl.name, SymbolicVal(decl.loc))
//    }
//    var vertices :List[Vertex] = List()
//    for (path <- paths) {
//      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
//
//    }
//    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState)
//    pda.initialize()
//    assert(pda.entryStates.size == 3)
//    assert(pda.exitStates.size == 1)
//    assert(pda.edges.size == 3)
//
//    var trace = Trace()
//    trace.summarizeTrace(pda, symbolicState, vertices(0), Number(1, CodeLoc(0, 0)), new mutable.HashMap(), new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]())
//    assert(trace.resChanges.isEmpty)
//    trace = Trace()
//    trace.summarizeTrace(pda, symbolicState, vertices(2), Number(1, CodeLoc(0, 0)), new mutable.HashMap(), new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]())
//    assert(trace.resChanges.size >= 0)
//    val ctx = new Context()
//    val constraintSolver = new ConstraintSolver(ctx)
//    for (initialX <- 0 to 5) {
//      for (initialIterationCount <- 0 to 5) {
//        val trueRes = initialX + 2 * initialIterationCount
//        val solver = ctx.mkSolver()
//        for (change <- trace.resChanges("x")) {
//          change.apply(Number(initialX, CodeLoc(0, 0))) match {
//            case expr => {
//              val v = LoopSummary.getSymbolicValsFromExpr(expr)
//              assert(v.nonEmpty)
//              val constraint = constraintSolver.createConstraint(BinaryOp(Equal, expr, Number(trueRes, CodeLoc(0, 0)), CodeLoc(0, 0)))
//              constraint match {
//                case cond: BoolExpr => solver.add(cond)
//              }
//            }
//            case _ =>
//              assert(false)
//          }
//        }
//        solver.check() match {
//          case Status.SATISFIABLE =>
//          case _ => fail("")
//        }
//      }
//    }
//
//    for (initialX <- 0 to 5) {
//      for (initialIterationCount <- 0 to 5) {
//        val trueRes = initialX + 3 * initialIterationCount
//        val solver = ctx.mkSolver()
//        for (change <- trace.resChanges("z")) {
//          change.apply(Number(initialX, CodeLoc(0, 0))) match {
//            case expr => {
//              val v = LoopSummary.getSymbolicValsFromExpr(expr)
//              assert(v.nonEmpty)
//              val constraint = constraintSolver.createConstraint(BinaryOp(Equal, expr, Number(trueRes, CodeLoc(0, 0)), CodeLoc(0, 0)))
//              constraint match {
//                case cond: BoolExpr => solver.add(cond)
//              }
//            }
//            case _ =>
//              assert(false)
//          3}
//        }
//      }
//    }
//
//    null
//  }


//  test("type1 summarization") {
//    val code =
//      """
//        |main() {
//        |  var n, x, z;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  while (x < n) {
//        |   if (z > x) {
//        |     x = x + 1;
//        |   }
//        |   else {
//        |     z = z + 1;
//        |   }
//        |  }
//        |  return 1 / (x - z);
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    var stmt: CfgNode = cfg.getFce("main")
//    val main = stmt
//
//    while (!stmt.ast.isInstanceOf[WhileStmt]) {
//      stmt = stmt.succ.head
//    }
//    val executor = new LoopSummary(cfg)
//    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
//    val paths = executor.getAllPathsInALoop(stmt)
//    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
//    for (decl <- decls) {
//      symbolicState.addedVar(decl.name, SymbolicVal(decl.loc))
//    }
//    var vertices :List[Vertex] = List()
//    for (path <- paths) {
//      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
//    }
//    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState)
//    pda.initialize()
//    assert(pda.entryStates.size == 3)
//    assert(pda.exitStates.size == 1)
//    assert(pda.edges.size == 3)
//
//    val summary = pda.summarizeType1Loop(symbolicState, Number(1, CodeLoc(0, 0)))
//
//    for (initialX <- 0 to 5) {
//      for (initialIterationCount <- 0 to 5) {
//        val trueRes = initialX + initialIterationCount
//        for (change <- summary._2("x")) {
//          change.apply(Number(initialX, CodeLoc(0, 0))) match {
//            case expr => {
//              val v = LoopSummary.getSymbolicValsFromExpr(expr)
//              assert(v.nonEmpty)
//              LoopSummary.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
//                case Number(value, _) =>
//                  println(value, trueRes)
//                  assert(value == trueRes)
//                case _ =>
//                  assert(false)
//              }
//            }
//            case _ =>
//              assert(false)
//          }
//        }
//      }
//    }
//
//    for (initialX <- 0 to 5) {
//      for (initialIterationCount <- 0 to 5) {
//        val trueRes = initialX + initialIterationCount
//        for (change <- summary._2("z")) {
//          change.apply(Number(initialX, CodeLoc(0, 0))) match {
//            case expr => {
//              val v = LoopSummary.getSymbolicValsFromExpr(expr)
//              assert(v.nonEmpty)
//              LoopSummary.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
//                case Number(value, _) =>
//                  assert(value == trueRes)
//                case _ =>
//                  assert(false)
//              }
//            }
//            case _ =>
//              assert(false)
//          }
//        }
//      }
//    }
//  }

  test("summary") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(!pda.checkForConnectedCycles())
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(0, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
              case expr => {
                var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                assert(v.nonEmpty)
                val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
                if (v.toSet.size >= 2) {
                  Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                    case Number(value, _) =>
                      println(value, trueRes)
                      assert(value == trueRes)
                    case a@_ =>
                      println(a)
                      assert(false)
                  }
                }
              }
              case _ =>
                assert(false)
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
                case expr => {
                  println(expr)
                  val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                  assert(v.nonEmpty)
                  if (v.toSet.size >= 2) {
                    Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                      case Number(value, _) =>
                        assert(value == trueRes)
                      case a@_ =>
                        println(a)
                        Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                          case Number(value, _) =>
                            assert(value == trueRes + initialIterationCount)
                          case _ =>
                            assert(false)
                        }
                    }
                  }
                }
                case _ =>
                  assert(false)
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    println(missingZ)
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }


  test("summary 1.5") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x + 1 < n) {
        |   if (z + 1 > x + 1) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
              case expr => {
                var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                assert(v.nonEmpty)
                val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
                if (v.toSet.size >= 2) {
                  Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                    case Number(value, _) =>
                      assert(value == trueRes)
                    case a@_ =>
                      println(a)
                      assert(false)
                  }
                }
              }
              case _ =>
                assert(false)
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
                case expr => {
                  println(expr)
                  val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                  assert(v.nonEmpty)
                  if (v.toSet.size >= 2) {
                    Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                      case Number(value, _) =>
                        assert(value == trueRes)
                      case a@_ =>
                        println(a)
                        Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                          case Number(value, _) =>
                            assert(value == trueRes + initialIterationCount)
                          case _ =>
                            assert(false)
                        }
                    }
                  }
                }
                case _ =>
                  assert(false)
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    println(missingZ)
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }



  test("summary 1.6") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x + 1 + 1 < n) {
        |   if (z + 1 + 1 > x + 1 + 1) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
              case expr => {
                var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                assert(v.nonEmpty)
                val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
                if (v.toSet.size >= 2) {
                  Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                    case Number(value, _) =>
                      assert(value == trueRes)
                    case a@_ =>
                      println(a)
                      assert(false)
                  }
                }
              }
              case _ =>
                assert(false)
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
                case expr => {
                  println(expr)
                  val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                  assert(v.nonEmpty)
                  if (v.toSet.size >= 2) {
                    Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                      case Number(value, _) =>
                        assert(value == trueRes)
                      case a@_ =>
                        println(a)
                        Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                          case Number(value, _) =>
                            assert(value == trueRes + initialIterationCount)
                          case _ =>
                            assert(false)
                        }
                    }
                  }
                }
                case _ =>
                  assert(false)
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    println(missingZ)
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }

//finish the code
  test("summary bigger increment") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 2;
        |   }
        |   else {
        |     z = z + 2;
        |   }
        |  }
        |
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + 2 * initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
              case expr => {
                var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                assert(v.nonEmpty)
                val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
                if (v.toSet.size >= 2) {
                  Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                    case Number(value, _) =>
                      assert(value - trueRes <= 1)
                    case a@_ =>
                      println(a)
                      assert(false)
                  }
                }
              }
              case _ =>
                assert(false)
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
                case expr => {
                  println(expr)
                  val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                  assert(v.nonEmpty)
                  if (v.toSet.size >= 2) {
                    Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                      case Number(value, _) =>
                        assert(value - trueRes <= 1)
                      case a@_ =>
                        Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                          case Number(value, _) =>
                            assert(value - trueRes - 2 * initialIterationCount <= 1)
                          case _ =>
                            assert(false)
                        }
                    }
                  }
                }
                case _ =>
                  assert(false)
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    println(missingZ)
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }


  test("summary2") {
    val code =
      """
        |main() {
        |  var n, x, z, a;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     a = x + 1;
        |     x = a;
        |   }
        |   else {
        |     a = z + 1;
        |     z = a;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
              case expr => {
                var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                assert(v.nonEmpty)
                val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
                if (v.toSet.size >= 2) {
                  Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                    case Number(value, _) =>
                      println(value, trueRes)
                      assert(value == trueRes)
                    case a@_ =>
                      println(a)
                      assert(false)
                  }
                }
              }
              case _ =>
                assert(false)
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
                case expr => {
                  println(expr)
                  val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                  assert(v.nonEmpty)
                  if (v.toSet.size >= 2) {
                    Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                      case Number(value, _) =>
                        assert(value == trueRes)
                      case a@_ =>
                        println(a)
                        Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                          case Number(value, _) =>
                            assert(value == trueRes + initialIterationCount)
                          case _ =>
                            assert(false)
                        }
                    }
                  }
                }
                case _ =>
                  assert(false)
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    println(missingZ)
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }



  test("summary3") {
    val code =
      """
        |main() {
        |  var n, x, z, a;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     a = x;
        |     x = a + 1;
        |   }
        |   else {
        |     a = z;
        |     z = a + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
              case expr => {
                var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                assert(v.nonEmpty)
                val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
                if (v.toSet.size >= 2) {
                  Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                    case Number(value, _) =>
                      println(value, trueRes)
                      assert(value == trueRes)
                    case a@_ =>
                      println(a)
                      assert(false)
                  }
                }
              }
              case _ =>
                assert(false)
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
                case expr => {
                  println(expr)
                  val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                  assert(v.nonEmpty)
                  if (v.toSet.size >= 2) {
                    Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                      case Number(value, _) =>
                        assert(value == trueRes)
                      case a@_ =>
                        println(a)
                        Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                          case Number(value, _) =>
                            assert(value == trueRes + initialIterationCount)
                          case _ =>
                            assert(false)
                        }
                    }
                  }
                }
                case _ =>
                  assert(false)
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    println(missingZ)
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }


  test("summary arrays") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = [input];
        |  z = [input];
        |  while (x[0] < n) {
        |   if (z[0] > x[0]) {
        |     x[0] = x[0] + 1;
        |   }
        |   else {
        |     z[0] = z[0] + 1;
        |   }
        |  }
        |  return 1 / (x[0] - z[0]);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
      if (decl.name == "x" || decl.name == "z") {
        symbolicState.updateVar(decl.name, ArrVal(Array(symbolicState.getSymbolicValOpt(decl.name).get.asInstanceOf[PointerVal])))
      }
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState.deepCopy(), mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  {
              case (ArrayAccess(Identifier(name, _), _, loc), _) => name == "x" || name == "z"
              case (Identifier(_, _), _) => false
            }.get._2
            change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
              case expr => {
                var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                assert(v.nonEmpty)
                val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
                if (v.toSet.size >= 2) {
                  Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                    case Number(value, _) =>
                      println(value, trueRes)
                      assert(value == trueRes)
                    case a@_ =>
                      println(a)
                      assert(false)
                  }
                }
              }
              case _ =>
                assert(false)
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists {
              case (ArrayAccess(Identifier(name, _), _, loc), _) => name == "z"
              case (Identifier(_, _), _) => false
            }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  {
                case (ArrayAccess(Identifier(name, _), _, loc), _) => name == "z"
                case (Identifier(_, _), _) => false
              }.get._2
              change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
                case expr => {
                  println(expr)
                  val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                  assert(v.nonEmpty)
                  if (v.toSet.size >= 2) {
                    Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                      case Number(value, _) =>
                        assert(value == trueRes)
                      case a@_ =>
                        println(a)
                        Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                          case Number(value, _) =>
                            assert(value == trueRes + initialIterationCount)
                          case _ =>
                            assert(false)
                        }
                    }
                  }
                }
                case _ =>
                  assert(false)
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    println(missingZ)
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }



  test("summary records") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = {field: input};
        |  z = {field: input};
        |  while (x.field < n) {
        |   if (z.field > x.field) {
        |     x.field = x.field + 1;
        |   }
        |   else {
        |     z.field = z.field + 1;
        |   }
        |  }
        |  return 1 / (x.field - z.field);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
      if (decl.name == "x" || decl.name == "z") {
        val fields = mutable.HashMap[String, PointerVal]()
        fields.put("field", symbolicState.getSymbolicValOpt(decl.name).get)
        symbolicState.updateVar(decl.name, RecVal(fields))
      }
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState.deepCopy(), mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  {
              case (FieldAccess(Identifier(name, _), _, loc), _) => name == "x" || name == "z"
              case (Identifier(_, _), _) => false
            }.get._2
            change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
              case expr => {
                var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                assert(v.nonEmpty)
                val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
                if (v.size >= 2) {
                  Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                    case Number(value, _) =>
                      println(value, trueRes)
                      assert(value == trueRes)
                    case a@_ =>
                      println(a)
                      assert(false)
                  }
                }
              }
              case _ =>
                assert(false)
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists {
              case (FieldAccess(Identifier(name, _), _, loc), _) => name == "z"
              case (Identifier(_, _), _) => false
            }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  {
                case (FieldAccess(Identifier(name, _), _, loc), _) => name == "z"
                case (Identifier(_, _), _) => false
              }.get._2
              change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState) match {
                case expr => {
                  println(expr)
                  val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
                  assert(v.nonEmpty)
                  if (v.size >= 2) {
                    Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                      case Number(value, _) =>
                        assert(value == trueRes)
                      case a@_ =>
                        println(a)
                        Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                          case Number(value, _) =>
                            assert(value == trueRes + initialIterationCount)
                          case _ =>
                            assert(false)
                        }
                    }
                  }
                }
                case _ =>
                  assert(false)
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    println(missingZ)
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }


  test("nested") {
    var code =
      """
        |main() {
        |    var i, j, sum, res, n;
        |    i = 0;
        |    sum = 0;
        |    n = input;
        |    if (n <= 0) {
        |       n = 1;
        |    }
        |
        |    while (i < n) {
        |        j = 0;
        |        while (j < n) {
        |            sum = sum + 1;
        |            j = j + 1;
        |        }
        |        i = i + 1;
        |    }
        |
        |    if (sum == n * n) {
        |       res = 1;
        |    }
        |    else {
        |       res = 0;
        |    }
        |
        |    return 1 / res;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val whileStmt = stmt
    stmt = stmt.succ.minBy(node => node.id)
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }


    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(stmt, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()

    symbolicState.variableDecls = decls
    val summary = executor.summarizeLoop(symbolicState, mapping)
    symbolicState.programLocation = whileStmt
    val summary2 = executor.summarizeLoop(symbolicState, mapping)
    null
  }



  test("empty loop finishes") {
    var code =
      """
        |main() {
        |    while (input) {
        |
        |    }
        |    return 1;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new LoopSummarization(cfg)
    executor.run()
    null
  }





    test("capture change from var") {
    val code =
      """
        |main() {
        |    var i, a, k, n;
        |    i = 0;
        |    k = input;
        |    n = input;
        |    a = 1;
        |    while (k < n) {
        |       i = i + a;
        |       k = k + 1;
        |    }
        |    return 1;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt
    val decls = stmt.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }

    var symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    symbolicState = symbolicState.updateVar("i", Number(0, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("k", SymbolicVal(CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("n", SymbolicVal(CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("a", Number(1, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("_t1", SymbolicVal(CodeLoc(0, 0)))

    val executor = new LoopSummarization(cfg)
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)

    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    for (path <- paths) {
      if (path.changes.nonEmpty) {
        val change: Expr => Expr => SymbolicState => Expr = path.changes.find  { case (Identifier(name, loc), _) => name == "i" }.get._2
        println(change.apply(Number(0, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))))
        println(change.apply(Number(0, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))))
        println(change.apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))))
        assert(change.apply(Number(0, CodeLoc(0, 0))).apply(Number(10, CodeLoc(0, 0))).asInstanceOf[Number].value == 10)
        assert(change.apply(Number(0, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 0)
        assert(change.apply(Number(10, CodeLoc(0, 0))).apply(Number(0, CodeLoc(0, 0))).asInstanceOf[Number].value == 10)
      }
    }
    null
  }



  test("uncomputable change") {
    var code =
      """
        |main() {
        |    var i, j, k, n;
        |    i = 0;
        |    k = input;
        |    n = input;
        |    j = 0;
        |    while (k < n) {
        |       j = j + 1;
        |       i = i + j;
        |    }
        |    return 1;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt
    val decls = stmt.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }

    var symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    symbolicState = symbolicState.updateVar("j", Number(1, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("i", Number(0, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("k", SymbolicVal(CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("n", SymbolicVal(CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("_t1", SymbolicVal(CodeLoc(0, 0)))

    val executor = new LoopSummarization(cfg)
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.isEmpty)
  }


  test("summary type2") {
    val code =
      """
        |main() {
        |  var i, j, a;
        |  i = input;
        |  j = input;
        |  a = input;
        |  while (i < 100) {
        |   if (a <= 5) {
        |     a = a + 1;
        |   }
        |   else {
        |     a = a - 4;
        |   }
        |   if (j < 8) {
        |     j = j + 1;
        |   }
        |   else {
        |     j = j - 3;
        |   }
        |   i = i + 1;
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    assert(!pda.checkForConnectedCycles())
    pda.initialize()
    for (edge <- pda.edges) {
      if (edge._1.statements.size > 1) {
        assert(edge._2.size == 4)
      }
      else {
        assert(edge._2.isEmpty)
      }
    }
    null
  }


  test("summary type3") {
    val code =
      """
        |main() {
        |  var i, j, k, n;
        |  i = input;
        |  k = input;
        |  n = input;
        |  while (i < n) {
        |     j = input;
        |     if (j <= 1) {
        |        j = 1;
        |     }
        |     i = i + j;
        |     k = k + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.isEmpty)
  }



  test("summary type3 arrays") {
    val code =
      """
        |main() {
        |  var i, j, k, n;
        |  i = [input];
        |  k = [input];
        |  n = [input];
        |  while (i[0] < n[0]) {
        |     j = [input];
        |     if (j[0] <= 1) {
        |        j[0] = 1;
        |     }
        |     i[0] = i[0] + j[0];
        |     k[0] = k[0] + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
      if (decl.name == "i" || decl.name == "k" || decl.name == "n") {
        symbolicState.updateVar(decl.name, ArrVal(Array(PointerVal(symbolicState.symbolicStore.storage.size - 1))))
      }
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.isEmpty)
  }



  test("summary type3 arrays arrays") {
    val code =
      """
        |main() {
        |  var i, j, k, n;
        |  i = [[input]];
        |  k = [[input]];
        |  n = [[input]];
        |  while (i[0][0] < n[0][0]) {
        |     j = [[input]];
        |     if (j[0][0] <= 1) {
        |        j[0][0] = 1;
        |     }
        |     i[0][0] = i[0][0] + j[0][0];
        |     k[0][0] = k[0][0] + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
      if (decl.name == "i" || decl.name == "k" || decl.name == "n") {
        symbolicState.updateVar(decl.name, ArrVal(Array(PointerVal(symbolicState.symbolicStore.storage.size - 1))))
        symbolicState.updateVar(decl.name, ArrVal(Array(PointerVal(symbolicState.symbolicStore.storage.size - 1))))
      }
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.isEmpty)
  }


  test("change identity function") {
    val code =
      """
        |main() {
        |  var i, j, k, n;
        |  i = input;
        |  k = 1;
        |  n = input;
        |  while (i < n) {
        |     k = k;
        |     j = k;
        |     i = i + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.updateVar("k", Number(1, CodeLoc(0, 0)))
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    for (path <- paths) {
      if (path.changes.nonEmpty) {
        val j = path.changes.find(ch => ch._1.asInstanceOf[Identifier].name == "j").get._2.apply(Number(1, CodeLoc(0, 0))).apply(Number(1, CodeLoc(0, 0))).apply(symbolicState)
        j match {
          case Number(value, _) =>
            assert(value == 1)
          case _ =>
            assert(false)
        }
        val k = path.changes.find(ch => ch._1.asInstanceOf[Identifier].name == "k").get._2.apply(Number(1, CodeLoc(0, 0))).apply(Number(1, CodeLoc(0, 0))).apply(symbolicState)
        k match {
          case Number(value, _) =>
            assert(value == 1)
          case _ =>
            assert(false)
        }
      }
    }
  }


  test("periods of cycles") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get

    val v1 = Vertex(paths(1), paths(1).condition, executor.pathToVertex(paths(1)), paths(1).iterations)
    val v2 = Vertex(paths(2), paths(2).condition, executor.pathToVertex(paths(2)), paths(2).iterations)
    var period = executor.computePeriod(v1, v2, v1)
    assert(period.nonEmpty)
    assert(period.get == 1)

    period = executor.computePeriod(v2, v1, v2)
    assert(period.nonEmpty)
    assert(period.get == 1)
    null
  }


  test("periods of cycles bigger increment") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 2;
        |   }
        |   else {
        |     z = z + 2;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get

    val v1 = Vertex(paths(1), paths(1).condition, executor.pathToVertex(paths(1)), paths(1).iterations)
    val v2 = Vertex(paths(2), paths(2).condition, executor.pathToVertex(paths(2)), paths(2).iterations)
    var period = executor.computePeriod(v1, v2, v1)
    assert(period.nonEmpty)
    assert(period.get == 1)

    period = executor.computePeriod(v2, v1, v2)
    assert(period.nonEmpty)
    assert(period.get == 1)
    null
  }

  test("periods of cycles bigger increment 2") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 2;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.variableDecls = decls
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashSet[Expr](), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get

    val v1 = Vertex(paths(1), paths(1).condition, executor.pathToVertex(paths(1)), paths(1).iterations)
    val v2 = Vertex(paths(2), paths(2).condition, executor.pathToVertex(paths(2)), paths(2).iterations)
    var period = executor.computePeriod(v1, v2, v1)
    assert(period.nonEmpty)
    assert(period.get == 1)

    period = executor.computePeriod(v2, v1, v2)
    assert(period.isEmpty)
    null
  }
}

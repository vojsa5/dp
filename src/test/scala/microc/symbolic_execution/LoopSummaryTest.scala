package microc.symbolic_execution

import microc.ast.{AndAnd, AssignStmt, BinaryOp, CodeLoc, Equal, Expr, FunDecl, GreaterThan, Identifier, LowerEqual, LowerThan, NestedBlockStmt, Number, WhileStmt}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.{Examples, MicrocSupport}
import munit.FunSuite
import com.microsoft.z3.{BoolExpr, Context, Status}
import microc.symbolic_execution.Value.{SymbolicExpr, SymbolicVal, Val}

import scala.collection.mutable


class LoopSummaryTest extends FunSuite with MicrocSupport with Examples {



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
    val summary = new LoopSummary(cfg).computeVariableChange(stmt.ast.asInstanceOf[WhileStmt].block.asInstanceOf[NestedBlockStmt].body,
      new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty)))
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
    var symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val loopSummary = new LoopSummary(cfg)
    var stmt: CfgNode = cfg.getFce("main")
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    symbolicState = symbolicState.addedVar("n", SymbolicVal(CodeLoc(1, 0)))
    symbolicState = symbolicState.addedVar("m", SymbolicVal(CodeLoc(2, 0)))
    symbolicState = symbolicState.addedVar("k", Number(0, CodeLoc(0, 0)))
    symbolicState = symbolicState.addedVar("i", Number(0, CodeLoc(0, 0)))
    symbolicState = symbolicState.addedVar("_t1", SymbolicExpr(BinaryOp(LowerThan, Identifier("n", CodeLoc(0, 0)), Identifier("m", CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    val pathsOpt = loopSummary.getAllPathsInALoop(stmt, symbolicState)
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
          val constraint = ctx.mkEq(constraintSolver.createConstraintWithState(paths(i).condition, symbolicState), comparison)
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
        val constraint = ctx.mkEq(constraintSolver.createConstraintWithState(paths(i).condition, symbolicState), comparison)
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
    var symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
    symbolicState = symbolicState.addedVar("n", SymbolicVal(CodeLoc(1, 0)))
    symbolicState = symbolicState.addedVar("x", SymbolicVal(CodeLoc(2, 0)))
    symbolicState = symbolicState.addedVar("z", SymbolicVal(CodeLoc(3, 0)))
    symbolicState = symbolicState.addedVar("_t1", SymbolicExpr(BinaryOp(LowerThan, Identifier("x", CodeLoc(0, 0)), Identifier("n", CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    symbolicState = symbolicState.addedVar("_t2", SymbolicExpr(BinaryOp(GreaterThan, Identifier("z", CodeLoc(0, 0)), Identifier("x", CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var main: CfgNode = cfg.getFce("main")
    var stmt = main
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummary(cfg)
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    assert(paths.size == 3)
    var sum = 0
    var path1: Option[Path] = None
    var path2: Option[Path] = None
    var path3: Option[Path] = None
    for (path <- paths) {
      assert(path.statements.size <= 3)
      val change = new LoopSummary(cfg).computeVariableChange(path.statements, symbolicState)
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
        val constraint = ctx.mkEq(constraintSolver.createConstraintWithState(path.condition, symbolicState), comparison)
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
        val constraint = ctx.mkEq(constraintSolver.createConstraintWithState(path.condition, symbolicState), comparison)
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
        val constraint = ctx.mkEq(constraintSolver.createConstraintWithState(path.condition, symbolicState), comparison)
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
    var symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
    symbolicState = symbolicState.addedVar("a", SymbolicVal(CodeLoc(1, 0)))
    symbolicState = symbolicState.addedVar("i", SymbolicVal(CodeLoc(2, 0)))
    symbolicState = symbolicState.addedVar("j", SymbolicVal(CodeLoc(3, 0)))
    symbolicState = symbolicState.addedVar("_t1", SymbolicExpr(BinaryOp(LowerThan, Identifier("i", CodeLoc(0, 0)), Number(100, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    symbolicState = symbolicState.addedVar("_t2", SymbolicExpr(BinaryOp(LowerEqual, Identifier("a", CodeLoc(0, 0)), Number(5, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    symbolicState = symbolicState.addedVar("_t3", SymbolicExpr(BinaryOp(LowerThan, Identifier("j", CodeLoc(0, 0)), Number(8, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummary(cfg)
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    assert(paths.size == 5)
    var firstBranchEncountered = false
    var secondBranchEncountered = false
    var thirdBranchEncountered = false
    var fourthBranchEncountered = false
    for (path <- paths) {
      val change = new LoopSummary(cfg).computeVariableChange(path.statements, symbolicState)

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
//    val symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
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
//    val symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
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
//    val symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
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
//    val symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
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
//    val symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
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
//    val symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
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
    val executor = new LoopSummary(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    for (decl <- decls) {
      symbolicState.addedVar(decl.name, SymbolicVal(decl.loc))
    }
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, decls, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState)

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change = trace._2("x")
            change.apply(Number(initialX, CodeLoc(0, 0))) match {
              case expr => {
                var v = LoopSummary.getSymbolicValsFromExpr(expr)
                assert(v.nonEmpty)
                val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
                if (v.size >= 2) {
                  LoopSummary.simplifyArithExpr(pda.applyIterationsCount(LoopSummary.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
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
            if (trace._2.contains("z")) {
              val change = trace._2("z")
              change.apply(Number(initialX, CodeLoc(0, 0))) match {
                case expr => {
                  println(expr)
                  val v = LoopSummary.getSymbolicValsFromExpr(expr)
                  assert(v.nonEmpty)
                  if (v.size >= 2) {
                    LoopSummary.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                      case Number(value, _) =>
                        assert(value == trueRes)
                      case a@_ =>
                        println(a)
                        LoopSummary.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
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


    val executor = new LoopSummary(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(stmt, PathCondition.initial(), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.addedVar(decl.name, SymbolicVal(decl.loc))
    }

    symbolicState.variableDecls = decls
    val summary = executor.summarizeLoop(symbolicState)
    symbolicState.nextStatement = whileStmt
    val summary2 = executor.summarizeLoop(symbolicState)
    null
  }

}

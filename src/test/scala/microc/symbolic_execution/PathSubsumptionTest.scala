package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.{AndAnd, BinaryOp, CodeLoc, Divide, Expr, GreaterEqual, GreaterThan, Identifier, LowerEqual, LowerThan, Minus, Null, Number, OrOr, Plus, Times, VarStmt, WhileStmt}
import microc.cfg.{CfgNode, CfgStmtNode, IntraproceduralCfgFactory}
import microc.symbolic_execution.Value.SymbolicVal
import microc.symbolic_execution.optimizations.merging.AggressiveStateMerging
import microc.symbolic_execution.optimizations.subsumption.PathSubsumption
import microc.symbolic_execution.optimizations.summarization.LoopSummarization
import microc.{Examples, MicrocSupport}
import munit.FunSuite

import scala.collection.mutable
import scala.concurrent.duration.DurationInt
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.util.Random
import scala.util.control.NonFatal

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
    var pathSubsumption = new PathSubsumption(constraintSolver)
    val node = new CfgStmtNode(1, Null(CodeLoc(0, 0)))
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    symbolicState.updateVar("x", SymbolicVal(CodeLoc(0, 0)))
//    for (_ <- 0 to 10) {
//      assert(pathSubsumption.checkSubsumption(node, generateRandomExpr(), new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))))
//    }
//    for (_ <- 0 to 10) {
//      pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
//      pathSubsumption.addAnnotation(node, constraintSolver.createConstraintWithState(generateRandomExpr(), symbolicState))
//      assert(pathSubsumption.checkSubsumption(node, Number(1, CodeLoc(0, 0)), new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))))
//    }
//    for (_ <- 0 to 10) {
//      pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
//      pathSubsumption.addAnnotation(node, constraintSolver.createConstraintWithState(Number(1, CodeLoc(0, 0)), symbolicState))
//      assert(!pathSubsumption.checkSubsumption(node, generateRandomExpr(), new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))))
//    }

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
//    pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
//    pathSubsumption.addAnnotation(
//      node,
//      constraintSolver.createConstraintWithState(oldCondition, symbolicState)
//    )
//    assert(!pathSubsumption.checkSubsumption(node, newCondition, symbolicState))
//    pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
//    pathSubsumption.addAnnotation(
//      node,
//      constraintSolver.createConstraintWithState(newCondition, symbolicState)
//    )
//    assert(pathSubsumption.checkSubsumption(node, oldCondition, symbolicState))


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
//    pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
//    pathSubsumption.addAnnotation(
//      node,
//      constraintSolver.createConstraintWithState(oldCondition, symbolicState)
//    )
//    assert(pathSubsumption.checkSubsumption(node, newCondition, symbolicState))
//    pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
//    pathSubsumption.addAnnotation(
//      node,
//      constraintSolver.createConstraintWithState(newCondition, symbolicState)
//    )
//    assert(pathSubsumption.checkSubsumption(node, oldCondition, symbolicState))
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx);
    executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 1)
    assert(executor.statistics.numPaths == 2)
    null
  }


  test("summarization from paper 1") {
    val code =
      """
        |main() {
        |  var x,y;
        |  x = 0;
        |  if (input) {
        |
        |  }
        |  else {
        |    y = input;
        |    if (y < 0) {
        |      y = 0 - y;
        |    }
        |    x = x + y;
        |  }
        |  if (x >= 0) {
        |
        |  }
        |  else {
        |    x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
    null
  }


  test("summarization from paper 2") {
    val code =
      """
        |main() {
        |  var p, a, x;
        |  p = input;
        |  x = input;
        |  if (p == 0) {
        |     p = 1;
        |  }
        |  if (input) {
        |     a = 1;
        |  }
        |  else {
        |     a = 0;
        |  }
        |  if (a != 0) {
        |     x = x + 1;
        |  }
        |  else {
        |     x = x - 1;
        |  }
        |  if (p == 0) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption > 0)
    assert(executor.statistics.numPaths > executor.statistics.stoppedWithSubsumption)
    null
  }


  test("loop inductivness") {
    val code =
      """
        |main() {
        |  var x, y, i, n;
        |  x = input;
        |  i = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |     x = x + 1;
        |     i = i + 1;
        |  }
        |  if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    val state = new SymbolicState(stmt, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    state.updateVar("x", SymbolicVal(CodeLoc(0, 0)))
    state.updateVar("i", SymbolicVal(CodeLoc(0, 0)))
    state.updateVar("n", SymbolicVal(CodeLoc(0, 0)))
    state.updateVar("y", state.getValueOfVar("x"))
    state.updateVar("_t1", SymbolicVal(CodeLoc(0, 0)))
    state.variableDecls = List.empty

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt.ast match {
        case VarStmt(vars, _) =>
          for (v <- vars) {
            if (Utility.varIsFromOriginalProgram(v.name)) {
              state.variableDecls = state.variableDecls.appended(v)
            }
          }
        case _ =>
      }
      stmt = stmt.succ.head
    }
    val ctx = new Context()
    val ps = new PathSubsumption(new ConstraintSolver(ctx))

    state.programLocation = stmt
    assert(ps.computeInductivness(state, BinaryOp(GreaterEqual, Identifier("x", CodeLoc(0, 0)), Identifier("y", CodeLoc(0, 0)), CodeLoc(0, 0)), new SymbolicExecutor(cfg), stmt))
    assert(!ps.computeInductivness(state, BinaryOp(LowerEqual, Identifier("x", CodeLoc(0, 0)), Identifier("y", CodeLoc(0, 0)), CodeLoc(0, 0)), new SymbolicExecutor(cfg), stmt))
  }

  test("remove non-inductive labels") {
    val code =
      """
        |main() {
        |  var x, y, i, n;
        |  x = input;
        |  i = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |     x = x + 1;
        |     i = i + 1;
        |  }
        |  if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    val state = new SymbolicState(stmt, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    state.updateVar("x", SymbolicVal(CodeLoc(0, 0)))
    state.updateVar("i", SymbolicVal(CodeLoc(0, 0)))
    state.updateVar("n", SymbolicVal(CodeLoc(0, 0)))
    state.updateVar("y", state.getValueOfVar("x"))
    state.updateVar("_t1", SymbolicVal(CodeLoc(0, 0)))
    state.variableDecls = List.empty

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt.ast match {
        case VarStmt(vars, _) =>
          for (v <- vars) {
            if (Utility.varIsFromOriginalProgram(v.name)) {
              state.variableDecls = state.variableDecls.appended(v)
            }
          }
        case _ =>
      }
      stmt = stmt.succ.head
    }
    val ctx = new Context()
    val ps = new PathSubsumption(new ConstraintSolver(ctx))

    state.programLocation = stmt
    val p = ps.removeNonInductiveLabels(
      state,
      BinaryOp(
        OrOr,
        BinaryOp(
          GreaterEqual,
          Identifier("x", CodeLoc(0, 0)),
          Identifier("y", CodeLoc(0, 0)),
          CodeLoc(0, 0)
        ),
        BinaryOp(
          LowerThan,
          Identifier("i", CodeLoc(0, 0)),
          Identifier("n", CodeLoc(0, 0)),
          CodeLoc(0, 0)
        ),
        CodeLoc(0, 0)
      ),
      new SymbolicExecutor(cfg),
      stmt
    )
    println("dfsf")
    assert(
      ps.removeNonInductiveLabels(
        state,
        BinaryOp(
          OrOr,
          BinaryOp(
            GreaterEqual,
            Identifier("x", CodeLoc(0, 0)),
            Identifier("y", CodeLoc(0, 0)),
            CodeLoc(0, 0)
          ),
          BinaryOp(
            LowerThan,
            Identifier("i", CodeLoc(0, 0)),
            Identifier("n", CodeLoc(0, 0)),
            CodeLoc(0, 0)
          ),
          CodeLoc(0, 0)
        ),
        new SymbolicExecutor(cfg),
        stmt
      ).equals(
        BinaryOp(
          GreaterEqual,
          Identifier("x", CodeLoc(0, 0)),
          Identifier("y", CodeLoc(0, 0)),
          CodeLoc(0, 0)
        )
      )
    )
  }


  test("summarization from paper 3") {
    val code =
      """
        |main() {
        |  var x, y, i, n;
        |  x = input;
        |  i = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |     x = x + 1;
        |     i = i + 1;
        |  }
        |  if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.numPaths == 3)
  }


  test("easy to find error") {
    val code =
      """
        |main() {
        |  var x, y, i, n;
        |  x = 0;
        |  i = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |     x = x + 1;
        |     i = i + 1;
        |  }
        |  if (x == 10) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    try {
      executor.run()
    }
    catch {
      case e: Exception =>
      case _ =>
        fail("An error should be found but was not")
    }
  }


  test("hard to find error") {
    val code =
      """
        |main() {
        |  var x, y, i, n;
        |  x = 0;
        |  i = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |     x = x + 1;
        |     i = i + 1;
        |  }
        |  if (x == 100000) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val future = Future {
      executor.run()
      fail("should be killed by timeout")
    }

    try {
      Await.ready(future, 10.seconds)
      assert(false)
    }
    catch {
      case _: TimeoutException =>
      case e =>
        fail(e.toString)
    }
  }



  test("summarization more complicated loop") {
    val code =
      """
        |main() {
        |  var x, y, i, n;
        |  x = input;
        |  i = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |     i = i + 1;
        |     if (input) {
        |        x = x + 1;
        |     }
        |  }
        |  if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.numPaths == 5)
  }


  test("nested loop") {
    val code =
      """
        |main() {
        |  var x, y, i, j, n;
        |  x = input;
        |  i = input;
        |  j = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |     i = i + 1;
        |     while (j < n) {
        |         x = x + 1;
        |         j = j + 1;
        |     }
        |  }
        |  if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val initialProgramSize = cfg.nodes.size
    val res = executor.run()
    assert(executor.statistics.numPaths == 5)
    assert(cfg.nodes.find(node => node.id == 15.0).get.succ.head.id == 12.0)
    assert(cfg.nodes.find(node => node.id == 16.0).get.succ.head.id == 9.0)
    assert(initialProgramSize == cfg.nodes.size)
  }


  test("nested loop with easy to find error") {
    val code =
      """
        |main() {
        |  var x, y, i, j, n;
        |  x = 0;
        |  i = input;
        |  j = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |     i = i + 1;
        |     while (j < n) {
        |         x = x + 1;
        |         j = j + 1;
        |     }
        |  }
        |  if (x == 10) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    try {
      executor.run()
    }
    catch {
      case e: Exception =>
      case _ =>
        fail("An error should be found but was not")
    }
  }


  test("nested loop with hard to find error") {
    val code =
      """
        |main() {
        |  var x, y, i, j, n;
        |  x = 0;
        |  i = input;
        |  j = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |     i = i + 1;
        |     while (j < n) {
        |         x = x + 1;
        |         j = j + 1;
        |     }
        |  }
        |  if (x == 1000000) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val future = Future {
      executor.run()
      fail("should be killed by timeout")
    }

    try {
      Await.ready(future, 10.seconds)
      assert(false)
    }
    catch {
      case _: TimeoutException =>
      case e =>
        fail(e.toString)
    }
  }


  test("empty loop") {
    val code =
      """
        |main() {
        |  var x, y, i, j, n;
        |  x = input;
        |  i = input;
        |  j = input;
        |  n = input;
        |  y = x;
        |  while (i < n) {
        |
        |  }
        |  if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val initialProgramSize = cfg.nodes.size
    val res = executor.run()
    assert(executor.statistics.numPaths == 3)
    assert(initialProgramSize == cfg.nodes.size)
  }

  test("possible error removes annotation") {
    val code =
      """
        |main() {
        |  var x, y, i;
        |  x = input;
        |  i = input;
        |  if (i == 0) {
        |     i = 1;
        |  }
        |  i = 1 / i;
        |  y = x;
        |  if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val subsumption = new PathSubsumption(new ConstraintSolver(ctx))
    val executor = new SymbolicExecutor(cfg, Some(subsumption), ctx, new DFSSearchStrategy());
    executor.run()
    assert(executor.statistics.numPaths == 3)
    assert(!subsumption.annotations.contains(cfg.nodes.find(node => node.id == 4.0).get))
    assert(!subsumption.annotations.contains(cfg.nodes.find(node => node.id == 8.0).get))
    null
  }



  test("possible error removes annotation 2") {
    val code =
      """
        |main() {
        |  var x, y, i, arr;
        |  x = input;
        |  i = input;
        |  arr = [0];
        |  if (i != 0) {
        |     i = 0;
        |  }
        |  arr[0] = arr[i];
        |  y = x;
        |  if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val subsumption = new PathSubsumption(new ConstraintSolver(ctx))
    val executor = new SymbolicExecutor(cfg, Some(subsumption), ctx, new DFSSearchStrategy());
    executor.run()
    assert(executor.statistics.numPaths == 3)
    assert(!subsumption.annotations.contains(cfg.nodes.find(node => node.id == 4.0).get))
    assert(!subsumption.annotations.contains(cfg.nodes.find(node => node.id == 8.0).get))
    null
  }


  test("no error at all") {
    val code =
      """
        |main() {
        |  var x,y;
        |  x = 0;
        |  if (input) {
        |
        |  }
        |  else {
        |    y = input;
        |    if (y < 0) {
        |      y = 0 - y;
        |    }
        |    x = x + y;
        |  }
        |  if (input) {
        |
        |  }
        |  else {
        |    output x;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    executor.run()
    assert(executor.statistics.numPaths == 4)
    null
  }


  test("pointers") {
    val code =
      """
        |main() {
        |  var x,y,z,a;
        |  z = 0;
        |  x = &z;
        |  if (input) {
        |
        |  }
        |  else {
        |    a = input;
        |    y = &a;
        |    if (*y < 0) {
        |      *y = 0 - *y;
        |    }
        |    *x = *x + *y;
        |  }
        |  if (*x >= 0) {
        |
        |  }
        |  else {
        |    *x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
    null
  }


  test("pointers pointers") {
    val code =
      """
        |main() {
        |  var x,y,z,z2,a,a2;
        |  z = 0;
        |  z2 = &z;
        |  x = &z2;
        |  if (input) {
        |
        |  }
        |  else {
        |    a = input;
        |    a2 = &a;
        |    y = &a2;
        |    if (**y < 0) {
        |      **y = 0 - **y;
        |    }
        |    **x = **x + **y;
        |  }
        |  if (**x >= 0) {
        |
        |  }
        |  else {
        |    **x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
    null
  }


  test("arrays") {
    val code =
      """
        |main() {
        |  var x,y;
        |  x = [0];
        |  if (input) {
        |
        |  }
        |  else {
        |    y = [input];
        |    if (y[0] < 0) {
        |      y[0] = 0 - y[0];
        |    }
        |    x[0] = x[0] + y[0];
        |  }
        |  if (x[0] >= 0) {
        |
        |  }
        |  else {
        |    x[0] = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
    null
  }



  test("arrays arrays") {
    val code =
      """
        |main() {
        |  var x,y;
        |  x = [[0]];
        |  if (input) {
        |
        |  }
        |  else {
        |    y = [[input]];
        |    if (y[0][0] < 0) {
        |      y[0][0] = 0 - y[0][0];
        |    }
        |    x[0][0] = x[0][0] + y[0][0];
        |  }
        |  if (x[0][0] >= 0) {
        |
        |  }
        |  else {
        |    x[0][0] = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
    null
  }


  test("records") {
    val code =
      """
        |main() {
        |  var x,y;
        |  x = {value: 0};
        |  if (input) {
        |
        |  }
        |  else {
        |    y = {value: input};
        |    if (y.value < 0) {
        |      y.value = 0 - y.value;
        |    }
        |    x.value = x.value + y.value;
        |  }
        |  if (x.value >= 0) {
        |
        |  }
        |  else {
        |    x.value = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
    null
  }


  test("pointers arrays") {
    val code =
      """
        |main() {
        |  var x,y,z,a;
        |  z = [0];
        |  x = &z;
        |  if (input) {
        |
        |  }
        |  else {
        |    a = [input];
        |    y = &a;
        |    if ((*y)[0] < 0) {
        |      (*y)[0] = 0 - (*y)[0];
        |    }
        |    (*x)[0] = (*x)[0] + (*y)[0];
        |  }
        |  if ((*x)[0] >= 0) {
        |
        |  }
        |  else {
        |    (*x)[0] = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
    null
  }


  test("arrays pointers") {
    val code =
      """
        |main() {
        |  var x,y,z,a;
        |  z = 0;
        |  x = [&z];
        |  if (input) {
        |
        |  }
        |  else {
        |    a = input;
        |    y = [&a];
        |    if (*y[0] < 0) {
        |      *y[0] = 0 - *y[0];
        |    }
        |    *x[0] = *x[0] + *y[0];
        |  }
        |  if (*x[0] >= 0) {
        |
        |  }
        |  else {
        |    *x[0] = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
    null
  }


  test("do not do path summarization for unclear array indices") {
    val code =
      """
        |main() {
        |  var x,y,z;
        |  x = [0, 0];
        |  z = input;
        |  if (z > 1) {
        |     z = 1;
        |  }
        |  if (z < 0) {
        |     z = 0;
        |  }
        |  if (input) {
        |
        |  }
        |  else {
        |    y = [input, input];
        |    if (y[z] < 0) {
        |      y[z] = 0 - y[z];
        |    }
        |    x[z] = x[z] + y[z];
        |  }
        |  if (x[z] >= 0) {
        |
        |  }
        |  else {
        |    x[z] = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    executor.run()
    assert(executor.statistics.numPaths == 11)
    null
  }


  test("condition obfuscated") {
    val code =
      """
        |main() {
        |  var x,y;
        |  x = 0;
        |  if (input) {
        |
        |  }
        |  else {
        |    y = input;
        |    if (y < 0) {
        |      y = 0 - y;
        |    }
        |    x = x + y;
        |  }
        |  if ([x][0] >= 0) {
        |
        |  }
        |  else {
        |    x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
    null
  }


  test("get paths weird loops finishes") {
    val code =
      """
        |main() {
        |  var x,y;
        |  while (input) {
        |     if (7) {}
        |     else {
        |         while (var10) {
        |             while (4) {}
        |             while (0) {}
        |         }
        |     }
        |  }
        |
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    var stmt: CfgNode = cfg.getFce("main")
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
    LoopSummarization.getAllPaths(stmt, stmt.id, new SymbolicState(stmt, Number(1, CodeLoc(0, 0)), new SymbolicStore(null)), executor)
    null
  }


  test("random generated test finishes with no error") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21;
        |  var0 = 2;
        |  var1 = [0,2,3,8,7,-1,1];
        |  var2 = {oaGrBnuZij:3,rewHZGUfuL:0};
        |  var3 = 8;
        |  var4 = 5;
        |  var5 = {qasYOcTZAu:4};
        |  var6 = [[6,8,4,3,-1,8,2],[0,4,2,3,-1,-1,0],[3,-1,7,-1,4,6,2],[5,1,1,1,2,0,5],[3,8,-1,3,6,2,8,4,1],[2,5,1,8,-1,6,1,5]];
        |  var7 = {RTRGMUWTKc:alloc 0};
        |  var8 = alloc 3;
        |  var9 = 6;
        |  var10 = -1;
        |  var11 = {WwllhQzzga:alloc 5};
        |  var12 = {eObqkYDAeF:0,wQFTpXtJGR:alloc [7,7,7,-1,3,2,5,-1],PfXGYhPMoV:[5,6,0,-1,1]};
        |  var13 = alloc 4;
        |  var14 = [2,5,5,0,1,1];
        |  var15 = 1;
        |  var16 = 4;
        |  var17 = 1;
        |  var18 = alloc 5;
        |  var19 = [alloc -1,alloc 5,alloc 8,alloc 7,alloc 3];
        |  var20 = {tlvWBMenWg:3};
        |  var21 = [5,3,1,0,4,8,0,7,-1];
        |  var14 = var14;
        |  var1 = var1;
        |  while ((var9 < var15)) {
        |    var21 = var21;
        |    while ((var0 < var10)) {
        |      var0 = (var0 + 1);
        |    }
        |    var9 = (var9 + 1);
        |  }
        |  while ((var17 < var3)) {
        |    if (var1[6]) {
        |      if (!input) {
        |        while (var16) {
        |          var2 = var2;
        |          output var5.qasYOcTZAu;
        |        }
        |      } else {
        |        while (![7,1,4,7,-1,5,3,3][4]) {}
        |        while ((!2 * [4,7,4,4,7,7][5])) {
        |          output var17;
        |          var7 = var7;
        |          output var2.oaGrBnuZij;
        |          output var3;
        |        }
        |        while ((var4 < var4)) {
        |          output (var14[4] * input);
        |          var4 = (var4 + 1);
        |        }
        |        while (!var15) {
        |          var1 = var1;
        |          output (input + var21[3]);
        |          var18 = &var3;
        |        }
        |      }
        |      while ((var16 < var0)) {
        |        var16 = (var16 + 1);
        |      }
        |      while ((var4 < var15)) {
        |        while ((var4 < var15)) {
        |          var12 = var12;
        |          var0 = !6;
        |          output var14[2];
        |          var4 = (var4 + 1);
        |        }
        |        while ((var10 < var16)) {
        |          output input;
        |          var10 = (var10 + 1);
        |        }
        |        if (var14[2]) {
        |          var8 = var18;
        |          output var14[2];
        |        } else {
        |          var11 = var11;
        |          var14 = var14;
        |        }
        |        var4 = (var4 + 1);
        |      }
        |    } else {
        |      var21[1] = input;
        |      var14[0] = (var2.oaGrBnuZij * var12.eObqkYDAeF);
        |      while (var3) {}
        |      while ((var3 < var9)) {
        |        var6[0] = var21;
        |        while ((var4 < var16)) {
        |          var4 = (var4 + 1);
        |        }
        |        while ((var9 < var0)) {
        |          var9 = (var9 + 1);
        |        }
        |        var3 = (var3 + 1);
        |      }
        |    }
        |    while ((var10 < var10)) {
        |      var10 = (var10 + 1);
        |    }
        |    var17 = (var17 + 1);
        |  }
        |  return var14[2];
        |}
        |""".stripMargin;
    val future = Future {
      val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
      val ctx = new Context()
      val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), ctx, new DFSSearchStrategy());
      executor.run()
    }
    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }
  }

  test("random generated test finishes with no error 2") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26,var27;
        |  var0 = 0;
        |  var1 = {wJfZvPalWH:4,VSvrDTlHzG:alloc 1,uMjAlfeSFB:0,HMADefIzLv:5};
        |  var2 = 6;
        |  var3 = alloc 1;
        |  var4 = {rxHUIoSnvB:alloc alloc 7,juYyRIAGXE:alloc alloc 4};
        |  var5 = alloc alloc 2;
        |  var6 = [5,4,4,4,0];
        |  var7 = 7;
        |  var8 = 1;
        |  var9 = 6;
        |  var10 = 6;
        |  var11 = 1;
        |  var12 = alloc 4;
        |  var13 = 2;
        |  var14 = 7;
        |  var15 = 8;
        |  var16 = 5;
        |  var17 = 6;
        |  var18 = 8;
        |  var19 = alloc alloc alloc 1;
        |  var20 = alloc [6,8,1,3,3,7,5,1,7];
        |  var21 = 1;
        |  var22 = alloc 5;
        |  var23 = 7;
        |  var24 = {qupIADhjdK:-1};
        |  var25 = -1;
        |  var26 = 0;
        |  var27 = [2,3,1,5,0];
        |  var2 = (input - input);
        |  output (var7 * var24.qupIADhjdK);
        |  while ((var18 < var21)) {
        |    var18 = (var18 + 1);
        |  }
        |  if ((input - var21)) {
        |    while ((var11 < var11)) {
        |      var9 = var1.HMADefIzLv;
        |      if (input) {
        |        while (input) {}
        |        if ((!5 + var24.qupIADhjdK)) {} else {
        |          var9 = input;
        |        }
        |        var27[1] = var8;
        |      } else {
        |        while ((var7 < var16)) {
        |          output input;
        |          var7 = (var7 + 1);
        |        }
        |      }
        |      while (var27[4]) {
        |        while (var27[2]) {
        |          output input;
        |        }
        |        output var25;
        |        var27[3] = var6[3];
        |        var5 = &var12;
        |      }
        |      if (var6[2]) {
        |        var1 = var1;
        |      } else {
        |        if (input) {
        |          output input;
        |          var7 = input;
        |          var20 = var20;
        |        } else {}
        |        var6[2] = var24.qupIADhjdK;
        |        output ([3,3,3,2,5,6,7][3] - (6 + 8));
        |        if (input) {
        |          output var11;
        |        } else {}
        |      }
        |      var11 = (var11 + 1);
        |    }
        |  } else {
        |    if (!!![3,0,0,3,8][0]) {
        |      var22 = &var14;
        |    } else {
        |      while (var6[1]) {}
        |      while (input) {
        |        var6[3] = var27[4];
        |      }
        |    }
        |    var6[0] = !!var24.qupIADhjdK;
        |    if (var6[0]) {
        |      var27[3] = var1.HMADefIzLv;
        |      var1 = var1;
        |    } else {
        |      if (!((2 + 4) * (6 * 0))) {} else {
        |        output var6[4];
        |        while (var27[3]) {
        |          var26 = [8,-1,4,2,-1,5,2,2][2];
        |          var9 = var9;
        |          output input;
        |        }
        |        if (var8) {
        |          output input;
        |          var27 = var27;
        |          output var17;
        |          var7 = [1,4,3,1,-1,7,6,1,2][8];
        |        } else {
        |          output input;
        |          var1 = var1;
        |          var12 = var12;
        |          var17 = var9;
        |        }
        |        while (var6[2]) {
        |          var17 = var8;
        |          var3 = &var2;
        |        }
        |      }
        |      while (var1.wJfZvPalWH) {
        |        if ((input + var21)) {
        |          var24 = var24;
        |        } else {
        |          output (var17 - var10);
        |          output input;
        |          var25 = input;
        |        }
        |        while ((var17 < var21)) {
        |          output input;
        |          var26 = input;
        |          var17 = (var17 + 1);
        |        }
        |      }
        |      var6[1] = var15;
        |    }
        |    var6[0] = (var27[2] - !var1.HMADefIzLv);
        |  }
        |  if ((input * input)) {
        |    var6[4] = input;
        |    while (!var6[0]) {
        |      var27[1] = !var27[1];
        |      var6[1] = input;
        |      var6[3] = (var26 - var1.HMADefIzLv);
        |      output input;
        |    }
        |    if (var1.HMADefIzLv) {} else {
        |      var24 = var24;
        |    }
        |  } else {
        |    while ((var10 < var15)) {
        |      var10 = (var10 + 1);
        |    }
        |    while (var27[3]) {
        |      if (var24.qupIADhjdK) {
        |        var10 = input;
        |        while ((var9 < var25)) {
        |          var9 = (var9 + 1);
        |        }
        |        output (var21 + var2);
        |      } else {
        |        var6[4] = var18;
        |        output var24.qupIADhjdK;
        |        while ((var11 < var26)) {
        |          output var1.wJfZvPalWH;
        |          var11 = (var11 + 1);
        |        }
        |        var8 = var1.HMADefIzLv;
        |      }
        |      var6[1] = input;
        |    }
        |    var25 = !!var25;
        |    var21 = input;
        |  }
        |  output input;
        |  return input;
        |}
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
    val ctx = new Context()
    val solver = new ConstraintSolver(ctx)
    val executor = new SymbolicExecutor(cfg, subsumption = Some(new PathSubsumption(solver)))
    executor.run()

  }



  test("nasty subsumption test") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16;
        |  var0 = -1;
        |  var1 = 4;
        |  var2 = {FqPeEQgtgT:alloc 3,GLTRGsqwSX:2};
        |  var3 = {AAYJcuYKQA:0,galokTcaUQ:alloc 1,sAOjYLVAFl:[5,8,5,4,8,4],ABkJFATzSQ:alloc 5};
        |  var4 = alloc 0;
        |  var5 = {tnXdyJXFCF:alloc 6,hvvsxfLVRH:2,jMxuOJMOdi:alloc 8,OIXCKjGxxH:-1,yiQlFLMOfD:alloc 0};
        |  var6 = 7;
        |  var7 = {jlpYTwaRRg:alloc alloc 6,PfwDCHTMZC:alloc -1,yTAaoMtoXb:[alloc 8,alloc 6,alloc 1,alloc -1,alloc 7,alloc 8]};
        |  var8 = 6;
        |  var9 = alloc 5;
        |  var10 = 5;
        |  var11 = alloc alloc 4;
        |  var12 = {CkqYpQUObT:alloc 1,rASeqbBkHU:alloc 6};
        |  var13 = alloc 2;
        |  var14 = -1;
        |  var15 = {VrJQZAFbxo:3};
        |  var16 = [0,4,5,4,7,6];
        |  while (input) {
        |    while (input) {
        |        while ((input * 3)) {
        |          while (var5.hvvsxfLVRH) {}
        |        }
        |        while (2) {
        |          while ((7 + -1)) {
        |            while (3) {
        |              var16 = [3,4,0,-1,4,8];
        |              var8 = 5;
        |            }
        |          }
        |        }
        |    }
        |  }
        |  return input;
        |}
        |""".stripMargin

    val future = Future {
      val program = parseUnsafe(code)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)

      val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
      val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
      for (node <- analysesResult) {
        val nodeCosts = new mutable.HashMap[String, Double]
        for (cost <- node._2) {
          nodeCosts.put(cost._1.name, cost._2)
        }
        variableCosts.put(node._1, nodeCosts)
      }
      val stateHistory = new ExecutionTree()
      val ctx = new Context()
      val executor = new SymbolicExecutor(cfg, ctx = ctx, subsumption = Some(new PathSubsumption(new ConstraintSolver(ctx))), searchStrategy = new RandomPathSelectionStrategy(stateHistory), executionTree = Some(stateHistory))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }

  }


  test("nasty subsumption test2") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20;
        |  var0 = 4;
        |  var1 = 8;
        |  var2 = alloc -1;
        |  var3 = alloc 8;
        |  var4 = alloc 7;
        |  var5 = alloc 1;
        |  var6 = [2,1,4,8,0,-1,8,5];
        |  var7 = alloc 2;
        |  var8 = 3;
        |  var9 = 2;
        |  var10 = 3;
        |  var11 = {cOYKfRcUOw:-1};
        |  var12 = 5;
        |  var13 = {VgQkoIYAXO:[0,3,6,0,7,0,7,1,-1],LuldBqYGXY:alloc -1,bhMXNkfqik:1};
        |  var14 = [alloc 4,alloc 8,alloc 6,alloc -1,alloc 2,alloc -1,alloc 4];
        |  var15 = 6;
        |  var16 = -1;
        |  var17 = 7;
        |  var18 = {smSaoMpFVX:0,qsylAAPlEZ:6};
        |  var19 = alloc 0;
        |  var20 = [8,3,-1,0,5];
        |  if (!!var17) {
        |    var14[0] = alloc input;
        |    var14[4] = &var8;
        |  } else {
        |    if (input) {
        |      var14[4] = var4;
        |    } else {
        |      var20[4] = !var0;
        |      while ((var6[3] * var16)) {
        |        output var18.qsylAAPlEZ;
        |        var20[0] = input;
        |      }
        |      var20[0] = var6[1];
        |    }
        |  }
        |  while (var11.cOYKfRcUOw) {
        |    while ((input - input)) {
        |      while (var13.bhMXNkfqik) {
        |        while (var18.qsylAAPlEZ) {
        |          while ([8,1,7,8,8,6][5]) {
        |            var14[4] = alloc -1;
        |            while (2) {}
        |          }
        |        }
        |      }
        |    }
        |  }
        |  return var6[0];
        |}
        |""".stripMargin

    val future = Future {
      val program = parseUnsafe(code)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)

      val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
      val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
      for (node <- analysesResult) {
        val nodeCosts = new mutable.HashMap[String, Double]
        for (cost <- node._2) {
          nodeCosts.put(cost._1.name, cost._2)
        }
        variableCosts.put(node._1, nodeCosts)
      }
      val stateHistory = new ExecutionTree()
      val ctx = new Context()
      val executor = new SymbolicExecutor(cfg, ctx = ctx, subsumption = Some(new PathSubsumption(new ConstraintSolver(ctx))), searchStrategy = new RandomPathSelectionStrategy(stateHistory), executionTree = Some(stateHistory))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }


  }


  test("nasty subsumption test3") {
    val code =
      """
        |main() {
        |  var var5,var13;
        |  var5 = 3;
        |  var13 = 0;
        |  while ((var13 < var5)) {
        |    if (input) {}
        |    var13 = (var13 + 1);
        |  }
        |  return input;
        |}
        |""".stripMargin
    val future = Future {
      val program = parseUnsafe(code)
      println(program)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)

      val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
      val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
      for (node <- analysesResult) {
        val nodeCosts = new mutable.HashMap[String, Double]
        for (cost <- node._2) {
          nodeCosts.put(cost._1.name, cost._2)
        }
        variableCosts.put(node._1, nodeCosts)
      }
      val executor = new SymbolicExecutor(cfg, searchStrategy = new AggressiveStateMerging(new DFSSearchStrategy))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }
  }


  test("nasty subsumption test4") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25;
        |  var0 = {FRoElVrbZi:5,ocQujqfFOn:0};
        |  var1 = 3;
        |  var2 = 1;
        |  var3 = alloc 7;
        |  var4 = 8;
        |  var5 = [5,1,8,3,-1,1,2];
        |  var6 = alloc 6;
        |  var7 = {fGtnZNVzCy:alloc 7,KDhnfjDMGu:[5,8,7,7,5,3],yeyfUaXpth:[alloc -1,alloc 4,alloc 0,alloc 8,alloc 6,alloc 5],VStXsHYwRf:alloc 7};
        |  var8 = alloc [4,0,6,0,1,8,6];
        |  var9 = 7;
        |  var10 = [[8,6,4,7,1,3],[3,0,8,-1,1,-1,2],[0,6,-1,1,4,4,0],[1,7,1,5,2,4,6,3,-1],[4,5,5,7,8,6,6,5],[6,8,6,2,5,4,6,7],[4,4,2,5,0,3,0,6],[3,1,6,-1,4,1,0]];
        |  var11 = 8;
        |  var12 = 8;
        |  var13 = [0,7,2,-1,3,0,-1,8,8];
        |  var14 = {ujiVTdClqO:alloc alloc 7,PxbNHgBvjg:4,nhlMAoQSLZ:alloc 4};
        |  var15 = 6;
        |  var16 = -1;
        |  var17 = 5;
        |  var18 = 0;
        |  var19 = alloc alloc 8;
        |  var20 = 5;
        |  var21 = 8;
        |  var22 = alloc 6;
        |  var23 = 3;
        |  var24 = {hmVXQVqHDP:alloc 4,zXNQZHlVbk:alloc alloc alloc 8,idhIWYgpKs:alloc 4,kbOeCdAZmz:2};
        |  var25 = [2,6,5,7,4];
        |  if ((var25[1] + !(input * var15))) {
        |    var22 = alloc (input + var15);
        |    while (input) {
        |      if (var17) {
        |        while (var2) {
        |          output var15;
        |          output !var21;
        |        }
        |        output input;
        |      } else {}
        |    }
        |    output input;
        |    while (var18) {}
        |  } else {
        |    output !var2;
        |  }
        |  return var15;
        |}
        |""".stripMargin


    val future = Future {
      val program = parseUnsafe(code)
      println(program)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)

      val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
      val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
      for (node <- analysesResult) {
        val nodeCosts = new mutable.HashMap[String, Double]
        for (cost <- node._2) {
          nodeCosts.put(cost._1.name, cost._2)
        }
        variableCosts.put(node._1, nodeCosts)
      }
      val executor = new SymbolicExecutor(cfg, searchStrategy = new AggressiveStateMerging(new DFSSearchStrategy))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }
  }



}

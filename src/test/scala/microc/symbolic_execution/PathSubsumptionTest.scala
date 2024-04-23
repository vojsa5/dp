package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.ast.{AndAnd, BinaryOp, CodeLoc, Divide, Expr, GreaterEqual, GreaterThan, Identifier, LowerEqual, LowerThan, Minus, Null, Number, Plus, Times, VarStmt, WhileStmt}
import microc.cfg.{CfgNode, CfgStmtNode, IntraproceduralCfgFactory}
import microc.symbolic_execution.Value.SymbolicVal
import microc.symbolic_execution.optimizations.subsumption.PathSubsumption
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx);
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
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
    val ps = new PathSubsumption(new ConstraintSolver(ctx), ctx)

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
    val ps = new PathSubsumption(new ConstraintSolver(ctx), ctx)

    state.programLocation = stmt

    assert(
      ps.removeNonInductiveLabels(
        state,
        BinaryOp(
          AndAnd,
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
    val res = executor.run()
//    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
    val res = executor.run()
//    assert(executor.statistics.stoppedWithSubsumption == 4)
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
    val initialProgramSize = cfg.nodes.size
    val res = executor.run()
//    assert(executor.statistics.stoppedWithSubsumption == 3)
    assert(executor.statistics.numPaths == 4)
    assert(cfg.nodes.find(node => node.id == 15.0).get.succ.head.id == 12.0)
    assert(cfg.nodes.find(node => node.id == 16.0).get.succ.head.id == 9.0)
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
        |   if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val subsumption = new PathSubsumption(new ConstraintSolver(ctx), ctx)
    val executor = new SymbolicExecutor(cfg, Some(subsumption), ctx, new DFSSearchStrategy());
    executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 1)
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
        |   if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val subsumption = new PathSubsumption(new ConstraintSolver(ctx), ctx)
    val executor = new SymbolicExecutor(cfg, Some(subsumption), ctx, new DFSSearchStrategy());
    executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 1)
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
    executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 3)
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
    executor.run()
//    assert(executor.statistics.stoppedWithSubsumption == 8)
    assert(executor.statistics.numPaths == 10)
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
    val res = executor.run()
    assert(executor.statistics.stoppedWithSubsumption == 2)
    assert(executor.statistics.numPaths == 3)
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
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
    val res = executor.run()
  }

}

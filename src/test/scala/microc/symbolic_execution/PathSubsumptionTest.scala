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
//    for (_ <- 0 to 10) {
//      assert(pathSubsumption.checkSubsumption(node, generateRandomExpr(), new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))))
//    }
//    for (_ <- 0 to 10) {
//      pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
//      pathSubsumption.addAnnotation(node, constraintSolver.createConstraintWithState(generateRandomExpr(), symbolicState))
//      assert(pathSubsumption.checkSubsumption(node, Number(1, CodeLoc(0, 0)), new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))))
//    }
//    for (_ <- 0 to 10) {
//      pathSubsumption = new PathSubsumption(new ConstraintSolver(context), context)
//      pathSubsumption.addAnnotation(node, constraintSolver.createConstraintWithState(Number(1, CodeLoc(0, 0)), symbolicState))
//      assert(!pathSubsumption.checkSubsumption(node, generateRandomExpr(), new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))))
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
    assert(executor.statistics.stoppedWithSubsumption == 2)
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
    assert(executor.statistics.stoppedWithSubsumption == 4)
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
    assert(executor.statistics.stoppedWithSubsumption == 3)
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
    assert(executor.statistics.stoppedWithSubsumption == 8)
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

}

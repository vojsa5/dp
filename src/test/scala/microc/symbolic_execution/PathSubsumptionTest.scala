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
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    symbolicState.addedVar("x", SymbolicVal(CodeLoc(0, 0)))
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

  test("random generated test finishes with no error") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18;
        |  var0 = {FrbkUriwKD:2};
        |  var1 = 7;
        |  var2 = 4;
        |  var3 = alloc 4;
        |  var4 = {ZpXlPyHmHH:5,dDqnONreXn:8,JLaheWDogc:alloc 3,vmnUidYZzD:[3,-1,6,7,8],bCwcGzSyvN:alloc 8};
        |  var5 = 8;
        |  var6 = [2,1,8,1,3];
        |  var7 = 8;
        |  var8 = 6;
        |  var9 = 1;
        |  var10 = alloc 3;
        |  var11 = alloc 5;
        |  var12 = {JjAdAZdRmn:5,qNOvLPeZSX:alloc alloc 6,GojQXAWRfc:alloc 8};
        |  var13 = alloc 7;
        |  var14 = 8;
        |  var15 = 6;
        |  var16 = 0;
        |  var17 = alloc 5;
        |  var18 = [8,4,8,4,8];
        |  if (!var18[3]) {
        |    output var18[2];
        |    var6[1] = var6[3];
        |    while (input) {
        |      while (var4.dDqnONreXn) {
        |        var1 = var12.JjAdAZdRmn;
        |        var3 = var13;
        |        output var6[0];
        |        output input;
        |      }
        |      if (input) {
        |        output var18[4];
        |        var17 = &var5;
        |        var11 = &var2;
        |        var17 = &var5;
        |      } else {
        |        output var12.JjAdAZdRmn;
        |        output input;
        |        output var1;
        |        var2 = [4,1,2,5,4,6][4];
        |        var4 = var4;
        |      }
        |      while (!!2) {
        |        var14 = input;
        |        output var7;
        |        output var8;
        |        output !var0.FrbkUriwKD;
        |      }
        |      var1 = var8;
        |    }
        |    var2 = var12.JjAdAZdRmn;
        |    if (var18[0]) {
        |      if (var2) {
        |        output var18[0];
        |        output var2;
        |        var9 = var4.ZpXlPyHmHH;
        |        var6 = var18;
        |      } else {
        |        output var12.JjAdAZdRmn;
        |        var1 = [7,8,0,-1,3,-1,1][4];
        |        var1 = !7;
        |        var12 = var12;
        |      }
        |      if (var18[1]) {
        |        output var18[2];
        |        output (var5 * var6[3]);
        |        var1 = [7,7,6,7,2,7,-1,1,3][3];
        |        output !input;
        |      } else {
        |        output input;
        |        var7 = input;
        |        var10 = alloc 1;
        |      }
        |      var4 = var4;
        |    } else {
        |      if ((var1 - input)) {
        |        output input;
        |        var6 = var6;
        |        var8 = var9;
        |        var12 = var12;
        |      } else {
        |        output input;
        |        var12 = var12;
        |        output var0.FrbkUriwKD;
        |      }
        |      while (var18[4]) {
        |        var15 = var7;
        |        var4 = var4;
        |        output !input;
        |      }
        |      while (input) {
        |        output var12.JjAdAZdRmn;
        |        var6 = var6;
        |        var2 = [0,2,0,-1,0,4,6,6][0];
        |        output var4.ZpXlPyHmHH;
        |      }
        |      var5 = var0.FrbkUriwKD;
        |    }
        |  } else {
        |    output var9;
        |    if (input) {
        |      if (var18[3]) {
        |        output !!input;
        |        output var6[3];
        |        output var0.FrbkUriwKD;
        |        output var1;
        |        output var4.dDqnONreXn;
        |      } else {
        |        output !var18[2];
        |        var9 = [0,5,7,6,8,6,1][3];
        |        output var14;
        |        var2 = var12.JjAdAZdRmn;
        |      }
        |      while (!var5) {
        |        output var18[4];
        |        output (input * (input + var18[3]));
        |        output !var6[0];
        |        var14 = var7;
        |        var4 = var4;
        |      }
        |      while ((var16 * input)) {
        |        output (var5 + (!input - input));
        |        output var0.FrbkUriwKD;
        |        output var6[4];
        |        var18 = var6;
        |        output var0.FrbkUriwKD;
        |      }
        |      var6[1] = input;
        |    } else {
        |      var15 = var12.JjAdAZdRmn;
        |      var18[2] = var4.ZpXlPyHmHH;
        |      var11 = alloc (7 - 5);
        |    }
        |    var6[2] = input;
        |  }
        |  output var12.JjAdAZdRmn;
        |  var18[3] = var6[4];
        |  while (input) {
        |    if (!input) {
        |      while ((input * [-1,8,2,-1,-1,-1][0])) {
        |        var7 = [5,4,2,3,6][2];
        |        output input;
        |        output var18[4];
        |        output input;
        |        output input;
        |      }
        |      output (input * [3,-1,3,1,0,-1][2]);
        |      if (var12.JjAdAZdRmn) {
        |        output (var1 * !input);
        |        var18 = var6;
        |        var18 = var18;
        |        output var12.JjAdAZdRmn;
        |      } else {
        |        var5 = input;
        |        output input;
        |        output var1;
        |        var6 = var6;
        |        var13 = alloc 4;
        |      }
        |    } else {
        |      output !input;
        |      output input;
        |      if (input) {
        |        output var8;
        |        output input;
        |        var3 = &var8;
        |      } else {
        |        output (((([3,8,1,2,7,7][2] * !3) * (var12.JjAdAZdRmn + !6)) * !var6[2]) * !input);
        |        var3 = &var2;
        |        output var6[2];
        |        output var2;
        |      }
        |      if (input) {
        |        var18 = var6;
        |        var1 = !1;
        |        var5 = var4.dDqnONreXn;
        |      } else {
        |        output (!var8 + input);
        |        var4 = var4;
        |        var7 = input;
        |      }
        |      var6[1] = !var2;
        |    }
        |    if ((input + var18[3])) {
        |      output (input + (6 * 5));
        |      while (var8) {
        |        output (input - var18[3]);
        |        var9 = input;
        |        output !var18[2];
        |        output !var6[1];
        |      }
        |      var16 = input;
        |      var5 = var0.FrbkUriwKD;
        |      var5 = var0.FrbkUriwKD;
        |    } else {
        |      if (input) {
        |        var11 = &var8;
        |        var4 = var4;
        |        output (var12.JjAdAZdRmn * (input * !var4.dDqnONreXn));
        |      } else {
        |        var4 = var4;
        |        output !var18[4];
        |        output var12.JjAdAZdRmn;
        |        var13 = &var1;
        |        var4 = var4;
        |      }
        |      output ([-1,6,5,2,4,7][4] + var16);
        |      output (var14 - input);
        |      var6[4] = var4.dDqnONreXn;
        |      while (input) {
        |        var14 = (3 - 5);
        |        var10 = alloc 7;
        |        output (input - var12.JjAdAZdRmn);
        |        output (input - input);
        |        var18 = var18;
        |      }
        |    }
        |    while (!!input) {
        |      if ((!8 + [4,-1,8,7,-1,-1][0])) {
        |        var11 = &var7;
        |        output var16;
        |        output input;
        |        output var18[2];
        |      } else {
        |        output (input * var4.ZpXlPyHmHH);
        |        output input;
        |        var12 = var12;
        |        output input;
        |        output var18[1];
        |      }
        |      var5 = var2;
        |      if (input) {
        |        output var12.JjAdAZdRmn;
        |        var15 = !5;
        |        var16 = [6,5,1,1,7,-1,0][0];
        |        var10 = alloc 1;
        |        output var4.dDqnONreXn;
        |      } else {
        |        output !!input;
        |        var8 = var4.ZpXlPyHmHH;
        |        output var14;
        |      }
        |    }
        |  }
        |  output input;
        |  if (!var0.FrbkUriwKD) {
        |    output !input;
        |    var8 = var2;
        |    output input;
        |    if (input) {
        |      while (var6[3]) {
        |        output !(var2 - var8);
        |        output var9;
        |        output var16;
        |        output !(var4.dDqnONreXn * var16);
        |        var18 = var18;
        |      }
        |      var17 = &var5;
        |      while (var0.FrbkUriwKD) {
        |        output (var0.FrbkUriwKD * (input + !!input));
        |        var10 = alloc 5;
        |        output input;
        |        var16 = (5 - 7);
        |        var12 = var12;
        |      }
        |      while (var12.JjAdAZdRmn) {
        |        var11 = var10;
        |        output input;
        |        var3 = &var5;
        |        var13 = alloc 5;
        |      }
        |      var6[0] = var12.JjAdAZdRmn;
        |    } else {
        |      while (var18[1]) {
        |        var4 = var4;
        |        output input;
        |        output var6[0];
        |        var9 = [4,8,5,7,5,4][4];
        |        var7 = var14;
        |      }
        |      while (!input) {
        |        output var6[2];
        |        output var18[1];
        |        output var5;
        |        var9 = input;
        |      }
        |      output var6[4];
        |      output input;
        |    }
        |  } else {
        |    var18[2] = var18[4];
        |    output var4.dDqnONreXn;
        |    var10 = var17;
        |    while (var4.dDqnONreXn) {
        |      if (var1) {
        |        output !((var4.ZpXlPyHmHH + var4.ZpXlPyHmHH) + var6[1]);
        |        var14 = var9;
        |        output input;
        |        output (var4.ZpXlPyHmHH + var18[3]);
        |        var4 = var4;
        |      } else {
        |        output !input;
        |        var2 = !5;
        |        var18 = var6;
        |        output var4.ZpXlPyHmHH;
        |      }
        |      output var12.JjAdAZdRmn;
        |      if ((input * !6)) {
        |        var16 = var4.dDqnONreXn;
        |        output input;
        |        output var5;
        |      } else {
        |        var12 = var12;
        |        var18 = var6;
        |        var16 = input;
        |        var12 = var12;
        |      }
        |      var6[4] = var12.JjAdAZdRmn;
        |      while (var18[3]) {
        |        output var8;
        |        var1 = var14;
        |        output input;
        |        var6 = var6;
        |        output var14;
        |      }
        |    }
        |  }
        |  output input;
        |  var18[2] = (input - input);
        |  output input;
        |  return var12.JjAdAZdRmn;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, new DFSSearchStrategy());
    val res = executor.run()
  }

}

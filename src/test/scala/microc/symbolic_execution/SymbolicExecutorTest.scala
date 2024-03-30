package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.{CodeLoc, Decl, NestedBlockStmt, Number, WhileStmt}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

import scala.collection.mutable
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.util.control.NonFatal

class SymbolicExecutorTest extends FunSuite with MicrocSupport with Examples {

  test("factorial") {
    val code =
      """
        |
        |fac(n) {
        |    var f;
        |
        |    if (n == 0) {
        |      f = 1;
        |    } else {
        |      f = n * fac(n - 1);
        |    }
        |
        |    return f;
        |}
        |
        |
        |main() {
        |  var a,b;
        |  b = input;
        |  if (b < 0) {
        |     b = 0;
        |  }
        |  a = fac(b);
        |  output(a);
        |  return 1 / (a - 5);
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    val future = Future {
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds)
    }
    catch {
      case _: TimeoutException =>
      case e =>
        throw e
    }
  }

  test("factorial 2") {
    val code =
      """
        |
        |fac(n) {
        |    var f;
        |
        |    if (n == 0) {
        |      f = 1;
        |    } else {
        |      f = n * fac(n - 1);
        |    }
        |
        |    return f;
        |}
        |
        |
        |main() {
        |  var a,b;
        |  b = input;
        |  if (b <= 0) {
        |     b = 1;
        |  }
        |  a = fac(b);
        |  output(a);
        |  return 1 / (a - 6);
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
        executor.run()
        fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("factorial 3") {
    val code =
      """
        |
        |fac(n) {
        |    var f;
        |
        |    if (n == 0) {
        |      f = 1;
        |    } else {
        |      f = n * fac(n - 1);
        |    }
        |
        |    return f;
        |}
        |
        |
        |main() {
        |  var a,b;
        |  b = input;
        |  if (b <= 0) {
        |     b = 1;
        |  }
        |  return 1 / (fac(b) - 6);
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }



  test("possible error") {
    val code =
      """
        |main() {
        |  var x;
        |  x = input;
        |  return 1/x;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }


  test("type 3 loop unsummarizable") {
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
    val executor = new LoopSummary(cfg);
    val future = Future {
      executor.run()
      fail("should be killed by timeout")
    }

    try {
      Await.ready(future, 5.seconds)
    }
    catch {
      case _: TimeoutException =>
      case e =>
        fail(e.toString)
    }
  }



  test("type 3 loop unsummarizable arrays") {
    val code =
      """
        |main() {
        |  var i, j, k, n;
        |  i = [input];
        |  k = [input];
        |  n = [input];
        |  while (i[0] < n[0]) {
        |     j = input;
        |     if (j <= 1) {
        |        j = 1;
        |     }
        |     i[0] = i[0] + j;
        |     k[0] = k[0] + 1;
        |  }
        |  return k[0];
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new LoopSummary(cfg);
    val future = Future {
      executor.run()
      fail("should be killed by timeout")
    }

    try {
      Await.ready(future, 5.seconds)
    }
    catch {
      case _: TimeoutException =>
      case e =>
        fail(e.toString)
    }
  }

//  test("infinite paths") {
//    val code =
//      """
//        |main() {
//        |  var y;
//        |  y = input;
//        |  while (y > 0) {
//        |   y = y - 1;
//        |  }
//        |  return 0;
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new SymbolicExecutor(cfg);
//    try {
//      executor.run()
//      fail("Expected a StackOverflowError but it did not occur.")
//    }
//    catch {
//      case _: StackOverflowError =>
//      case other: Throwable => fail("Expected a StackOverflowError, but caught different exception: " + other)
//    }
//
//    null
//  }
//
//
//  test("infinite paths 2") {
//    val code =
//      """
//        |main() {
//        |  var y;
//        |  y = input;
//        |  y = y + 1;
//        |  while (y > 0) {
//        |   y = y - 1;
//        |  }
//        |  return 0;
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new SymbolicExecutor(cfg);
//    try {
//      executor.run()
//      fail("Expected a StackOverflowError but it did not occur.")
//    }
//    catch {
//      case _: StackOverflowError =>
//      case other: Throwable => fail("Expected a StackOverflowError, but caught different exception: " + other)
//    }
//
//    null
//  }


  test("survey test") {
    val code =
      """
        |foobar(a, b) {
        |  var x, y;
        |  x = 1;
        |  y = 0;
        |  if (a != 0) {
        |   y = 3 + x;
        |   if (b == 0) {
        |     x = 2 * (a + b);
        |   }
        |  }
        |  return 1 / (x - y);
        |}
        |
        |main() {
        |  var y, x;
        |  y = input;
        |  x = input;
        |  x = foobar(x, y);
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }

  test("my5") {
    val code =
      """
        |main() {
        |  var y, x;
        |  y = 4;
        |  x = 0;
        |  while (y > 0) {
        |   y = y - 1;
        |   x = x + 1;
        |  }
        |  output x;
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

  test("error as nullptr dereference") {
    val code =
      """
        |main() {
        |  var y, x, a, b;
        |  a = input;
        |  y = input;
        |  if (a) {
        |   x = &y;
        |  }
        |  else {
        |   x = null;
        |  }
        |  return *x;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }


  test("error as use of uninitialized value") {
    val code =
      """
        |main() {
        |  var y, x, a, b;
        |  a = input;
        |  y = input;
        |  if (a) {
        |   x = &y;
        |  }
        |  else {
        |   x = null;
        |  }
        |  return *x;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }


  test("error as use of uninitialized value") {
    val code =
      """
        |main() {
        |  var y, a;
        |  a = [1, 2, 3];
        |  y = input;
        |  return a[y];
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }


  test("dfs strategy") {
    val code =
      """
        |main() {
        |  var y, x;
        |  y = 4;
        |  x = 0;
        |  while (y > 0) {
        |   y = y - 1;
        |   x = x + 1;
        |  }
        |  output x;
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg, searchStrategy = new DFSSearchStrategy());
    executor.run()
    null
  }


  test("random strategy") {
    val code =
      """
        |main() {
        |  var y, x;
        |  y = 4;
        |  x = 0;
        |  while (y > 0) {
        |   y = y - 1;
        |   x = x + 1;
        |  }
        |  output x;
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg, searchStrategy = new RandomSearchStrategy());
    executor.run()
    null
  }

  test("error does not happen") {
    val code =
      """
        |main() {
        |  var y,z;
        |  z = 0;
        |  y = 1;
        |  if (z == 0) {
        |   y = 2;
        |  }
        |  else {
        |   y = 3 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

  test("error in second path") {
    val code =
      """
        |main() {
        |  var y,z;
        |  z = input;
        |  y = 1;
        |  if (z == 0) {
        |   y = 2;
        |  }
        |  else {
        |   y = 3 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }


  test("nested unreachable error") {
    val code =
      """
        |main() {
        |  var y,z;
        |  z = input;
        |  y = 1;
        |  if (z == 0) {
        |   y = 2;
        |  }
        |  else {
        |   y = 3 / z;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

  test("my2") {
    val code =
      """
        |main() {
        |  var x,y,z,a,b;
        |  a = 1;
        |  b = 2;
        |  z = a+b;
        |  y = a*b;
        |  while (y > a+b) {
        |    a = a+1;
        |    x = a+b;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }


  test("simple in subsumption paper") {
    val code =
      """
        |main() {
        |  var x,y;
        |  x = 0;
        |  if (input) {
        |
        |  }
        |  else {
        |     y = input;
        |     if (y < 0) {
        |       y = 0;
        |     }
        |     x = x + y;
        |  }
        |  if (x < 0) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), searchStrategy = new DFSSearchStrategy)
    executor.run()
    null
  }

  test("loops in subsumption paper") {
    val code =
      """
        |main() {
        |  var x,y,i,n;
        |  x = input;
        |  n = input;
        |  y = x;
        |  i = 0;
        |  while (i < n) {
        |    x = x + 1;
        |    i = i + 1;
        |  }
        |  if (x < y) {
        |     x = 1 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), searchStrategy = new DFSSearchStrategy)
    executor.run()
    null
  }

//  test("bf") {
//    val code = bfCode
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new SymbolicExecutor(cfg)
//    executor.run()
//  }

//  test("bf coverage search") {
//    val code = bfCode
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val covered = Some(mutable.HashSet[CfgNode]())
//    val executor = new SymbolicExecutor(cfg, searchStrategy = new CoverageSearchStrategy(covered.get), covered = covered)
//    executor.run()
//  }
//
//  test("bf random path search") {
//    val code = bfCode
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val covered = Some(mutable.HashSet[CfgNode]())
//    val stateHistory = new StateHistory()
//    val executor = new SymbolicExecutor(cfg, stateHistory = Some(stateHistory), searchStrategy = new RandomPathSelectionStrategy(stateHistory), covered = covered)
//    executor.run()
//  }
//
//  test("bf klee search") {
//    val code = bfCode
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val covered = Some(mutable.HashSet[CfgNode]())
//    val stateHistory = new StateHistory()
//    val executor = new SymbolicExecutor(cfg, searchStrategy = new KleeSearchStrategy(stateHistory, covered.get), covered = covered)
//    executor.run()
//  }
//
//  test("bf with subsumption") {
//    val code = bfCode
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val ctx = new Context()
//    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)))
//    executor.run()
//  }
//
//  test("bf with merging") {
//    val code = bfCode
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new SymbolicExecutor(cfg, None, searchStrategy = new AgressiveStateMerging(new BFSSearchStrategy))
//    executor.run()
//  }
//
//  test("bf with smart merging") {
//    val code = bfCode
//    val program = parseUnsafe(code)
//    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
//    val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
//    val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
//    for (node <- analysesResult) {
//      val nodeCosts = new mutable.HashMap[String, Double]
//      for (cost <- node._2) {
//        nodeCosts.put(cost._1.name, cost._2)
//      }
//      variableCosts.put(node._1, nodeCosts)
//    }
//    val executor = new SymbolicExecutor(cfg, None, searchStrategy = new HeuristicBasedStateMerging(new BFSSearchStrategy, variableCosts, 3))
//    executor.run()
//  }
//
//  test("bf with smart merging 2") {
//    val code = bfCode
//    val program = parseUnsafe(code)
//    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
//    val tmp = new TMP()(new SemanticAnalysis().analyze(program))
//    tmp.tmp2(cfg)
//    val executor = new SymbolicExecutor(cfg, None, searchStrategy = new HeuristicBasedStateMerging(new BFSSearchStrategy, tmp.mapping, 3))
//    executor.run()
//  }
//
//  test("bf dynamic smart merging") {
//    val code = bfCode
//    val program = parseUnsafe(code)
//    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
//    val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
//    val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
//    for (node <- analysesResult) {
//      val nodeCosts = new mutable.HashMap[String, Double]
//      for (cost <- node._2) {
//        nodeCosts.put(cost._1.name, cost._2)
//      }
//      variableCosts.put(node._1, nodeCosts)
//    }
//    val limitCost = 3.0
//    val depth = 3
//    val stateHistory = new StateHistory()
//    val dynamicStateMerging = new DynamicStateMerging(
//      new HeuristicBasedStateMerging(new BFSSearchStrategy, variableCosts, limitCost),
//      stateHistory,
//      variableCosts,
//      limitCost,
//      depth
//    )
//    val executor = new SymbolicExecutor(cfg, None, searchStrategy = dynamicStateMerging)
//    executor.run()
//  }
//
//  test("bf with merging and subsumption") {
//    val code = bfCode
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val ctx = new Context()
//    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), searchStrategy = new AgressiveStateMerging(new BFSSearchStrategy))
//    executor.run()
//  }




  test("sequential unbounded loop finishes with summarization correctly") {
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

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new LoopSummary(cfg)
    executor.run()
  }


  test("simple sequential summarization is correct") {

    var code =
      """
        |main() {
        |  var i, m;
        |  i = 0;
        |  m = input;
        |  if (m <= 0) {
        |   m = 1;
        |  }
        |  while (i < m) {
        |   i = i + 1;
        |  }
        |  return 1 / (i - m - 1);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    executor.run()


    code =
      """
        |main() {
        |  var i, m;
        |  i = 0;
        |  m = input;
        |  if (m <= 0) {
        |   m = 1;
        |  }
        |  while (i < m) {
        |   i = i + 1;
        |  }
        |  return 1 / (i - m);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }


    code =
      """
        |main() {
        |  var i, m;
        |  i = 0;
        |  m = input;
        |  if (m <= 0) {
        |   m = 1;
        |  }
        |  while (i < m) {
        |   i = i + 1;
        |  }
        |  return 1 / (i - m + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    executor.run()
  }

  test("sequential unbounded periodic loop finishes with summarization correctly") {
    var code =
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

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }

    code =
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
        |  return 1 / (x - n);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("sequential unbounded periodic loop finishes with summarization correctly arrays") {
    var code =
      """
        |main() {
        |  var n, x, z;
        |  n = [input];
        |  x = [input];
        |  z = [input];
        |  while (x[0] < n[0]) {
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

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }

    code =
      """
        |main() {
        |  var n, x, z;
        |  n = [input];
        |  x = [input];
        |  z = [input];
        |  while (x < n) {
        |   if (z[0] > x[0]) {
        |     x[0] = x[0] + 1;
        |   }
        |   else {
        |     z[0] = z[0] + 1;
        |   }
        |  }
        |  return 1 / (x[0] - n[0]);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }



  test("sequential unbounded periodic loop finishes with summarization correctly arrays arrays") {
    var code =
      """
        |main() {
        |  var n, x, z;
        |  n = [[input]];
        |  x = [[input]];
        |  z = [[input]];
        |  while (x[0][0] < n[0][0]) {
        |   if (z[0][0] > x[0][0]) {
        |     x[0][0] = x[0][0] + 1;
        |   }
        |   else {
        |     z[0][0] = z[0][0] + 1;
        |   }
        |  }
        |  return 1 / (x[0][0] - z[0][0]);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }

    code =
      """
        |main() {
        |  var n, x, z;
        |  n = [[input]];
        |  x = [[input]];
        |  z = [[input]];
        |  while (x[0][0] < n[0][0]) {
        |   if (z[0][0] > x[0][0]) {
        |     x[0][0] = x[0][0] + 1;
        |   }
        |   else {
        |     z[0][0] = z[0][0] + 1;
        |   }
        |  }
        |  return 1 / (x[0][0] - n[0][0]);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("sequential unbounded periodic loop finishes with summarization correctly records") {
    var code =
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

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }

    code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = {field: input};
        |  z = {field: input};
        |  while (x.field < n) {
        |   if (z.field > x.field]) {
        |     x.field = x.field + 1;
        |   }
        |   else {
        |     z.field = z.field + 1;
        |   }
        |  }
        |  return 1 / (x.field - n.field);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("sequential unbounded periodic loop with adding a variables") {
    var code =
      """
        |main() {
        |  var n, x, z, a1, a2;
        |  n = input;
        |  x = input;
        |  z = input;
        |  a1 = input;
        |  a2 = input;
        |  if (a1 <= 0) {
        |     a1 = 1;
        |  }
        |  if (a2 <= 0) {
        |     a2 = 1;
        |  }
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + a1;
        |   }
        |   else {
        |     z = z + a2;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("unbounded periodic loop finishes with summarization correctly 2") {
    var code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  if (x >= n) {
        |   x = n - 1;
        |  }
        |  if (z >= n) {
        |   z = n - 1;
        |  }
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z - 1);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    executor.run()


    code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  if (x >= n) {
        |   x = n - 1;
        |  }
        |  if (z >= n) {
        |   z = n - 1;
        |  }
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

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }


    code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  if (x >= n) {
        |   x = n - 1;
        |  }
        |  if (z >= n) {
        |   z = n - 1;
        |  }
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    executor.run()
  }


  test("unrolled nested summarization") {
    var code =
      """
        |main() {
        |    var i, j, sum, res, n;
        |    sum = 0;
        |    j = 0;
        |    n = input;
        |    if (n <= 0) {
        |       n = 1;
        |    }
        |
        |    while (j < n) {
        |        sum = sum + 1;
        |        j = j + 1;
        |    }
        |
        |    if (sum == n) {
        |       res = 1;
        |    }
        |    else {
        |       res = 0;
        |    }
        |
        |    return 1 / res;
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    assert(executor.run() == 1)
  }


  test("unrolled nested summarization 2") {
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
        |       sum = sum + n;
        |       i = i + 1;
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

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    assert(executor.run() == 1)
  }


  test("basic nested summarization") {
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

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    assert(executor.run() == 1)
  }


  test("basic nested nested summarization") {
    var code =
      """
        |main() {
        |    var i, j, k, sum, res, n;
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
        |            k = 0;
        |            while (k < n) {
        |               sum = sum + 1;
        |               k = k + 1;
        |            }
        |            j = j + 1;
        |        }
        |        i = i + 1;
        |    }
        |
        |    if (sum == n * n * n) {
        |       res = 1;
        |    }
        |    else {
        |       res = 0;
        |    }
        |
        |    return 1 / res;
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    assert(executor.run() == 1)
  }


  test("nested periodic loop unrolled") {
    val code =
      """
        |main() {
        |  var n, x, z, res, i;
        |  n = input;
        |  x = input;
        |  z = input;
        |  res = 0;
        |  if (n <= 0) {
        |     n = 1;
        |  }
        |  if (x >= n) {
        |   x = n - 1;
        |  }
        |  if (z >= n) {
        |   z = n - 1;
        |  }
        |  i = 0;
        |  while (i < n) {
        |     x = n;
        |     z = n;
        |     i = i + 1;
        |     res = res + z;
        |  }
        |
        |  if (res == n * n) {
        |     res = 1;
        |  }
        |  else {
        |     res = 0;
        |  }
        |
        |  return 1 / res;
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    assert(executor.run() == 1)
  }


  test("nested periodic loop") {
    var code =
      """
        |main() {
        |  var n, x, z, res, i, realX, realZ;
        |  n = input;
        |  x = input;
        |  z = input;
        |  res = 0;
        |  if (n <= 0) {
        |     n = 1;
        |  }
        |  if (x >= n) {
        |     x = n - 1;
        |  }
        |  if (z >= n) {
        |     z = n - 1;
        |  }
        |  realX = x;
        |  realZ = z;
        |
        |  i = 0;
        |  while (i < n) {
        |     x = realX;
        |     z = realZ;
        |     while (x < n) {
        |        if (z > x) {
        |           x = x + 1;
        |        }
        |        else {
        |           z = z + 1;
        |        }
        |     }
        |     res = res + x;
        |     i = i + 1;
        |  }
        |
        |  if (res == n * n) {
        |     res = 1;
        |  }
        |  else {
        |     res = 0;
        |  }
        |
        |  return 1 / res;
        |}
        |
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    assert(executor.run() == 1)


//    code =
//      """
//        |main() {
//        |  var n, x, z, x2, z2, res, realX, realZ, realX2, realZ2;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  x2 = input;
//        |  z2 = input;
//        |  res = 0;
//        |  if (n <= 0) {
//        |     n = 1;
//        |  }
//        |  if (x >= n) {
//        |     x = n - 1;
//        |  }
//        |  if (z >= n) {
//        |     z = n - 1;
//        |  }
//        |  if (x2 >= n) {
//        |     x2 = n - 1;
//        |  }
//        |  if (z2 >= n) {
//        |     z2 = n - 1;
//        |  }
//        |  realX = x;
//        |  realZ = z;
//        |  realX2 = x2;
//        |  realZ2 = z2;
//        |
//        |  while (x2 < n) {
//        |     if (z2 > x2) {
//        |        x2 = x2 + n;
//        |     }
//        |     else {
//        |        z2 = z2 + n;
//        |     }
//        |  }
//        |
//        |  if (z2 <= n * n) {
//        |     res = 1;
//        |  }
//        |  else {
//        |     res = 0;
//        |  }
//        |
//        |  return 1 / res;
//        |}
//        |
//        |""".stripMargin;
//
//    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    executor = new LoopSummary(cfg)
//    assert(executor.run() == 1)
//
//
//    code =
//      """
//        |main() {
//        |  var n, x, z, x2, z2, res, realX, realZ, realX2, realZ2;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  x2 = input;
//        |  z2 = input;
//        |  res = 0;
//        |  if (n <= 0) {
//        |     n = 1;
//        |  }
//        |  if (x >= n) {
//        |     x = n - 1;
//        |  }
//        |  if (z >= n) {
//        |     z = n - 1;
//        |  }
//        |  if (x2 >= n + n) {
//        |     x2 = n + n - 1;
//        |  }
//        |  if (z2 >= n + n) {
//        |     z2 = n + n - 1;
//        |  }
//        |  realX = x;
//        |  realZ = z;
//        |  realX2 = x2;
//        |  realZ2 = z2;
//        |
//        |  while (x2 < n + n) {
//        |     x = realX;
//        |     z = realZ;
//        |     if (z2 > x2) {
//        |        while (x < n) {
//        |           if (z > x) {
//        |              x = x + 1;
//        |           }
//        |           else {
//        |              z = z + 1;
//        |           }
//        |        }
//        |        x2 = x2 + x;
//        |     }
//        |     else {
//        |        while (x < n) {
//        |           if (z > x) {
//        |              x = x + 1;
//        |           }
//        |           else {
//        |              z = z + 1;
//        |           }
//        |        }
//        |        z2 = z2 + x;
//        |     }
//        |  }
//        |
//        |  if (z2 >= n + n) {
//        |     res = 1;
//        |  }
//        |  else {
//        |     res = 0;
//        |  }
//        |
//        |  return 1 / res;
//        |}
//        |
//        |""".stripMargin;
//
//    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    executor = new LoopSummary(cfg)
//    //assert(executor.run() == 1)
//
//
//
//    code =
//      """
//        |main() {
//        |  var n, x, z, x2, z2, res, realX, realZ, realX2, realZ2;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  x2 = input;
//        |  z2 = input;
//        |  res = 0;
//        |  if (n <= 0) {
//        |     n = 1;
//        |  }
//        |  if (x >= n) {
//        |     x = n - 1;
//        |  }
//        |  if (z >= n) {
//        |     z = n - 1;
//        |  }
//        |  if (x2 >= n + n) {
//        |     x2 = n - 1;
//        |  }
//        |  if (z2 >= n + n) {
//        |     z2 = n - 1;
//        |  }
//        |  realX = x;
//        |  realZ = z;
//        |  realX2 = x2;
//        |  realZ2 = z2;
//        |
//        |  while (x2 < n + n) {
//        |     x = realX;
//        |     z = realZ;
//        |     if (z2 > x2) {
//        |        while (x < n) {
//        |           if (z > x) {
//        |              x = x + 1;
//        |           }
//        |           else {
//        |              z = z + 1;
//        |           }
//        |        }
//        |        x2 = x2 + x;
//        |     }
//        |     else {
//        |        while (x < n) {
//        |           if (z > x) {
//        |              x = x + 1;
//        |           }
//        |           else {
//        |              z = z + 1;
//        |           }
//        |        }
//        |        z2 = z2 + x;
//        |     }
//        |  }
//        |
//        |  if (x2 >= n + n) {
//        |     res = 1;
//        |  }
//        |  else {
//        |     res = 0;
//        |  }
//        |
//        |  return 1 / res;
//        |}
//        |
//        |""".stripMargin;
//
//    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    executor = new LoopSummary(cfg)
//    executor.run()
//    assert(executor.run() == 1)
  }



  test("factorial of number bigger then 2 is even") {
    var code =
      """
        |main() {
        |  var result, i, j, n, sum, result2;
        |  result = 1; // Factorial of 0 is 1 by definition
        |  n = input;
        |  if (n < 2) {
        |     n = 2;
        |  }
        |
        |  i = 1;
        |  while (i <= n) {
        |    sum = 0; // Reset sum for each multiplication
        |    j = 0;
        |    while (j < i) {
        |      sum = sum + result; // Add 'result' to 'sum' 'i' times
        |      j = j + 1;
        |    }
        |    result = sum; // This sum is effectively 'result * i'
        |    i = i + 1;
        |  }
        |
        |  result2 = (result / 2) * 2;
        |
        |  return (1 / (result - result2 + 1));
        |}
        |
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    executor.run()


    code =
      """
        |main() {
        |  var result, i, j, n, sum, result2;
        |  result = 1; // Factorial of 0 is 1 by definition
        |  n = input;
        |  if (n < 2) {
        |     return 0;
        |  }
        |
        |  i = 1;
        |  while (i <= n) {
        |    sum = 0; // Reset sum for each multiplication
        |    j = 0;
        |    while (j < i) {
        |      sum = sum + result; // Add 'result' to 'sum' 'i' times
        |      j = j + 1;
        |    }
        |    result = sum; // This sum is effectively 'result * i'
        |    i = i + 1;
        |  }
        |
        |  result2 = (result / 2) * 2;
        |
        |  return (1 / (result - result2));
        |}
        |
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }

  test("normalization work well") {
    var code =
      """
        |main() {
        |  var x, y, z, i, tmp;
        |
        |  tmp = input;
        |  y = &tmp;
        |  i = 0;
        |  z = [input, input];
        |  x = *y + z[i + 1];
        |
        |  return 0;
        |}
        |
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
    val executor = new LoopSummary(cfg)
    executor.run()

  }


  test("niv condition") {
    var code =
      """
        |main() {
        |  var k, i, n;
        |
        |  k = 1;
        |  i = 0;
        |  n = input;
        |  while (i <= n) {
        |    i = input;
        |  }
        |
        |  return 0;
        |}
        |
        |""".stripMargin;

    val future = Future {
      val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
      val executor = new LoopSummary(cfg)
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }
  }


  test("change uncomputable") {
    var code =
      """
        |main() {
        |  var k, i, n;
        |
        |  k = 1;
        |  i = 0;
        |  n = input;
        |  while (i <= n) {
        |    i = i + k;
        |    k = k + 1;
        |  }
        |
        |  return 0;
        |}
        |
        |""".stripMargin;

    val future = Future {
      val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
      val executor = new LoopSummary(cfg)
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

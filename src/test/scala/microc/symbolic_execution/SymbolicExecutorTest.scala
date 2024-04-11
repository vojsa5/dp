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
        |  if (i == 0 && n >= m) {
        |   k = 1 / 0;
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


  test("sequential multi-path loop") {
    var code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  res = 0;
        |  while (z < n) {
        |   if (x < n) {
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
  }


  test("periodic unbounded periodic loop finishes with summarization correctly") {
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


  test("periodic unbounded periodic loop finishes with summarization correctly arrays") {
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
        |  while (x[0] < n[0]) {
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



  test("periodic unbounded periodic loop with adding a variables") {
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


  test("unbounded periodic loop finishes with summarization correctly 3") {
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
        |  while (x + 1 < n) {
        |   if (z + 1 > x + 1) {
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
        |  while (x + 1 < n) {
        |   if (z + 1 > x + 1) {
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


  test("unbounded periodic loop finishes with summarization correctly arrays") {
    var code =
      """
        |main() {
        |  var n, x, z;
        |  n = [input];
        |  x = [input];
        |  z = [input];
        |  if (x[0] >= n[0]) {
        |   x[0] = n[0] - 1;
        |  }
        |  if (z[0] >= n[0]) {
        |   z[0] = n[0] - 1;
        |  }
        |  while (x[0] < n[0]) {
        |   if (z[0] > x[0]) {
        |     x[0] = x[0] + 1;
        |   }
        |   else {
        |     z[0] = z[0] + 1;
        |   }
        |  }
        |  return 1 / (x[0] - z[0] - 1);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummary(cfg)
    executor.run()

    code =
      """
        |main() {
        |  var n, x, z;
        |  n = [input];
        |  x = [input];
        |  z = [input];
        |  if (x[0] >= n[0]) {
        |   x[0] = n - 1;
        |  }
        |  if (z[0] >= n[0]) {
        |   z[0] = n - 1;
        |  }
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


    code =
      """
        |main() {
        |  var n, x, z;
        |  n = [input];
        |  x = [input];
        |  z = [input];
        |  if (x[0] >= n[0]) {
        |   x[0] = n[0] - 1;
        |  }
        |  if (z[0] >= n[0]) {
        |   z[0] = n[0] - 1;
        |  }
        |  while (x[0] < n[0]) {
        |   if (z[0] > x[0]) {
        |     x[0] = x[0] + 1;
        |   }
        |   else {
        |     z[0] = z[0] + 1;
        |   }
        |  }
        |  return 1 / (x[0] - z[0] + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummary(cfg)
    executor.run()
  }



  test("unbounded periodic loop finishes with summarization correctly arrays arrays") {
    var code =
      """
        |main() {
        |  var n, x, z;
        |  n = [[input]];
        |  x = [[input]];
        |  z = [[input]];
        |  if (x[0][0] >= n[0][0]) {
        |   x[0][0] = n[0][0] - 1;
        |  }
        |  if (z[0][0] >= n[0][0]) {
        |   z[0][0] = n[0][0] - 1;
        |  }
        |  while (x[0][0] < n[0][0]) {
        |   if (z[0][0] > x[0][0]) {
        |     x[0][0] = x[0][0] + 1;
        |   }
        |   else {
        |     z[0][0] = z[0][0] + 1;
        |   }
        |  }
        |  return 1 / (x[0][0] - z[0][0] - 1);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummary(cfg)
    executor.run()

    code =
      """
        |main() {
        |  var n, x, z;
        |  n = [[input]];
        |  x = [[input]];
        |  z = [[input]];
        |  if (x[0][0] >= n[0][0]) {
        |   x[0][0] = n[0][0] - 1;
        |  }
        |  if (z[0] >= n[0]) {
        |   z[0][0] = n[0][0] - 1;
        |  }
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


    code =
      """
        |main() {
        |  var n, x, z;
        |  n = [[input]];
        |  x = [[input]];
        |  z = [[input]];
        |  if (x[0][0] >= n[0][0]) {
        |   x[0][0] = n[0][0] - 1;
        |  }
        |  if (z[0][0] >= n[0][0]) {
        |   z[0][0] = n[0][0] - 1;
        |  }
        |  while (x[0][0] < n[0][0]) {
        |   if (z[0][0] > x[0][0]) {
        |     x[0][0] = x[0][0] + 1;
        |   }
        |   else {
        |     z[0][0] = z[0][0] + 1;
        |   }
        |  }
        |  return 1 / (x[0][0] - z[0][0] + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummary(cfg)
    executor.run()
  }


  test("unbounded periodic loop finishes with summarization correctly records") {
    var code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = {field: input};
        |  z = {field: input};
        |  if (x.field >= n) {
        |   x.field = n - 1;
        |  }
        |  if (z.field >= n) {
        |   z.field = n - 1;
        |  }
        |  while (x.field < n) {
        |   if (z.field > x.field) {
        |     x.field = x.field + 1;
        |   }
        |   else {
        |     z.field = z.field + 1;
        |   }
        |  }
        |  return 1 / (x.field - z.field - 1);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummary(cfg)
    executor.run()

    code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = {field: input};
        |  z = {field: input};
        |  if (x.field >= n) {
        |   x.field = n - 1;
        |  }
        |  if (z.field >= n) {
        |   z.field = n - 1;
        |  }
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

    code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = {field: input};
        |  z = {field: input};
        |  if (x.field >= n) {
        |   x.field = n - 1;
        |  }
        |  if (z.field >= n) {
        |   z.field = n - 1;
        |  }
        |  while (x.field < n) {
        |   if (z.field > x.field) {
        |     x.field = x.field + 1;
        |   }
        |   else {
        |     z.field = z.field + 1;
        |   }
        |  }
        |  return 1 / (x.field - z.field + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummary(cfg)
    executor.run()
  }


  test("unbounded periodic loop finishes with summarization correctly irregular increment") {
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
        |     z = z + 2;
        |   }
        |  }
        |  return 1 / (x - n - 1);
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
        |     z = z + 2;
        |   }
        |  }
        |  return 1 / (x - n);
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
        |     z = z + 2;
        |   }
        |  }
        |  return 1 / (x - n + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    executor.run()
  }


  test("unbounded periodic loop finishes with summarization correctly irregular symbolic increment") {
    var code =
      """
        |main() {
        |  var n, x, z, inc;
        |  n = input;
        |  x = input;
        |  z = input;
        |  inc = input;
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
        |     z = z + inc;
        |   }
        |  }
        |  return 1 / (x - n - 1);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    executor.run()


    code =
      """
        |main() {
        |  var n, x, z, inc;
        |  n = input;
        |  x = input;
        |  z = input;
        |  inc = input;
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
        |     z = z + inc;
        |   }
        |  }
        |  return 1 / (x - n);
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
        |  var n, x, z, inc;
        |  n = input;
        |  x = input;
        |  z = input;
        |  inc = input;
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
        |     z = z + input;
        |   }
        |  }
        |  return 1 / (x - n + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    executor.run()
  }


//  test("path cycle not at the beginning of the loop") {
//    var code =
//      """
//        |main() {
//        |  var n, x, z, a;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  a = input;
//        |  if (a < 10) {
//        |   a = 1;
//        |  }
//        |  if (x >= n) {
//        |   x = n - 1;
//        |  }
//        |  if (z >= n) {
//        |   z = n - 1;
//        |  }
//        |  while (x < n) {
//        |   if (a < 10) {
//        |     a = a + 1;
//        |   }
//        |   else {
//        |     if (z > x) {
//        |       x = x + 1;
//        |     }
//        |     else {
//        |       z = z + 2;
//        |     }
//        |   }
//        |  }
//        |  return 1 / (x - n - 1);
//        |}
//        |""".stripMargin;
//
//    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    var executor = new LoopSummary(cfg)
//    executor.run()
//
//
//    code =
//      """
//        |main() {
//        |  var n, x, z, a;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  a = input;
//        |  if (a < 10) {
//        |   a = 1;
//        |  }
//        |  if (x >= n) {
//        |   x = n - 1;
//        |  }
//        |  if (z >= n) {
//        |   z = n - 1;
//        |  }
//        |  while (x < n) {
//        |   if (a < 10) {
//        |     a = a + 1;
//        |   }
//        |   else {
//        |     if (z > x) {
//        |       x = x + 1;
//        |     }
//        |     else {
//        |       z = z + 2;
//        |     }
//        |   }
//        |  }
//        |  return 1 / (x - n);
//        |}
//        |""".stripMargin;
//
//    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    executor = new LoopSummary(cfg)
//    try {
//      executor.run()
//      fail("Expected a ExecutionException but it did not occur.")
//    }
//    catch {
//      case _: ExecutionException =>
//      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
//    }
//
//
//    code =
//      """
//        |main() {
//        |  var n, x, z, a;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  a = input;
//        |  if (a < 10) {
//        |   a = 1;
//        |  }
//        |  if (x >= n) {
//        |   x = n - 1;
//        |  }
//        |  if (z >= n) {
//        |   z = n - 1;
//        |  }
//        |  while (x < n) {
//        |   if (a < 10) {
//        |     a = a + 1;
//        |   }
//        |   else {
//        |     if (z > x) {
//        |       x = x + 1;
//        |     }
//        |     else {
//        |       z = z + 2;
//        |     }
//        |   }
//        |  }
//        |  return 1 / (x - n + 1);
//        |}
//        |""".stripMargin;
//
//    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    executor = new LoopSummary(cfg)
//    executor.run()
//  }


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
    executor.run()
    assert(executor.run() == 1)
  }


  test("basic nested summarization array") {
    var code =
      """
        |main() {
        |    var i, j, sum, res, n;
        |    i = 0;
        |    sum = [0];
        |    n = input;
        |    if (n <= 0) {
        |       n = 1;
        |    }
        |
        |    while (i < n) {
        |        j = 0;
        |        while (j < n) {
        |            sum[0] = sum[0] + 1;
        |            j = j + 1;
        |        }
        |        i = i + 1;
        |    }
        |
        |    if (sum[0] == n * n) {
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


  test("basic nested nested summarization arrays") {
    var code =
      """
        |main() {
        |    var i, j, k, sum, res, n;
        |    i = 0;
        |    sum = [0];
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
        |               sum[0] = sum[0] + 1;
        |               k = k + 1;
        |            }
        |            j = j + 1;
        |        }
        |        i = i + 1;
        |    }
        |
        |    if (sum[0] == n * n * n) {
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
    executor.run()
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
    executor.run()
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


  test("random generated test finishes with no error") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26;
        |  var0 = {gNqMDLMcfy:0,zkxbIeqIBW:6,LTCEjwyJEu:8,GyWGiMqije:3};
        |  var1 = 2;
        |  var2 = 1;
        |  var3 = 6;
        |  var4 = alloc 1;
        |  var5 = 0;
        |  var6 = 2;
        |  var7 = {cNlnxMBeVn:alloc 4};
        |  var8 = {kcruHvbwQz:[-1,3,3,6,2,2,-1]};
        |  var9 = 5;
        |  var10 = [alloc 1,alloc -1,alloc 8,alloc 8,alloc 3];
        |  var11 = {qydKuolMGM:alloc 2,TgjjsYmndd:4,wcMiswESVf:4,DSlZrnKtYQ:0,vbsdVOXOvy:4};
        |  var12 = 1;
        |  var13 = -1;
        |  var14 = 8;
        |  var15 = alloc 8;
        |  var16 = alloc 0;
        |  var17 = 4;
        |  var18 = alloc 7;
        |  var19 = alloc 7;
        |  var20 = {tojgCSrbms:3,IcDhEgNJjW:alloc alloc -1,KvINJvcTrN:alloc 6};
        |  var21 = -1;
        |  var22 = 1;
        |  var23 = 8;
        |  var24 = alloc [alloc 2,alloc 8,alloc 0,alloc 8,alloc 4,alloc -1,alloc 0];
        |  var25 = {LLeokGTSoT:-1,AwGowRpTnD:3,nQZdwKgDsM:alloc alloc 7,vPnoyKPxck:alloc alloc 5,LdXKjFBXat:alloc alloc 2};
        |  var26 = [0,5,-1,-1,8,1];
        |  output input;
        |  var26[0] = 4;
        |  output (((!1 + var25.AwGowRpTnD) + (input * (-1 - 2))) - 2);
        |  var26[3] = var25.LLeokGTSoT;
        |  if (input) {
        |    output var21;
        |    output var12;
        |    var15 = alloc input;
        |    var25 = var25;
        |  } else {
        |    if (var0.LTCEjwyJEu) {
        |      var10[2] = var16;
        |      output !var22;
        |      output !(8 - 3);
        |      output input;
        |    } else {
        |      if (var3) {
        |        output input;
        |        output input;
        |        output 0;
        |        output !var2;
        |        var3 = (8 - 2);
        |      } else {
        |        output input;
        |        output 4;
        |        output var13;
        |      }
        |      var13 = ((8 - 3) - !4);
        |      var14 = !(2 * 2);
        |      if (var0.zkxbIeqIBW) {
        |        output !var11.TgjjsYmndd;
        |        output !var11.wcMiswESVf;
        |        output var9;
        |        output (9 - 9);
        |      } else {
        |        var16 = alloc 8;
        |        var20 = var20;
        |        output input;
        |        output input;
        |        output !(8 * var0.LTCEjwyJEu);
        |      }
        |      var17 = input;
        |    }
        |    var26[2] = 8;
        |    if (var20.tojgCSrbms) {
        |      output !var0.gNqMDLMcfy;
        |      var3 = input;
        |      output 6;
        |      var3 = input;
        |      while (!0) {
        |        var17 = var20.tojgCSrbms;
        |        output var9;
        |        var6 = !4;
        |        output var21;
        |        var16 = var15;
        |      }
        |    } else {
        |      var24 = var24;
        |      output 7;
        |      var26[1] = var0.gNqMDLMcfy;
        |      var24 = &var10;
        |      if (1) {
        |        var2 = input;
        |        output 4;
        |        var26 = var26;
        |        output input;
        |        var16 = alloc 7;
        |      } else {
        |        output input;
        |        var1 = input;
        |        output (var17 * input);
        |      }
        |    }
        |    if (2) {
        |      var14 = var11.DSlZrnKtYQ;
        |      while (5) {
        |        output input;
        |        var0 = var0;
        |        var6 = (1 + 6);
        |        var17 = !4;
        |        output (!!input + (input + var6));
        |      }
        |      var26[2] = 0;
        |      var26[0] = !(2 * 3);
        |      output input;
        |    } else {
        |      while ((var23 - input)) {
        |        var12 = !0;
        |        var13 = (1 + 1);
        |        var24 = &var10;
        |      }
        |      if (input) {
        |        var9 = !2;
        |        output var0.LTCEjwyJEu;
        |        output 8;
        |        var20 = var20;
        |      } else {
        |        var14 = input;
        |        var1 = (4 + 8);
        |        output (!var22 * (input - var11.vbsdVOXOvy));
        |        var0 = var0;
        |        output var3;
        |      }
        |      var1 = input;
        |      var10[4] = alloc !7;
        |      output var21;
        |    }
        |    output !1;
        |  }
        |  if (input) {
        |    var10[3] = alloc !input;
        |    var12 = input;
        |    while (!8) {
        |      while (!input) {
        |        output var2;
        |        var10 = var10;
        |        output var20.tojgCSrbms;
        |        output var9;
        |      }
        |      while (input) {
        |        output !var11.vbsdVOXOvy;
        |        output input;
        |        var24 = alloc [alloc 4,alloc 4,alloc 6,alloc 3,alloc 2,alloc 1,alloc 2,alloc 3];
        |      }
        |      output var17;
        |      var10[3] = &var2;
        |      var7 = var7;
        |    }
        |  } else {
        |    output var22;
        |    var10[3] = alloc !input;
        |    var26[4] = var20.tojgCSrbms;
        |  }
        |  output !var11.TgjjsYmndd;
        |  while (4) {
        |    while (input) {
        |      if (8) {
        |        output !var11.wcMiswESVf;
        |        output input;
        |        var14 = (8 - 4);
        |        output var20.tojgCSrbms;
        |        var14 = 3;
        |      } else {
        |        var15 = &var9;
        |        output !var6;
        |        var12 = input;
        |        output var11.TgjjsYmndd;
        |        output var11.vbsdVOXOvy;
        |      }
        |      while (input) {
        |        var17 = !3;
        |        var19 = &var17;
        |        output !input;
        |      }
        |      var17 = var12;
        |      var26[0] = var0.gNqMDLMcfy;
        |      var5 = 7;
        |    }
        |    output (input * (!2 * 5));
        |    var10[0] = &var14;
        |    output 8;
        |    output input;
        |  }
        |  var4 = alloc input;
        |  return 3;
        |}
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
    val executor = new LoopSummary(cfg)
    executor.run()
  }


  test("random generated test finishes with no error 2") {
    val code =
      """
        |main() {
        |    var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16;
        |    var0 = 2;
        |    var1 = 0;
        |    var2 = alloc 2;
        |    var3 = alloc 3;
        |    var4 = {lnLBXVaSFe:alloc alloc -1,kjLXcdwndq:alloc alloc 2};
        |    var5 = -1;
        |    var6 = {kKBxNeHCeP:[-1,0,8,1,3,-1,8,2,3],FogZIoHFdb:0,GivSRKSzdu:alloc alloc 4,devBFpwYca:alloc 6};
        |    var7 = alloc -1;
        |    var8 = {LiJZrwrJao:3,IHvSjdwuoP:[5,7,2,1,4,6]};
        |    var9 = alloc 2;
        |    var10 = 3;
        |    var11 = {eEfZxCrfzu:alloc 0,xVvQireolI:3,pGdVKqXrhK:5,SmMKAWgdIg:alloc 3,OpjTwGZRMd:alloc 2};
        |    var12 = 0;
        |    var13 = 8;
        |    var14 = 7;
        |    var15 = {TaAZUNQfde:alloc alloc 4};
        |    var16 = [7,7,5,5,2];
        |    output ((input * !input) * (var10 + (var13 * !7)));
        |    while (!6) {
        |      output (!(5 - 0) - !var13);
        |      var16[2] = input;
        |      while (input) {
        |        if (var1) {
        |          output input;
        |          var11 = var11;
        |          output var11.xVvQireolI;
        |          output (var8.LiJZrwrJao - !!var0);
        |        } else {
        |          output input;
        |          output 2;
        |          var12 = !6;
        |        }
        |        if (var5) {
        |          var7 = var9;
        |          output var13;
        |          output input;
        |          var12 = input;
        |        } else {
        |          var2 = var9;
        |          output !(!var10 - var14);
        |          var8 = var8;
        |        }
        |        if (0) {
        |          output !((!9 + (input + input)) * 1);
        |          var13 = input;
        |          output input;
        |        } else {
        |          var7 = var9;
        |          output input;
        |          var0 = input;
        |        }
        |        output var1;
        |      }
        |      var11 = var11;
        |    }
        |    var12 = 1;
        |    var12 = input;
        |    while (var0) {
        |      while (input) {
        |        output (2 + input);
        |        if (!var14) {
        |          var4 = var4;
        |          var12 = 9;
        |          output var8.LiJZrwrJao;
        |        } else {
        |          output var1;
        |          output input;
        |          output 2;
        |        }
        |        output var11.xVvQireolI;
        |        var16[2] = input;
        |        var2 = var7;
        |      }
        |      var0 = input;
        |      output var11.xVvQireolI;
        |    }
        |    var6 = var6;
        |    var15 = var15;
        |    if (5) {
        |      var10 = 9;
        |      var16[4] = 3;
        |      output var10;
        |      var16[3] = var8.LiJZrwrJao;
        |    } else {
        |      if (input) {
        |        while (input) {
        |          output var14;
        |          var14 = 7;
        |          var11 = var11;
        |        }
        |        var3 = var9;
        |        var16[0] = input;
        |      } else {
        |        output input;
        |        if (var8.LiJZrwrJao) {
        |          var13 = input;
        |          output 7;
        |          output var8.LiJZrwrJao;
        |          var3 = alloc 1;
        |          var4 = var4;
        |        } else {
        |          output var6.FogZIoHFdb;
        |          output (input - input);
        |          var15 = var15;
        |          var14 = input;
        |          var16 = var16;
        |        }
        |        var16[0] = var6.FogZIoHFdb;
        |        var16[2] = !input;
        |        if (var11.pGdVKqXrhK) {
        |          output var11.pGdVKqXrhK;
        |          var8 = var8;
        |          var0 = (1 - 6);
        |        } else {
        |          output (!!7 - input);
        |          output var11.xVvQireolI;
        |          var2 = &var1;
        |          output 4;
        |        }
        |      }
        |      var14 = !input;
        |      while (!input) {
        |        var10 = (3 + 1);
        |        output var11.xVvQireolI;
        |        output (4 + 5);
        |        var3 = alloc !2;
        |        var16[4] = 6;
        |      }
        |    }
        |    var16[4] = var11.pGdVKqXrhK;
        |    return input;
        |  }
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
    val executor = new LoopSummary(cfg)
    executor.run()
  }



  test("random generated test finishes with no error 3") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19;
        |  var0 = 0;
        |  var1 = -1;
        |  var2 = [3,4,5,0,2,5,8,2,7];
        |  var3 = {zdWwCzijUg:[[2,-1,5,0,8],[7,-1,5,7,2,-1],[6,1,5,7,7,4],[7,6,0,4,6,2,3,1,0],[4,3,8,-1,6,0]],BoAmvMovVm:alloc 5,WtQRzqkGJp:1};
        |  var4 = alloc 6;
        |  var5 = 7;
        |  var6 = alloc 1;
        |  var7 = [0,8,3,1,0,7,1,0];
        |  var8 = 3;
        |  var9 = 6;
        |  var10 = 2;
        |  var11 = {XhXQvqWFDQ:4};
        |  var12 = 0;
        |  var13 = 8;
        |  var14 = 0;
        |  var15 = alloc [3,0,8,0,0,0];
        |  var16 = 4;
        |  var17 = 6;
        |  var18 = 2;
        |  var19 = [5,4,1,2,5,6,8];
        |  while (input) {
        |    while (var2[8]) {
        |      var15 = &var19;
        |      while (var3.WtQRzqkGJp) {
        |        var15 = &var7;
        |        output var18;
        |        output !input;
        |      }
        |      if (var2[7]) {
        |        var5 = input;
        |        var2 = var2;
        |        output (input - var19[2]);
        |      } else {
        |        output !var11.XhXQvqWFDQ;
        |        var14 = var11.XhXQvqWFDQ;
        |        var12 = [1,3,-1,0,8,0,1][0];
        |        output input;
        |        output (var12 - var3.WtQRzqkGJp);
        |      }
        |    }
        |    while ((input * var3.WtQRzqkGJp)) {
        |      if (input) {
        |        var9 = var1;
        |        output (var3.WtQRzqkGJp * var11.XhXQvqWFDQ);
        |        var0 = (4 - 4);
        |        output input;
        |        output var19[2];
        |      } else {
        |        var12 = input;
        |        output !(input + var0);
        |        output input;
        |        var7 = var7;
        |        output var11.XhXQvqWFDQ;
        |      }
        |      var7[4] = var2[6];
        |      while (!!7) {
        |        output var10;
        |        var11 = var11;
        |        output var3.WtQRzqkGJp;
        |        output input;
        |      }
        |      output !input;
        |    }
        |    var3 = var3;
        |    output input;
        |    var5 = var11.XhXQvqWFDQ;
        |  }
        |  output var11.XhXQvqWFDQ;
        |  while (!(var3.WtQRzqkGJp - input)) {
        |    while (!!input) {
        |      if (input) {
        |        output var14;
        |        var8 = input;
        |        output input;
        |        var16 = !6;
        |        output var0;
        |      } else {
        |        var15 = &var7;
        |        output var19[6];
        |        var13 = input;
        |        output (var2[3] - var19[6]);
        |      }
        |      var14 = var19[0];
        |      if (input) {
        |        output var1;
        |        output var3.WtQRzqkGJp;
        |        var9 = input;
        |      } else {
        |        output input;
        |        output input;
        |        output input;
        |      }
        |      if (!var14) {
        |        var4 = &var17;
        |        var16 = var3.WtQRzqkGJp;
        |        var17 = var3.WtQRzqkGJp;
        |        output var2[5];
        |      } else {
        |        output input;
        |        var5 = input;
        |        var7 = var7;
        |        output input;
        |      }
        |      var1 = var18;
        |    }
        |    if (var3.WtQRzqkGJp) {
        |      output !!-1;
        |      while (var14) {
        |        var8 = var11.XhXQvqWFDQ;
        |        var5 = input;
        |        output var3.WtQRzqkGJp;
        |      }
        |      var2[8] = var11.XhXQvqWFDQ;
        |      if (![-1,0,-1,-1,0,7,3,-1][0]) {
        |        output input;
        |        var0 = var9;
        |        var12 = (2 + 8);
        |      } else {
        |        var9 = (0 + -1);
        |        var19 = var19;
        |        output var3.WtQRzqkGJp;
        |        output input;
        |        var8 = var3.WtQRzqkGJp;
        |      }
        |    } else {
        |      if (var2[2]) {
        |        output input;
        |        var2 = var2;
        |        output var0;
        |      } else {
        |        output var1;
        |        output var3.WtQRzqkGJp;
        |        var7 = var7;
        |        output var7[6];
        |      }
        |      output input;
        |      var2[4] = var12;
        |    }
        |    while ((var19[2] + input)) {
        |      if (var14) {
        |        output var2[1];
        |        output var0;
        |        output var3.WtQRzqkGJp;
        |        output var3.WtQRzqkGJp;
        |      } else {
        |        var3 = var3;
        |        var5 = [5,6,0,5,7][3];
        |        var12 = [4,3,6,7,5,5,0,2][3];
        |      }
        |      while (var9) {
        |        output !(var18 + input);
        |        output var2[0];
        |        var6 = alloc -1;
        |        var10 = var5;
        |        var0 = var3.WtQRzqkGJp;
        |      }
        |      var7[1] = var3.WtQRzqkGJp;
        |    }
        |    while (var7[3]) {
        |      var5 = (input - input);
        |      var2 = var2;
        |      var19 = var19;
        |    }
        |    if ((var16 * var3.WtQRzqkGJp)) {
        |      output var3.WtQRzqkGJp;
        |      while (var11.XhXQvqWFDQ) {
        |        output (!!input * var2[1]);
        |        output input;
        |        output input;
        |      }
        |      var2[5] = !input;
        |      while (var3.WtQRzqkGJp) {
        |        output input;
        |        var11 = var11;
        |        output input;
        |        var18 = var5;
        |        output var3.WtQRzqkGJp;
        |      }
        |    } else {
        |      if ((var11.XhXQvqWFDQ * [5,7,0,1,0][2])) {
        |        var15 = &var7;
        |        var2 = var2;
        |        var19 = var19;
        |      } else {
        |        output var2[6];
        |        var3 = var3;
        |        var10 = [1,8,6,8,0][3];
        |        var5 = (3 + 5);
        |        output !!var5;
        |      }
        |      var3 = var3;
        |      if (var7[4]) {
        |        var17 = [-1,0,0,8,8,5][2];
        |        output input;
        |        output input;
        |        output !(input - var7[7]);
        |      } else {
        |        var5 = [0,0,7,6,2,6][4];
        |        var12 = [-1,6,3,2,1,4,5,4][2];
        |        output var9;
        |      }
        |    }
        |  }
        |  var7 = var7;
        |  var2[7] = var10;
        |  var17 = var2[2];
        |  return ([5,8,5,5,8,5,4,5][3] + var13);
        |}
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
    val executor = new LoopSummary(cfg)
    executor.run()
  }


  test("random generated test finishes with no error 4") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26,var27;
        |  var0 = {ZiDVisiYjZ:6,fVkBeOYvac:2,ANekffvDSl:1,orgIRcDHoa:6};
        |  var1 = 1;
        |  var2 = 4;
        |  var3 = {oagofINLUu:7,jkLsndkGTy:alloc 8,cTxsIAbxhU:2};
        |  var4 = 5;
        |  var5 = alloc 8;
        |  var6 = [7,1,4,5,2,2,2];
        |  var7 = alloc 2;
        |  var8 = {wuxRiNamVJ:alloc alloc 6,OaZdtzsxma:alloc 8};
        |  var9 = [alloc -1,alloc 5,alloc -1,alloc 5,alloc 3,alloc 8,alloc 7];
        |  var10 = 3;
        |  var11 = 7;
        |  var12 = 4;
        |  var13 = 3;
        |  var14 = 0;
        |  var15 = 4;
        |  var16 = [7,4,5,5,8,8,6,6];
        |  var17 = 0;
        |  var18 = 6;
        |  var19 = alloc alloc 2;
        |  var20 = {lOcqqrnldC:1,NQOqXljxeg:alloc 2};
        |  var21 = 4;
        |  var22 = [1,1,8,-1,7,0,5,7];
        |  var23 = 4;
        |  var24 = {EMQqEFLBWm:2,okmHFYsYta:0};
        |  var25 = 3;
        |  var26 = 3;
        |  var27 = [1,1,5,1,2,6,3,3];
        |  var6[1] = var24.EMQqEFLBWm;
        |  var9[2] = alloc var27[7];
        |  if (input) {
        |    output var0.orgIRcDHoa;
        |    output var12;
        |    if (var10) {
        |      while ((var13 < var14)) {
        |        output (input - input);
        |        var24 = var24;
        |        var16 = var16;
        |        var7 = &var12;
        |        var27 = var22;
        |        var13 = (var13 + 1);
        |      }
        |      output !var3.oagofINLUu;
        |      var27 = var16;
        |    } else {
        |      while ((var23 < var11)) {
        |        output (input - !input);
        |        var15 = var21;
        |        var2 = !1;
        |        output ((!var0.ANekffvDSl + var22[0]) - !(((1 - -1) * var0.fVkBeOYvac) * input));
        |        var23 = (var23 + 1);
        |      }
        |      output var22[4];
        |      if (!var24.EMQqEFLBWm) {
        |        var14 = input;
        |        output !var16[0];
        |        output input;
        |        var17 = !-1;
        |        output input;
        |      } else {
        |        output var3.oagofINLUu;
        |        output (var21 - !((var3.oagofINLUu - input) * ([4,1,7,0,-1,4][5] - !5)));
        |        var17 = (2 + 4);
        |        output var25;
        |        var18 = [3,6,3,4,4,-1][2];
        |      }
        |      while (var22[0]) {
        |        output !input;
        |        output (input - (var3.cTxsIAbxhU - input));
        |        output ((var22[1] * input) - var25);
        |        var0 = var0;
        |        output var17;
        |      }
        |      var27[0] = (!3 * [2,5,5,5,-1][4]);
        |    }
        |    while ((var21 < var1)) {
        |      output var0.orgIRcDHoa;
        |      var5 = alloc (7 - 6);
        |      output input;
        |      var12 = ((6 + 7) * [1,1,1,2,3,0,3][5]);
        |      var21 = (var21 + 1);
        |    }
        |    var12 = input;
        |  } else {
        |    while (input) {
        |      while ((var4 < var21)) {
        |        var12 = (5 * 6);
        |        var2 = [8,6,5,4,8,-1,6][4];
        |        var7 = alloc 7;
        |        var8 = var8;
        |        var24 = var24;
        |        var4 = (var4 + 1);
        |      }
        |      while (input) {
        |        output !var18;
        |        var4 = var3.oagofINLUu;
        |        var15 = [8,5,6,1,-1][1];
        |      }
        |      while ((var26 < var15)) {
        |        output input;
        |        output input;
        |        var7 = &var13;
        |        output (var16[7] - (input + input));
        |        output var0.fVkBeOYvac;
        |        var26 = (var26 + 1);
        |      }
        |      var9[6] = alloc [5,7,1,8,-1,0,4,5,3][6];
        |    }
        |    output !input;
        |    output !var27[1];
        |  }
        |  var16[6] = (var27[6] * input);
        |  var9[6] = alloc var6[6];
        |  if (input) {
        |    output !!var26;
        |    while (input) {
        |      if (input) {
        |        var4 = input;
        |        output (input * var17);
        |        output var22[6];
        |        var22 = var16;
        |      } else {
        |        var18 = input;
        |        output input;
        |        output !input;
        |        var9 = var9;
        |      }
        |      if (var14) {
        |        var27 = var22;
        |        output var0.orgIRcDHoa;
        |        output ((var3.cTxsIAbxhU * (var27[6] - !input)) + var16[5]);
        |      } else {
        |        var15 = var0.ZiDVisiYjZ;
        |        output (var3.cTxsIAbxhU - (var2 * var25));
        |        var16 = var16;
        |        output input;
        |      }
        |      if (var22[0]) {
        |        var18 = var0.orgIRcDHoa;
        |        var15 = input;
        |        var20 = var20;
        |        var5 = var7;
        |        output input;
        |      } else {
        |        var3 = var3;
        |        var7 = var7;
        |        var8 = var8;
        |        var10 = input;
        |        output (input + var22[2]);
        |      }
        |      var22[0] = var0.ANekffvDSl;
        |      while ((var13 < var18)) {
        |        var4 = (-1 - 5);
        |        var10 = (1 - 2);
        |        output var20.lOcqqrnldC;
        |        var16 = var22;
        |        output var22[5];
        |        var13 = (var13 + 1);
        |      }
        |    }
        |    var23 = var0.ANekffvDSl;
        |    while ((!var1 - !var3.cTxsIAbxhU)) {
        |      var6[3] = input;
        |      if (var0.orgIRcDHoa) {
        |        var26 = !8;
        |        output input;
        |        var4 = !5;
        |        output input;
        |        var23 = var24.okmHFYsYta;
        |      } else {
        |        output (!var10 + (var0.orgIRcDHoa - !(!6 + (8 * 0))));
        |        var5 = var7;
        |        output (!var16[1] + !var2);
        |        var25 = var4;
        |      }
        |      var11 = !input;
        |      while ((var25 < var2)) {
        |        output input;
        |        output input;
        |        var6 = var6;
        |        var25 = (var25 + 1);
        |      }
        |    }
        |  } else {
        |    var12 = var25;
        |    var27[4] = input;
        |    output var2;
        |    while (!var11) {
        |      var27 = var22;
        |      while ((var2 < var15)) {
        |        var6 = var6;
        |        output input;
        |        var24 = var24;
        |        output input;
        |        var2 = (var2 + 1);
        |      }
        |      while ((!2 * input)) {
        |        output input;
        |        var1 = input;
        |        output var6[0];
        |      }
        |      while (var22[4]) {
        |        var26 = input;
        |        var1 = (3 * 8);
        |        output var25;
        |        output var27[2];
        |        var7 = var5;
        |      }
        |      if (!var13) {
        |        output var18;
        |        var8 = var8;
        |        output !!input;
        |        output input;
        |        var26 = [0,6,2,7,7,8][0];
        |      } else {
        |        output var11;
        |        output !var15;
        |        var19 = var19;
        |      }
        |    }
        |    output (([8,-1,5,0,0,8,6][4] * [2,6,0,7,0,1,1,0,5][6]) + input);
        |  }
        |  output (var24.EMQqEFLBWm + var24.okmHFYsYta);
        |  return var10;
        |}
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
    val executor = new SymbolicExecutor(cfg)
    executor.run()
  }


  test("random generated test finishes with no error 5") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26,var27;
        |  var0 = {ZiDVisiYjZ:6,fVkBeOYvac:2,ANekffvDSl:1,orgIRcDHoa:6};
        |  var1 = 1;
        |  var2 = 4;
        |  var3 = {oagofINLUu:7,jkLsndkGTy:alloc 8,cTxsIAbxhU:2};
        |  var4 = 5;
        |  var5 = alloc 8;
        |  var6 = [7,1,4,5,2,2,2];
        |  var7 = alloc 2;
        |  var8 = {wuxRiNamVJ:alloc alloc 6,OaZdtzsxma:alloc 8};
        |  var9 = [alloc -1,alloc 5,alloc -1,alloc 5,alloc 3,alloc 8,alloc 7];
        |  var10 = 3;
        |  var11 = 7;
        |  var12 = 4;
        |  var13 = 3;
        |  var14 = 0;
        |  var15 = 4;
        |  var16 = [7,4,5,5,8,8,6,6];
        |  var17 = 0;
        |  var18 = 6;
        |  var19 = alloc alloc 2;
        |  var20 = {lOcqqrnldC:1,NQOqXljxeg:alloc 2};
        |  var21 = 4;
        |  var22 = [1,1,8,-1,7,0,5,7];
        |  var23 = 4;
        |  var24 = {EMQqEFLBWm:2,okmHFYsYta:0};
        |  var25 = 3;
        |  var26 = 3;
        |  var27 = [1,1,5,1,2,6,3,3];
        |  var6[1] = var24.EMQqEFLBWm;
        |  var9[2] = alloc var27[7];
        |  if (input) {
        |    output var0.orgIRcDHoa;
        |    output var12;
        |    if (var10) {
        |      while ((var13 < var14)) {
        |        output (input - input);
        |        var24 = var24;
        |        var16 = var16;
        |        var7 = &var12;
        |        var27 = var22;
        |        var13 = (var13 + 1);
        |      }
        |      output !var3.oagofINLUu;
        |      var27 = var16;
        |    } else {
        |      while ((var23 < var11)) {
        |        output (input - !input);
        |        var15 = var21;
        |        var2 = !1;
        |        output ((!var0.ANekffvDSl + var22[0]) - !(((1 - -1) * var0.fVkBeOYvac) * input));
        |        var23 = (var23 + 1);
        |      }
        |      output var22[4];
        |      if (!var24.EMQqEFLBWm) {
        |        var14 = input;
        |        output !var16[0];
        |        output input;
        |        var17 = !-1;
        |        output input;
        |      } else {
        |        output var3.oagofINLUu;
        |        output (var21 - !((var3.oagofINLUu - input) * ([4,1,7,0,-1,4][5] - !5)));
        |        var17 = (2 + 4);
        |        output var25;
        |        var18 = [3,6,3,4,4,-1][2];
        |      }
        |      while (var22[0]) {
        |        output !input;
        |        output (input - (var3.cTxsIAbxhU - input));
        |        output ((var22[1] * input) - var25);
        |        var0 = var0;
        |        output var17;
        |      }
        |      var27[0] = (!3 * [2,5,5,5,-1][4]);
        |    }
        |    while ((var21 < var1)) {
        |      output var0.orgIRcDHoa;
        |      var5 = alloc (7 - 6);
        |      output input;
        |      var12 = ((6 + 7) * [1,1,1,2,3,0,3][5]);
        |      var21 = (var21 + 1);
        |    }
        |    var12 = input;
        |  } else {
        |    while (input) {
        |      while ((var4 < var21)) {
        |        var12 = (5 * 6);
        |        var2 = [8,6,5,4,8,-1,6][4];
        |        var7 = alloc 7;
        |        var8 = var8;
        |        var24 = var24;
        |        var4 = (var4 + 1);
        |      }
        |      while (input) {
        |        output !var18;
        |        var4 = var3.oagofINLUu;
        |        var15 = [8,5,6,1,-1][1];
        |      }
        |      while ((var26 < var15)) {
        |        output input;
        |        output input;
        |        var7 = &var13;
        |        output (var16[7] - (input + input));
        |        output var0.fVkBeOYvac;
        |        var26 = (var26 + 1);
        |      }
        |      var9[6] = alloc [5,7,1,8,-1,0,4,5,3][6];
        |    }
        |    output !input;
        |    output !var27[1];
        |  }
        |  var16[6] = (var27[6] * input);
        |  var9[6] = alloc var6[6];
        |  if (input) {
        |    output !!var26;
        |    while (input) {
        |      if (input) {
        |        var4 = input;
        |        output (input * var17);
        |        output var22[6];
        |        var22 = var16;
        |      } else {
        |        var18 = input;
        |        output input;
        |        output !input;
        |        var9 = var9;
        |      }
        |      if (var14) {
        |        var27 = var22;
        |        output var0.orgIRcDHoa;
        |        output ((var3.cTxsIAbxhU * (var27[6] - !input)) + var16[5]);
        |      } else {
        |        var15 = var0.ZiDVisiYjZ;
        |        output (var3.cTxsIAbxhU - (var2 * var25));
        |        var16 = var16;
        |        output input;
        |      }
        |      if (var22[0]) {
        |        var18 = var0.orgIRcDHoa;
        |        var15 = input;
        |        var20 = var20;
        |        var5 = var7;
        |        output input;
        |      } else {
        |        var3 = var3;
        |        var7 = var7;
        |        var8 = var8;
        |        var10 = input;
        |        output (input + var22[2]);
        |      }
        |      var22[0] = var0.ANekffvDSl;
        |      while ((var13 < var18)) {
        |        var4 = (-1 - 5);
        |        var10 = (1 - 2);
        |        output var20.lOcqqrnldC;
        |        var16 = var22;
        |        output var22[5];
        |        var13 = (var13 + 1);
        |      }
        |    }
        |    var23 = var0.ANekffvDSl;
        |    while ((!var1 - !var3.cTxsIAbxhU)) {
        |      var6[3] = input;
        |      if (var0.orgIRcDHoa) {
        |        var26 = !8;
        |        output input;
        |        var4 = !5;
        |        output input;
        |        var23 = var24.okmHFYsYta;
        |      } else {
        |        output (!var10 + (var0.orgIRcDHoa - !(!6 + (8 * 0))));
        |        var5 = var7;
        |        output (!var16[1] + !var2);
        |        var25 = var4;
        |      }
        |      var11 = !input;
        |      while ((var25 < var2)) {
        |        output input;
        |        output input;
        |        var6 = var6;
        |        var25 = (var25 + 1);
        |      }
        |    }
        |  } else {
        |    var12 = var25;
        |    var27[4] = input;
        |    output var2;
        |    while (!var11) {
        |      var27 = var22;
        |      while ((var2 < var15)) {
        |        var6 = var6;
        |        output input;
        |        var24 = var24;
        |        output input;
        |        var2 = (var2 + 1);
        |      }
        |      while ((!2 * input)) {
        |        output input;
        |        var1 = input;
        |        output var6[0];
        |      }
        |      while (var22[4]) {
        |        var26 = input;
        |        var1 = (3 * 8);
        |        output var25;
        |        output var27[2];
        |        var7 = var5;
        |      }
        |      if (!var13) {
        |        output var18;
        |        var8 = var8;
        |        output !!input;
        |        output input;
        |        var26 = [0,6,2,7,7,8][0];
        |      } else {
        |        output var11;
        |        output !var15;
        |        var19 = var19;
        |      }
        |    }
        |    output (([8,-1,5,0,0,8,6][4] * [2,6,0,7,0,1,1,0,5][6]) + input);
        |  }
        |  output (var24.EMQqEFLBWm + var24.okmHFYsYta);
        |  return var10;
        |}
        |""".stripMargin

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
    val executor = new SymbolicExecutor(cfg, searchStrategy = new HeuristicBasedStateMerging(new BFSSearchStrategy, variableCosts, 3))
    executor.run()
  }


  test("random generated test finishes with no error 6") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17;
        |  var0 = 0;
        |  var1 = 8;
        |  var2 = 2;
        |  var3 = [5,2,1,8,3,-1,7,8,2];
        |  var4 = 8;
        |  var5 = [0,3,3,8,7,1];
        |  var6 = {TxDxdCMpIF:1,HDSBrIAuKM:5,kUyibOAvPZ:-1,dxOKbiyZgQ:alloc [5,7,4,4,1,5,2,7],dkjOARXwLV:alloc 3};
        |  var7 = {TAILvftcuo:alloc 6,awEtLTnPUr:4,MQmJMqvkqB:2};
        |  var8 = alloc 4;
        |  var9 = 2;
        |  var10 = alloc 2;
        |  var11 = alloc 0;
        |  var12 = alloc 6;
        |  var13 = alloc alloc 0;
        |  var14 = -1;
        |  var15 = 2;
        |  var16 = alloc 3;
        |  var17 = [5,1,4,0,-1];
        |  output var0;
        |  var17[0] = input;
        |  var4 = (var5[3] + var6.kUyibOAvPZ);
        |  while ((var14 < var4)) {
        |    output var7.awEtLTnPUr;
        |    var0 = var9;
        |    var0 = !!input;
        |    var14 = (var14 + 1);
        |  }
        |  var14 = var0;
        |  return var5[1];
        |}
        |""".stripMargin

    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program)

    val stateHistory = new StateHistory()
    val executor = new SymbolicExecutor(cfg, searchStrategy = new RandomPathSelectionStrategy(stateHistory), stateHistory = Some(stateHistory))
    executor.run()
  }



  test("random generated test finishes with no error 7") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16;
        |  var0 = 4;
        |  var1 = alloc 8;
        |  var2 = 6;
        |  var3 = alloc 6;
        |  var4 = 1;
        |  var5 = {iHoEIVSEub:0,VcKKMxqvgk:5,NAwBbwxBtW:5,nHGYljuDmO:alloc alloc 6,rilMbrwwom:5};
        |  var6 = 8;
        |  var7 = 3;
        |  var8 = [-1,0,0,0,5];
        |  var9 = 7;
        |  var10 = [1,7,8,-1,0,-1];
        |  var11 = 4;
        |  var12 = 7;
        |  var13 = alloc alloc 1;
        |  var14 = 6;
        |  var15 = alloc alloc alloc 2;
        |  var16 = [7,4,3,2,3,1,8,6,4];
        |  while ((var9 < var2)) {
        |    if (var8[2]) {
        |      var10 = var10;
        |      var10[0] = var7;
        |      var2 = input;
        |    } else {
        |      var16[8] = var10[5];
        |      while (input) {
        |        output var5.VcKKMxqvgk;
        |        output var8[2];
        |        var11 = input;
        |      }
        |      var13 = var13;
        |      while (([1,7,5,2,2,-1,0,0,6][0] * input)) {
        |        var1 = &var9;
        |        output var10[3];
        |        var2 = input;
        |      }
        |    }
        |    var15 = &var13;
        |    var5 = var5;
        |    output var5.NAwBbwxBtW;
        |    var9 = (var9 + 1);
        |  }
        |  if (var5.iHoEIVSEub) {
        |    var8[2] = var5.NAwBbwxBtW;
        |    output var12;
        |    var7 = var10[5];
        |    while ((var9 < var12)) {
        |      while ((var9 < var7)) {
        |        output (((input + input) - !input) - var11);
        |        var15 = var15;
        |        var14 = !4;
        |        output !var10[5];
        |        var9 = (var9 + 1);
        |      }
        |      while ((var7 < var2)) {
        |        var15 = alloc alloc alloc 0;
        |        var5 = var5;
        |        var1 = &var7;
        |        output !!input;
        |        output var5.iHoEIVSEub;
        |        var7 = (var7 + 1);
        |      }
        |      if ((input + var5.VcKKMxqvgk)) {
        |        var1 = var1;
        |        output input;
        |        output !(var8[2] - input);
        |      } else {
        |        var12 = var9;
        |        output var16[8];
        |        output var8[3];
        |      }
        |      var9 = var5.iHoEIVSEub;
        |      while (input) {
        |        var7 = [5,8,2,4,0,-1][4];
        |        output ((var12 + input) + input);
        |        output !!input;
        |      }
        |      var9 = (var9 + 1);
        |    }
        |  } else {
        |    var16[6] = var16[7];
        |    var0 = input;
        |    if (var10[1]) {
        |      if (![0,2,0,6,7][3]) {
        |        output !var2;
        |        var8 = var8;
        |        output input;
        |        output var5.iHoEIVSEub;
        |      } else {
        |        var8 = var8;
        |        var11 = var5.iHoEIVSEub;
        |        var10 = var10;
        |        output input;
        |        var12 = input;
        |      }
        |      var16[1] = !!2;
        |      while ((var0 < var0)) {
        |        var7 = input;
        |        output var8[1];
        |        var7 = var5.NAwBbwxBtW;
        |        output var6;
        |        output (var5.rilMbrwwom + input);
        |        var0 = (var0 + 1);
        |      }
        |      output input;
        |    } else {
        |      output input;
        |      while ((var6 < var12)) {
        |        output var6;
        |        var9 = [2,0,4,-1,1,8,5][6];
        |        output input;
        |        output var4;
        |        output var10[0];
        |        var6 = (var6 + 1);
        |      }
        |      var6 = !input;
        |    }
        |    while ((var0 < var11)) {
        |      if (var4) {
        |        output (var8[1] + input);
        |        var8 = var8;
        |        output (input * input);
        |      } else {
        |        output input;
        |        output !var16[5];
        |        var4 = (1 - 1);
        |      }
        |      while (var8[4]) {
        |        var8 = var8;
        |        var16 = var16;
        |        output ((!(var2 - input) * var5.iHoEIVSEub) * var5.rilMbrwwom);
        |        output var16[6];
        |        var8 = var8;
        |      }
        |      while (input) {
        |        output !var5.rilMbrwwom;
        |        var0 = [7,8,8,6,4,1][5];
        |        var15 = var15;
        |        var7 = [1,1,8,7,1,4,3][2];
        |        var15 = var15;
        |      }
        |      var16 = var16;
        |      while (var5.rilMbrwwom) {
        |        var2 = !3;
        |        var14 = [3,4,3,8,4,1][1];
        |        output input;
        |        output var5.rilMbrwwom;
        |        output (input + input);
        |      }
        |      var0 = (var0 + 1);
        |    }
        |  }
        |  output var0;
        |  if (var8[3]) {
        |    while (input) {
        |      var4 = var12;
        |      var0 = input;
        |      var2 = var0;
        |      if (var0) {
        |        output input;
        |        var4 = [-1,5,4,3,2][0];
        |        output input;
        |        var8 = var8;
        |      } else {
        |        var4 = (8 - 6);
        |        var0 = input;
        |        output (!!var5.NAwBbwxBtW + var5.iHoEIVSEub);
        |        output var5.NAwBbwxBtW;
        |        output ((input + !var0) * var14);
        |      }
        |      if (input) {
        |        var16 = var16;
        |        var9 = [8,2,1,8,3,1,7,1,7][3];
        |        var14 = input;
        |        var13 = &var3;
        |      } else {
        |        var10 = var10;
        |        output var16[8];
        |        var10 = var10;
        |        var13 = alloc alloc 6;
        |      }
        |    }
        |    if (!var11) {
        |      while (!!8) {
        |        output input;
        |        output var5.NAwBbwxBtW;
        |        output var5.NAwBbwxBtW;
        |        output (var6 - var5.NAwBbwxBtW);
        |      }
        |      var10[1] = ([-1,1,7,1,1][2] - input);
        |      while (var10[3]) {
        |        output !var5.NAwBbwxBtW;
        |        var16 = var16;
        |        var1 = var3;
        |        output var6;
        |        output !var5.rilMbrwwom;
        |      }
        |      var14 = var5.iHoEIVSEub;
        |    } else {
        |      while ((var9 < var14)) {
        |        output var16[8];
        |        var3 = var1;
        |        var9 = var6;
        |        var9 = (var9 + 1);
        |      }
        |      var15 = alloc alloc alloc 4;
        |      if ((input - !5)) {
        |        output var9;
        |        output var16[7];
        |        var9 = (6 - -1);
        |      } else {
        |        var13 = &var3;
        |        var8 = var8;
        |        var14 = (6 + 4);
        |      }
        |      if (((1 - 7) + (8 + 6))) {
        |        output var5.iHoEIVSEub;
        |        var15 = alloc alloc alloc 7;
        |        output (!input * var16[8]);
        |      } else {
        |        output !var8[0];
        |        var5 = var5;
        |        output var5.NAwBbwxBtW;
        |        output input;
        |      }
        |    }
        |    while (var16[6]) {
        |      var12 = input;
        |      var10[5] = var6;
        |      if (var5.iHoEIVSEub) {
        |        output (var10[2] + !(var8[0] * !var5.iHoEIVSEub));
        |        output input;
        |        output var8[0];
        |        output (var5.NAwBbwxBtW * var5.NAwBbwxBtW);
        |        output input;
        |      } else {
        |        var2 = input;
        |        output var5.iHoEIVSEub;
        |        output input;
        |        output var7;
        |      }
        |      output !var5.rilMbrwwom;
        |      if (input) {
        |        var15 = alloc alloc alloc 1;
        |        output input;
        |        var10 = var10;
        |      } else {
        |        output var5.rilMbrwwom;
        |        output var2;
        |        output ((var8[2] * (input - var12)) - var5.NAwBbwxBtW);
        |        output !input;
        |      }
        |    }
        |    while ((var12 < var7)) {
        |      var8 = var8;
        |      var3 = &var14;
        |      var9 = !input;
        |      if (input) {
        |        output var8[4];
        |        var15 = var15;
        |        output ((!input - var4) * input);
        |        var15 = alloc alloc alloc 3;
        |      } else {
        |        output (input - var14);
        |        var14 = !4;
        |        output var5.rilMbrwwom;
        |      }
        |      var12 = (var12 + 1);
        |    }
        |    while (input) {
        |      var5 = var5;
        |      while ((var11 < var0)) {
        |        output var10[2];
        |        var8 = var8;
        |        var13 = &var3;
        |        var3 = &var0;
        |        var11 = (var11 + 1);
        |      }
        |      var8[2] = input;
        |    }
        |  } else {
        |    var3 = alloc ![-1,0,5,6,1,5][5];
        |    output input;
        |    output input;
        |    while (var8[2]) {
        |      var3 = alloc input;
        |      var12 = ([7,1,3,1,3,8][0] - !0);
        |      var8[2] = input;
        |    }
        |    output var5.rilMbrwwom;
        |  }
        |  var13 = &var1;
        |  return (var5.iHoEIVSEub - input);
        |}
        |""".stripMargin

    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program)

    val stateHistory = new StateHistory()
    val executor = new SymbolicExecutor(cfg, searchStrategy = new AgressiveStateMerging(new RandomPathSelectionStrategy(stateHistory)), stateHistory = Some(stateHistory), printStats = false)
    executor.run()
  }



}

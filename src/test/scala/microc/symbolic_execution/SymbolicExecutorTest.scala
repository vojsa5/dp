package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.{CodeLoc, Decl, NestedBlockStmt, Number, WhileStmt}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.symbolic_execution.optimizations.subsumption.PathSubsumption
import microc.symbolic_execution.optimizations.summarization.LoopSummarization
import microc.symbolic_execution.optimizations.merging.{AggressiveStateMerging, HeuristicBasedStateMerging}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

import scala.collection.immutable.HashSet
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
    val executor = new LoopSummarization(cfg);
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
    val executor = new LoopSummarization(cfg);
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), searchStrategy = new DFSSearchStrategy)
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
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))), searchStrategy = new DFSSearchStrategy)
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
    val executor = new LoopSummarization(cfg)
    executor.run()
  }

  test("sequential unbounded loop finishes with summarization correctly 2") {
    val code =
      """
        |main() {
        |  var a, i, n;
        |  a = 0;
        |  i = input;
        |  n = input;
        |
        |  while (i < n) {
        |    a = a + 2;
        |    i = i + 1;
        |  }
        |
        |  if (a == 15) {
        |    a = 1 / 0;
        |  }
        |  else {
        |
        |  }
        |
        |  return 0;
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
        |  if (x + 1 >= n) {
        |   x = n - 2;
        |  }
        |  if (z + 1 >= n) {
        |   z = n - 2;
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
    var executor = new LoopSummarization(cfg)
    executor.run()


    code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  if (x + 1 >= n) {
        |   x = n - 2;
        |  }
        |  if (z + 1 >= n) {
        |   z = n - 2;
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
    executor = new LoopSummarization(cfg)
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
        |  if (x + 1 >= n) {
        |   x = n - 2;
        |  }
        |  if (z + 1 >= n) {
        |   z = n - 2;
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
    executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
    executor.run()

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
        |  return 1 / (x[0] - z[0]);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
    executor.run()
  }


  test("unbounded periodic loop finishes with summarization correctly pointers") {
    var code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = alloc input;
        |  z = alloc input;
        |  if (*x >= n) {
        |   *x = n - 1;
        |  }
        |  if (*z >= n) {
        |   *z = n - 1;
        |  }
        |  while (*x < n) {
        |   if (*z > *x) {
        |     *x = *x + 1;
        |   }
        |   else {
        |     *z = *z + 1;
        |   }
        |  }
        |  return 1 / (*x - *z - 1);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummarization(cfg)
    executor.run()

    code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = alloc input;
        |  z = alloc input;
        |  if (*x >= n) {
        |   *x = n - 1;
        |  }
        |  if (*z >= n) {
        |   *z = n - 1;
        |  }
        |  while (*x < n) {
        |   if (*z > *x) {
        |     *x = *x + 1;
        |   }
        |   else {
        |     *z = *z + 1;
        |   }
        |  }
        |  return 1 / (*x - *z);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummarization(cfg)
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
        |  x = alloc input;
        |  z = alloc input;
        |  if (*x >= n) {
        |   *x = n - 1;
        |  }
        |  if (*z >= n) {
        |   *z = n - 1;
        |  }
        |  while (*x < n) {
        |   if (*z > *x) {
        |     *x = *x + 1;
        |   }
        |   else {
        |     *z = *z + 1;
        |   }
        |  }
        |  return 1 / (*x - *z + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
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
    executor = new LoopSummarization(cfg)
    executor.run()
  }


//  test("unbounded periodic loop finishes with summarization correctly irregular symbolic increment") {
//    var code =
//      """
//        |main() {
//        |  var n, x, z, inc;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  inc = input;
//        |  if (x >= n) {
//        |   x = n - 1;
//        |  }
//        |  if (z >= n) {
//        |   z = n - 1;
//        |  }
//        |  while (x < n) {
//        |   if (z > x) {
//        |     x = x + 1;
//        |   }
//        |   else {
//        |     z = z + inc;
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
//        |  var n, x, z, inc;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  inc = input;
//        |  if (x >= n) {
//        |   x = n - 1;
//        |  }
//        |  if (z >= n) {
//        |   z = n - 1;
//        |  }
//        |  while (x < n) {
//        |   if (z > x) {
//        |     x = x + 1;
//        |   }
//        |   else {
//        |     z = z + inc;
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
//        |  var n, x, z, inc;
//        |  n = input;
//        |  x = input;
//        |  z = input;
//        |  inc = input;
//        |  if (x >= n) {
//        |   x = n - 1;
//        |  }
//        |  if (z >= n) {
//        |   z = n - 1;
//        |  }
//        |  while (x < n) {
//        |   if (z > x) {
//        |     x = x + 1;
//        |   }
//        |   else {
//        |     z = z + input;
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
        |    var j, sum, res, n;
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
    var executor = new LoopSummarization(cfg)
    assert(executor.run() == 1)
  }


  test("unrolled nested summarization 2") {
    var code =
      """
        |main() {
        |    var i, sum, res, n;
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
    var executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
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
    var executor = new LoopSummarization(cfg)
    executor.run()
    assert(executor.run() == 1)
  }


  test("nested periodic loop") {
//    var code =
//      """
//        |main() {
//        |  var n, x, z, res, i, realX, realZ;
//        |  n = input;
//        |  x = input;
//        |  z = input;
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
//        |  realX = x;
//        |  realZ = z;
//        |
//        |  i = 0;
//        |  while (i < n) {
//        |     x = realX;
//        |     z = realZ;
//        |     while (x < n) {
//        |        if (z > x) {
//        |           x = x + 1;
//        |        }
//        |        else {
//        |           z = z + 1;
//        |        }
//        |     }
//        |     res = res + x;
//        |     i = i + 1;
//        |  }
//        |
//        |  if (res == n * n) {
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
//    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    var executor = new LoopSummarization(cfg)
//    executor.run()
//    assert(executor.run() == 1)


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
    var executor = new LoopSummarization(cfg)
    executor.run()
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
    val executor = new LoopSummarization(cfg)
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
      val executor = new LoopSummarization(cfg)
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
      val executor = new LoopSummarization(cfg)
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
    val executor = new LoopSummarization(cfg)
    executor.run()
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
    val stateHistory = new StateHistory()
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, ctx = ctx, subsumption = Some(new PathSubsumption(new ConstraintSolver(ctx))), searchStrategy = new RandomPathSelectionStrategy(stateHistory), stateHistory = Some(stateHistory))
    executor.run()
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
    val stateHistory = new StateHistory()
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, ctx = ctx, subsumption = Some(new PathSubsumption(new ConstraintSolver(ctx))), searchStrategy = new RandomPathSelectionStrategy(stateHistory), stateHistory = Some(stateHistory))
    executor.run()
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


  test("random generated test finishes with no error 6") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26;
        |  var0 = 0;
        |  var1 = 5;
        |  var2 = 3;
        |  var3 = 2;
        |  var4 = {cHBiKkwpZV:0,tNuYDkeSNC:alloc -1,efNRyctmGF:7,bBDGoCFXBA:8};
        |  var5 = 3;
        |  var6 = {WHLokIkAyA:alloc 6};
        |  var7 = 6;
        |  var8 = alloc 1;
        |  var9 = 1;
        |  var10 = 1;
        |  var11 = 2;
        |  var12 = alloc 8;
        |  var13 = -1;
        |  var14 = 5;
        |  var15 = alloc 7;
        |  var16 = 1;
        |  var17 = [alloc 8,alloc 2,alloc 0,alloc 0,alloc 8,alloc 7,alloc 1,alloc 2,alloc -1];
        |  var18 = {BJvuAvwVou:8,GsGXzoMDAE:alloc alloc 7};
        |  var19 = [2,1,7,1,5,0,8,0,6];
        |  var20 = alloc -1;
        |  var21 = alloc alloc 7;
        |  var22 = alloc [alloc -1,alloc 6,alloc 5,alloc 7,alloc 2,alloc 6,alloc 8,alloc 6,alloc 4];
        |  var23 = alloc 8;
        |  var24 = alloc alloc alloc 3;
        |  var25 = alloc alloc 0;
        |  var26 = [-1,2,4,6,1];
        |  while ((var13 < var5)) {
        |    while ((var16 < var11)) {
        |      var0 = !var18.BJvuAvwVou;
        |      var16 = (var16 + 1);
        |    }
        |    while ((var16 < var10)) {
        |      while ((var0 < var5)) {
        |        output var26[0];
        |        var0 = (var0 + 1);
        |      }
        |      var19[7] = (!(6 + 8) - input);
        |      var16 = (var16 + 1);
        |    }
        |    if (input) {
        |      while ((var2 < var9)) {
        |        var2 = (var2 + 1);
        |      }
        |      var1 = input;
        |    } else {
        |      if (input) {} else {}
        |      output var18.BJvuAvwVou;
        |      var26[2] = ((input + input) * var9);
        |    }
        |    output var18.BJvuAvwVou;
        |    var13 = (var13 + 1);
        |  }
        |  var2 = (var19[8] + (input - input));
        |  while (input) {}
        |  output var26[0];
        |  return input;
        |}
        |""".stripMargin

    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program)

    val stateHistory = new StateHistory()
    val executor = new SymbolicExecutor(cfg, searchStrategy = new RandomPathSelectionStrategy(stateHistory), stateHistory = Some(stateHistory))
    executor.run()
  }



  test("nasty summarization test1") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26,var27;
        |  var0 = {zWiHmxMkme:1,KCckbJgOSE:8,PzLwkpeQto:7};
        |  var1 = 1;
        |  var2 = 0;
        |  var3 = alloc 0;
        |  var4 = [2,1,1,0,1,6];
        |  var5 = alloc alloc 5;
        |  var6 = 0;
        |  var7 = 5;
        |  var8 = 4;
        |  var9 = alloc alloc 2;
        |  var10 = alloc 6;
        |  var11 = 8;
        |  var12 = alloc 1;
        |  var13 = alloc alloc alloc 2;
        |  var14 = {dbcqMEeaWa:8,NJGgkmBLvD:0,CyreIezFTA:[7,3,5,-1,3,5,8,1],EFgEVXEzKB:alloc 3};
        |  var15 = alloc alloc 8;
        |  var16 = 5;
        |  var17 = {ZwUXtHoCfU:1,tekdQaWOeb:7,XYUpcanEai:1};
        |  var18 = 4;
        |  var19 = alloc 6;
        |  var20 = {VIlTIzVhZK:3,LUJkdCpqLh:alloc alloc alloc alloc 5,eQvClWeazG:7,waYAWcmcvX:8};
        |  var21 = -1;
        |  var22 = {nRyXOBCwWr:alloc alloc 0,zCQceqYwwV:[alloc 1,alloc 2,alloc 4,alloc -1,alloc 3,alloc 5,alloc 6,alloc 7,alloc 1],GkqgnUGCYY:8,zvAoqKptYL:7};
        |  var23 = alloc 3;
        |  var24 = 8;
        |  var25 = 8;
        |  var26 = 1;
        |  var27 = [8,1,1,5,8,1];
        |  var6 = var20.waYAWcmcvX;
        |  if (input) {
        |    while ((var8 < var6)) {
        |      var26 = input;
        |      var19 = &var2;
        |      while ((var7 < var18)) {
        |        while (var4[4]) {
        |          output input;
        |          var9 = &var12;
        |          var16 = !-1;
        |          output input;
        |        }
        |        var7 = (var7 + 1);
        |      }
        |      var8 = (var8 + 1);
        |    }
        |  } else {}
        |  while ((var8 < var11)) {
        |    output var20.VIlTIzVhZK;
        |    while (input) {
        |      var4[2] = input;
        |      if (input) {
        |        var8 = (var26 * var0.PzLwkpeQto);
        |        var4[1] = input;
        |      } else {
        |        var10 = var12;
        |        if (var11) {} else {
        |          var24 = input;
        |        }
        |        if (var20.eQvClWeazG) {
        |          output var14.dbcqMEeaWa;
        |          output var7;
        |          output var0.KCckbJgOSE;
        |          var20 = var20;
        |        } else {
        |          var25 = input;
        |          var12 = var12;
        |        }
        |        var16 = var11;
        |      }
        |    }
        |    var8 = (var8 + 1);
        |  }
        |  var27[5] = input;
        |  return var21;
        |}
        |
        |""".stripMargin

    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program)
    val stateHistory = new StateHistory()
    val tree = new RandomPathSelectionStrategy(stateHistory)

    val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
    executor.run()

  }



  test("nasty summarization test2") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26,var27,var28;
        |  var0 = 6;
        |  var1 = {VIqsaowuJA:alloc 3,TnyLGnSOxx:alloc 3,ZgkFwzgsBL:[3,3,1,8,-1,0,4,0],BJvVQdKRjF:8};
        |  var2 = 6;
        |  var3 = 4;
        |  var4 = 7;
        |  var5 = alloc 1;
        |  var6 = 3;
        |  var7 = 1;
        |  var8 = 0;
        |  var9 = 0;
        |  var10 = {QTwXuVYccr:-1,ntrVtUEXHf:6,eKJGFskErJ:1,UhfDSCfUOU:0,haKQqwSTIf:alloc 3};
        |  var11 = alloc alloc 8;
        |  var12 = 8;
        |  var13 = alloc 2;
        |  var14 = 1;
        |  var15 = alloc 5;
        |  var16 = {dJbuOpNVgm:alloc alloc 8,PmOpoWYpwP:6};
        |  var17 = 8;
        |  var18 = 3;
        |  var19 = alloc 1;
        |  var20 = alloc alloc 0;
        |  var21 = {PVanMgsYKM:alloc 6};
        |  var22 = 8;
        |  var23 = -1;
        |  var24 = {uksndVaIfg:[alloc alloc 1,alloc alloc 5,alloc alloc 1,alloc alloc 6,alloc alloc 7,alloc alloc 2],ZHGbwtRofV:alloc alloc alloc 5,uaqRlOemMF:alloc 1,sMoRMjSOuN:alloc alloc alloc 8,MVhsPPLfBz:6};
        |  var25 = alloc 7;
        |  var26 = 8;
        |  var27 = 4;
        |  var28 = [3,-1,8,2,4,3,-1,7];
        |  var28[0] = input;
        |  if (input) {
        |    while (var23) {
        |      var28[3] = input;
        |      while ((var26 < var22)) {
        |        var26 = (var26 + 1);
        |      }
        |      if (var10.ntrVtUEXHf) {} else {}
        |    }
        |    while (input) {
        |      while ((var6 < var18)) {
        |        output input;
        |        var28[1] = 8;
        |        output 6;
        |        var6 = (var6 + 1);
        |      }
        |      var11 = &var5;
        |      while ((var27 < var12)) {
        |        while (!5) {}
        |        while ((var17 < var6)) {
        |          output input;
        |          output var27;
        |          output var10.eKJGFskErJ;
        |          output 9;
        |          var17 = (var17 + 1);
        |        }
        |        while (input) {}
        |        while ((var0 < var6)) {
        |          var12 = (1 + 5);
        |          output input;
        |          var0 = (var0 + 1);
        |        }
        |        var27 = (var27 + 1);
        |      }
        |    }
        |    while (input) {}
        |    while ((var9 < var14)) {
        |      while (var1.BJvVQdKRjF) {
        |        while ((input - (6 + 5))) {
        |          output var22;
        |        }
        |        while ((var22 < var12)) {
        |          var22 = (var22 + 1);
        |        }
        |      }
        |      output input;
        |      var9 = (var9 + 1);
        |    }
        |  } else {
        |    var13 = &var6;
        |  }
        |  if (2) {
        |    output input;
        |    while ((var17 < var7)) {
        |      var18 = (input - (input + var12));
        |      while ((var0 < var4)) {
        |        var0 = (var0 + 1);
        |      }
        |      var28[6] = var9;
        |      output var10.eKJGFskErJ;
        |      var17 = (var17 + 1);
        |    }
        |    output var10.ntrVtUEXHf;
        |  } else {
        |    while ((var14 < var4)) {
        |      while ((var23 < var17)) {
        |        while ((var6 < var26)) {
        |          var6 = (var6 + 1);
        |        }
        |        while ((var0 < var3)) {
        |          output 2;
        |          output !6;
        |          var22 = input;
        |          output var2;
        |          var0 = (var0 + 1);
        |        }
        |        while ((var26 < var17)) {
        |          output (9 * input);
        |          var6 = (4 / 1);
        |          var26 = (var26 + 1);
        |        }
        |        while ((var14 < var8)) {
        |          output var9;
        |          var2 = var10.eKJGFskErJ;
        |          output input;
        |          var18 = !8;
        |          var14 = (var14 + 1);
        |        }
        |        var23 = (var23 + 1);
        |      }
        |      while ((var7 < var26)) {
        |        var7 = (var7 + 1);
        |      }
        |      var14 = (var14 + 1);
        |    }
        |  }
        |  var28[2] = 0;
        |  while ((var6 < var12)) {
        |    var6 = (var6 + 1);
        |  }
        |  while ((var26 < var0)) {
        |    while (!input) {
        |      while ((var22 < var17)) {
        |        var22 = (var22 + 1);
        |      }
        |      while ((var18 < var26)) {
        |        if (var12) {} else {
        |          output input;
        |          output var24.MVhsPPLfBz;
        |          output (3 + (5 * ((input - var10.eKJGFskErJ) + input)));
        |          var19 = &var0;
        |        }
        |        while ((var4 < var26)) {
        |          output input;
        |          var4 = (var4 + 1);
        |        }
        |        while ((var8 < var18)) {
        |          output input;
        |          output input;
        |          var0 = input;
        |          var8 = (var8 + 1);
        |        }
        |        var18 = (var18 + 1);
        |      }
        |    }
        |    while ((var0 < var2)) {
        |      var28[0] = input;
        |      if (!input) {
        |        while (var16.PmOpoWYpwP) {
        |          var0 = 1;
        |        }
        |        while (!!0) {
        |          output var9;
        |          var9 = var9;
        |          output input;
        |          var9 = input;
        |        }
        |        while (var14) {}
        |        output (1 - 2);
        |      } else {
        |        while ((var12 < var27)) {
        |          output var4;
        |          output input;
        |          output input;
        |          var12 = (var12 + 1);
        |        }
        |        var28[0] = var10.eKJGFskErJ;
        |      }
        |      var0 = (var0 + 1);
        |    }
        |    if (var10.UhfDSCfUOU) {} else {
        |      var12 = 9;
        |    }
        |    var28[3] = !input;
        |    var26 = (var26 + 1);
        |  }
        |  while ((var7 < var23)) {
        |    var28[5] = var12;
        |    output input;
        |    while (4) {
        |      while ((var3 < var3)) {
        |        var3 = (var3 + 1);
        |      }
        |      while (var4) {}
        |      while ((var17 < var2)) {
        |        if (3) {} else {
        |          var22 = 6;
        |          output 0;
        |        }
        |        while ((var2 < var8)) {
        |          output !var6;
        |          var15 = &var17;
        |          var2 = (var2 + 1);
        |        }
        |        output !input;
        |        var17 = (var17 + 1);
        |      }
        |    }
        |    var7 = (var7 + 1);
        |  }
        |  return input;
        |}
        |
        |""".stripMargin

    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program)
    val stateHistory = new StateHistory()
    val tree = new RandomPathSelectionStrategy(stateHistory)

    val future = Future {
      val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
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



  test("nasty summarization test4") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16;
        |  var0 = {MPYAGeSjFk:0,dYQjpNhFtK:0,RSRmVdhnMG:0,ypdicEwDne:4,EmbFYjvEPp:4};
        |  var1 = 7;
        |  var2 = [6,0,7,5,3,6,7];
        |  var3 = alloc 8;
        |  var4 = [2,7,2,3,0,5,4,0];
        |  var5 = 1;
        |  var6 = alloc alloc 3;
        |  var7 = 7;
        |  var8 = {mvvTjDHumj:7,CilUnXXvuR:8,mEyQloGawX:1,qvFUnVanLe:8};
        |  var9 = 7;
        |  var10 = alloc [1,0,5,0,4,6,5,7];
        |  var11 = 1;
        |  var12 = {ByolHJlRxy:alloc 7,LjEosXUkCW:3,FfzUUOrTbW:3};
        |  var13 = [alloc -1,alloc 1,alloc 1,alloc 8,alloc 2,alloc 1,alloc 5];
        |  var14 = {IMbcMywnND:2};
        |  var15 = alloc -1;
        |  var16 = [0,6,6,4,8,8,3,0];
        |  var9 = var16[4];
        |  while ((var1 < var9)) {
        |    while ((var7 < var5)) {
        |      while (input) {
        |        while ((var7 < var9)) {
        |          var16[3] = !7;
        |          while ((var1 < var5)) {
        |            var1 = (var1 + 1);
        |          }
        |          while (var9) {
        |            while ((var9 < var11)) {
        |              output !var4[1];
        |              var6 = alloc alloc 4;
        |              var3 = alloc 0;
        |              output input;
        |              var9 = (var9 + 1);
        |            }
        |            output 3;
        |            while ((var7 < var9)) {
        |              var9 = 8;
        |              var7 = (var7 + 1);
        |            }
        |          }
        |          var7 = (var7 + 1);
        |        }
        |      }
        |      while ((var7 < var9)) {
        |        var11 = !(-1 + 6);
        |        var8 = var8;
        |        var16 = var4;
        |        var7 = (var7 + 1);
        |      }
        |      var7 = (var7 + 1);
        |    }
        |    while (var7) {
        |      while ((var7 < var5)) {
        |        while ((var5 < var1)) {
        |          while ((var5 < var9)) {
        |            while ((var7 < var7)) {
        |              var7 = (var7 + 1);
        |            }
        |            var2[5] = 3;
        |            var5 = (var5 + 1);
        |          }
        |          var13[0] = var3;
        |          while ((var1 < var1)) {
        |            output 7;
        |            while ((var7 < var9)) {
        |              var7 = (var7 + 1);
        |            }
        |            while ((var5 < var5)) {
        |              var12 = {ByolHJlRxy:alloc 4,LjEosXUkCW:7,FfzUUOrTbW:1};
        |              var8 = {mvvTjDHumj:3,CilUnXXvuR:0,mEyQloGawX:4,qvFUnVanLe:5};
        |              var5 = (var5 + 1);
        |            }
        |            var1 = (var1 + 1);
        |          }
        |          if ((2 * 8)) {
        |            if (-1) {
        |              output !(var8.qvFUnVanLe * !!var9);
        |              output var4[4];
        |            } else {
        |              var1 = 8;
        |              var13 = [alloc -1,alloc 0,alloc 0,alloc 7,alloc 7,alloc 2,alloc -1];
        |              var4 = [1,6,-1,3,3];
        |              var12 = {ByolHJlRxy:alloc 6,LjEosXUkCW:6,FfzUUOrTbW:8};
        |            }
        |            while ((var11 < var9)) {
        |              output (input + input);
        |              output !var4[4];
        |              var11 = (var11 + 1);
        |            }
        |          } else {
        |            while ((var1 < var7)) {
        |              var2 = [2,8,2,4,2,3,5];
        |              output !input;
        |              output input;
        |              var6 = alloc alloc 8;
        |              var1 = (var1 + 1);
        |            }
        |            while (0) {
        |              var16 = [6,3,-1,3,2,4,3,2];
        |              output !var11;
        |              output (var1 - (input - input));
        |              output var8.mvvTjDHumj;
        |            }
        |            while (2) {
        |              output input;
        |              var3 = alloc 4;
        |            }
        |          }
        |          var5 = (var5 + 1);
        |        }
        |        var7 = (var7 + 1);
        |      }
        |      output input;
        |      while ((var9 < var11)) {
        |        var9 = (var9 + 1);
        |      }
        |    }
        |    while ((var11 < var9)) {
        |      while ((var7 < var7)) {
        |        if (var2[5]) {
        |          while ((var7 < var5)) {
        |            while (0) {
        |              var5 = 5;
        |              var0 = {MPYAGeSjFk:0,dYQjpNhFtK:7,RSRmVdhnMG:0,ypdicEwDne:2,EmbFYjvEPp:6};
        |              output (var0.MPYAGeSjFk * input);
        |            }
        |            while ((var5 < var7)) {
        |              var6 = alloc alloc -1;
        |              var10 = alloc [8,2,1,0,5,1,6,0];
        |              output var2[6];
        |              var5 = (var5 + 1);
        |            }
        |            while ((var9 < var5)) {
        |              var7 = 2;
        |              var9 = (var9 + 1);
        |            }
        |            while ((var7 < var9)) {
        |              var7 = (var7 + 1);
        |            }
        |            var7 = (var7 + 1);
        |          }
        |          while ((4 + 5)) {
        |            var6 = alloc alloc 3;
        |            while ((var7 < var1)) {
        |              var7 = 0;
        |              var7 = (var7 + 1);
        |            }
        |            var2[0] = 4;
        |          }
        |        } else {
        |          var13 = var13;
        |          while ((var7 < var11)) {
        |            var7 = (var7 + 1);
        |          }
        |        }
        |        output input;
        |        while ((var11 < var7)) {
        |          while (input) {
        |            while ((var5 < var9)) {
        |              output input;
        |              var10 = alloc [0,4,1,1,6,7,2];
        |              var5 = (var5 + 1);
        |            }
        |            output 0;
        |            if (6) {
        |              var16 = [4,4,2,5,7,0,-1];
        |              output var2[4];
        |              output input;
        |              var10 = alloc [0,5,5,0,6,7,5,2,-1];
        |            } else {}
        |            while ((var5 < var5)) {
        |              var5 = 5;
        |              var5 = -1;
        |              var5 = (var5 + 1);
        |            }
        |          }
        |          var11 = (var11 + 1);
        |        }
        |        while ((var9 < var1)) {
        |          var9 = (var9 + 1);
        |        }
        |        var7 = (var7 + 1);
        |      }
        |      while ((var11 < var7)) {
        |        var11 = (var11 + 1);
        |      }
        |      var11 = (var11 + 1);
        |    }
        |    while ((var7 < var11)) {
        |      var7 = (var7 + 1);
        |    }
        |    var1 = (var1 + 1);
        |  }
        |  while ((var1 < var9)) {
        |    while ((var9 < var7)) {
        |      if (!var4[2]) {
        |        while ((var7 < var9)) {
        |          if (input) {
        |            while ((var5 < var7)) {
        |              output ((!var9 + (var11 - input)) + input);
        |              output input;
        |              var5 = (var5 + 1);
        |            }
        |            while ((var7 < var7)) {
        |              var0 = {MPYAGeSjFk:2,dYQjpNhFtK:5,RSRmVdhnMG:-1,ypdicEwDne:3,EmbFYjvEPp:2};
        |              var7 = (var7 + 1);
        |            }
        |            while ((var11 < var11)) {
        |              output !var2[0];
        |              var0 = {MPYAGeSjFk:-1,dYQjpNhFtK:6,RSRmVdhnMG:-1,ypdicEwDne:-1,EmbFYjvEPp:3};
        |              output (var11 + input);
        |              var2 = [7,2,4,5,6,2,7,3];
        |              var11 = (var11 + 1);
        |            }
        |            while ((var9 < var1)) {
        |              var11 = 7;
        |              output var8.CilUnXXvuR;
        |              var9 = (var9 + 1);
        |            }
        |          } else {}
        |          while ((var7 < var1)) {
        |            while ((var11 < var5)) {
        |              var7 = 1;
        |              var11 = (var11 + 1);
        |            }
        |            while ((var9 < var11)) {
        |              output input;
        |              var6 = alloc alloc 5;
        |              var0 = {MPYAGeSjFk:0,dYQjpNhFtK:0,RSRmVdhnMG:8,ypdicEwDne:1,EmbFYjvEPp:0};
        |              var9 = (var9 + 1);
        |            }
        |            while ((var1 < var9)) {
        |              output input;
        |              var4 = [1,0,4,8,4,2,0];
        |              output (var16[5] + var0.RSRmVdhnMG);
        |              var1 = (var1 + 1);
        |            }
        |            var7 = (var7 + 1);
        |          }
        |          var4[7] = [5,4,6,3,0,2][3];
        |          var7 = (var7 + 1);
        |        }
        |        while ((var11 < var9)) {
        |          while ((var11 < var5)) {
        |            while ((var1 < var1)) {
        |              output !var4[2];
        |              var13 = [alloc 8,alloc 7,alloc 5,alloc 3,alloc 8];
        |              var14 = {IMbcMywnND:4};
        |              var1 = (var1 + 1);
        |            }
        |            var2[0] = 2;
        |            var11 = (var11 + 1);
        |          }
        |          var4[5] = var1;
        |          var11 = (var11 + 1);
        |        }
        |        while ((var5 < var1)) {
        |          var5 = (var5 + 1);
        |        }
        |        while ((var9 < var11)) {
        |          while ((var5 < var1)) {
        |            while ((var1 < var11)) {
        |              var11 = -1;
        |              var0 = {MPYAGeSjFk:5,dYQjpNhFtK:1,RSRmVdhnMG:5,ypdicEwDne:2,EmbFYjvEPp:1};
        |              var7 = 0;
        |              var6 = alloc alloc 0;
        |              var1 = (var1 + 1);
        |            }
        |            var1 = 0;
        |            var3 = alloc 7;
        |            var5 = (var5 + 1);
        |          }
        |          while ((var1 < var11)) {
        |            var1 = (var1 + 1);
        |          }
        |          var2 = var2;
        |          var9 = (var9 + 1);
        |        }
        |      } else {
        |        while ((var5 < var5)) {
        |          while ((var7 < var1)) {
        |            while (-1) {
        |              var4 = [6,6,0,6,0,2];
        |            }
        |            var7 = (var7 + 1);
        |          }
        |          if (var0.EmbFYjvEPp) {
        |            while ((var7 < var9)) {
        |              output var7;
        |              var8 = {mvvTjDHumj:-1,CilUnXXvuR:8,mEyQloGawX:6,qvFUnVanLe:2};
        |              var7 = (var7 + 1);
        |            }
        |            while (0) {
        |              var2 = [3,3,1,3,5,8,0];
        |              var4 = [0,7,7,2,7,4,6,2,6];
        |            }
        |          } else {
        |            while ((var9 < var9)) {
        |              var12 = {ByolHJlRxy:alloc 0,LjEosXUkCW:5,FfzUUOrTbW:5};
        |              output input;
        |              var9 = (var9 + 1);
        |            }
        |            output 2;
        |          }
        |          output var5;
        |          while (var0.MPYAGeSjFk) {}
        |          var5 = (var5 + 1);
        |        }
        |      }
        |      var9 = (var9 + 1);
        |    }
        |    while ((var7 < var7)) {
        |      while ((var1 < var9)) {
        |        var1 = (var1 + 1);
        |      }
        |      while (var0.EmbFYjvEPp) {
        |        while (!!7) {}
        |        while ((var5 < var9)) {
        |          while ((var9 < var9)) {
        |            while ((var9 < var11)) {
        |              output var7;
        |              var9 = (var9 + 1);
        |            }
        |            if (6) {
        |              var5 = 1;
        |              var2 = [6,4,6,5,0,8,-1];
        |            } else {
        |              output (!input + input);
        |              output (input * input);
        |            }
        |            while ((var7 < var7)) {
        |              var10 = alloc [1,4,-1,4,6,-1,3,3];
        |              var7 = (var7 + 1);
        |            }
        |            var9 = (var9 + 1);
        |          }
        |          var5 = (var5 + 1);
        |        }
        |        while ((var7 < var5)) {
        |          output !4;
        |          while ((var5 < var7)) {
        |            if (-1) {} else {
        |              var9 = 4;
        |              var1 = 7;
        |            }
        |            while ((var7 < var5)) {
        |              var11 = 6;
        |              var15 = alloc 5;
        |              var0 = {MPYAGeSjFk:8,dYQjpNhFtK:2,RSRmVdhnMG:6,ypdicEwDne:6,EmbFYjvEPp:1};
        |              output input;
        |              var7 = (var7 + 1);
        |            }
        |            var1 = 2;
        |            var2[1] = 6;
        |            var5 = (var5 + 1);
        |          }
        |          var7 = (var7 + 1);
        |        }
        |      }
        |      var16[3] = input;
        |      while ((var5 < var9)) {
        |        while ((var11 < var11)) {
        |          var16[6] = var1;
        |          var11 = (var11 + 1);
        |        }
        |        var5 = (var5 + 1);
        |      }
        |      var7 = (var7 + 1);
        |    }
        |    var1 = (var1 + 1);
        |  }
        |  while ((var1 - (input - var2[6]))) {
        |    while ((var1 < var5)) {
        |      var16[1] = (!input + !var9);
        |      var6 = var6;
        |      while ((var5 < var1)) {
        |        while ((var11 < var1)) {
        |          var11 = (var11 + 1);
        |        }
        |        while ((var9 < var9)) {
        |          while ((5 * 3)) {
        |            while ((var5 < var1)) {
        |              output input;
        |              var5 = (var5 + 1);
        |            }
        |            if (3) {} else {}
        |            while (5) {
        |              var4 = [3,2,3,6,-1,4];
        |            }
        |          }
        |          while ((var1 < var5)) {
        |            while ((var1 < var11)) {
        |              var1 = (var1 + 1);
        |            }
        |            var1 = (var1 + 1);
        |          }
        |          var9 = (var9 + 1);
        |        }
        |        while ((var9 < var5)) {
        |          while ((var5 < var7)) {
        |            while (5) {
        |              var11 = 2;
        |              output input;
        |              var9 = 5;
        |            }
        |            while ((var9 < var9)) {
        |              var9 = (var9 + 1);
        |            }
        |            var5 = (var5 + 1);
        |          }
        |          var3 = &var5;
        |          var9 = (var9 + 1);
        |        }
        |        var6 = &var3;
        |        var5 = (var5 + 1);
        |      }
        |      var1 = (var1 + 1);
        |    }
        |    while ((var11 < var9)) {
        |      var11 = (var11 + 1);
        |    }
        |  }
        |  var0 = var0;
        |  var16[0] = var5;
        |  while (var11) {}
        |  while ((var9 < var11)) {
        |    while ((var9 < var9)) {
        |      while ((var11 < var9)) {
        |        output var14.IMbcMywnND;
        |        while ((var11 < var9)) {
        |          while ((var7 < var11)) {
        |            while (4) {
        |              output (input * !(!var5 - var4[2]));
        |              var3 = alloc 8;
        |              var10 = alloc [8,3,4,2,4,7,7];
        |            }
        |            while (1) {
        |              output input;
        |              output var0.ypdicEwDne;
        |            }
        |            while ((var1 < var1)) {
        |              var1 = (var1 + 1);
        |            }
        |            while (1) {
        |              var14 = {IMbcMywnND:0};
        |              output !var7;
        |              var7 = 1;
        |              output !input;
        |            }
        |            var7 = (var7 + 1);
        |          }
        |          var11 = (var11 + 1);
        |        }
        |        var11 = (var11 + 1);
        |      }
        |      while ((var5 < var9)) {
        |        var16[4] = input;
        |        while ((var1 < var1)) {
        |          while ((var7 < var11)) {
        |            while ((var7 < var9)) {
        |              output var2[3];
        |              var4 = [3,3,8,8,6];
        |              var9 = -1;
        |              var7 = (var7 + 1);
        |            }
        |            var4[3] = 0;
        |            var7 = (var7 + 1);
        |          }
        |          var1 = (var1 + 1);
        |        }
        |        while ((var5 < var5)) {
        |          while ((var9 < var9)) {
        |            while ((var11 < var11)) {
        |              var8 = {mvvTjDHumj:-1,CilUnXXvuR:6,mEyQloGawX:-1,qvFUnVanLe:8};
        |              var14 = {IMbcMywnND:1};
        |              var9 = 2;
        |              var11 = (var11 + 1);
        |            }
        |            while ((var9 < var11)) {
        |              var9 = (var9 + 1);
        |            }
        |            while ((var9 < var11)) {
        |              var2 = [8,0,4,1,1];
        |              output !var8.qvFUnVanLe;
        |              var3 = alloc 8;
        |              var9 = (var9 + 1);
        |            }
        |            while (-1) {
        |              output !var7;
        |              var5 = 7;
        |            }
        |            var9 = (var9 + 1);
        |          }
        |          if (input) {
        |            while (3) {
        |              output input;
        |              var5 = 0;
        |              output input;
        |            }
        |            while (1) {
        |              var5 = 6;
        |              output !input;
        |              output (input - !var5);
        |              output input;
        |            }
        |            var4[3] = 0;
        |          } else {
        |            while ((var7 < var9)) {
        |              var7 = (var7 + 1);
        |            }
        |            while (5) {
        |              var16 = [1,8,3,6,1,5,-1,2];
        |              output ((input + (var1 + var7)) - (var16[0] + input));
        |              var12 = {ByolHJlRxy:alloc 2,LjEosXUkCW:1,FfzUUOrTbW:7};
        |              var14 = {IMbcMywnND:5};
        |            }
        |          }
        |          var5 = (var5 + 1);
        |        }
        |        var12 = var12;
        |        var5 = (var5 + 1);
        |      }
        |      while ((var9 < var9)) {
        |        while (input) {}
        |        output var4[6];
        |        while ((var9 < var5)) {
        |          while ((var1 < var9)) {
        |            var1 = (var1 + 1);
        |          }
        |          while ((var11 < var11)) {
        |            while (0) {
        |              var15 = alloc 8;
        |              output var0.EmbFYjvEPp;
        |              output var11;
        |              output input;
        |            }
        |            output 2;
        |            var11 = (var11 + 1);
        |          }
        |          var0 = var0;
        |          var9 = (var9 + 1);
        |        }
        |        var9 = (var9 + 1);
        |      }
        |      while ((var1 < var1)) {
        |        while ((var7 < var5)) {
        |          while (!0) {}
        |          while (!4) {
        |            while ((var7 < var7)) {
        |              output input;
        |              var0 = {MPYAGeSjFk:7,dYQjpNhFtK:2,RSRmVdhnMG:4,ypdicEwDne:0,EmbFYjvEPp:3};
        |              var10 = alloc [0,7,1,0,5,2];
        |              var13 = [alloc 2,alloc 2,alloc 7,alloc -1,alloc 7,alloc 4,alloc 3,alloc 2];
        |              var7 = (var7 + 1);
        |            }
        |          }
        |          var7 = (var7 + 1);
        |        }
        |        var1 = (var1 + 1);
        |      }
        |      var9 = (var9 + 1);
        |    }
        |    var9 = (var9 + 1);
        |  }
        |  return (var12.LjEosXUkCW + input);
        |}
        |
        |""".stripMargin

    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program)
    val stateHistory = new StateHistory()
    val tree = new RandomPathSelectionStrategy(stateHistory)

    val future = Future {
      val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
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


  test("nasty summarization test5") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21;
        |  var0 = -1;
        |  var1 = 1;
        |  var2 = alloc 8;
        |  var3 = 7;
        |  var4 = 1;
        |  var5 = alloc 5;
        |  var6 = alloc 5;
        |  var7 = 3;
        |  var8 = [8,4,5,5,8,0,1,4,6];
        |  var9 = {OWLLOauFHj:alloc 3,UvgFHmcwmB:alloc alloc 3,LvMFFkUQmf:0};
        |  var10 = {vCNqPeruCi:6,IXaVgQimeE:6,bWRyAXYiIf:3};
        |  var11 = 5;
        |  var12 = alloc 7;
        |  var13 = 5;
        |  var14 = 6;
        |  var15 = {cVpzpMRNpn:4,GeVkvIOfCZ:alloc 4,lnKuUWuyyP:alloc -1,cPrWvFubKO:1};
        |  var16 = alloc alloc 3;
        |  var17 = 7;
        |  var18 = 3;
        |  var19 = 7;
        |  var20 = 6;
        |  var21 = [2,2,1,8,1];
        |  while ((var11 < var20)) {
        |    while ((var20 < var4)) {
        |      while ((var4 < var13)) {
        |        if (input) {
        |          while ((var7 < var4)) {
        |            while (-1) {
        |              output input;
        |              var19 = 8;
        |              var12 = alloc 1;
        |            }
        |            var7 = (var7 + 1);
        |          }
        |          while ((var14 < var11)) {
        |            while ((var20 < var7)) {
        |              var18 = 4;
        |              var11 = 1;
        |              var17 = 2;
        |              var9 = {OWLLOauFHj:alloc 2,UvgFHmcwmB:alloc alloc -1,LvMFFkUQmf:4};
        |              var20 = (var20 + 1);
        |            }
        |            while ((var20 < var1)) {
        |              var19 = 3;
        |              var13 = 4;
        |              output var9.LvMFFkUQmf;
        |              var20 = (var20 + 1);
        |            }
        |            while ((var17 < var18)) {
        |              var0 = 2;
        |              var0 = 1;
        |              var17 = (var17 + 1);
        |            }
        |            var14 = (var14 + 1);
        |          }
        |          while (input) {
        |            var21[1] = 0;
        |            var10 = {vCNqPeruCi:6,IXaVgQimeE:8,bWRyAXYiIf:4};
        |            while (2) {
        |              output input;
        |              output var18;
        |            }
        |            while ((var4 < var18)) {
        |              var4 = (var4 + 1);
        |            }
        |          }
        |          while ((var11 < var0)) {
        |            while ((var3 < var20)) {
        |              var18 = 0;
        |              output !input;
        |              var19 = 4;
        |              output var0;
        |              var3 = (var3 + 1);
        |            }
        |            while ((var0 < var13)) {
        |              var1 = 6;
        |              output input;
        |              var0 = (var0 + 1);
        |            }
        |            while ((var7 < var18)) {
        |              var12 = alloc 6;
        |              output var15.cVpzpMRNpn;
        |              var16 = alloc alloc 3;
        |              output (input * input);
        |              var7 = (var7 + 1);
        |            }
        |            var11 = (var11 + 1);
        |          }
        |        } else {}
        |        var4 = (var4 + 1);
        |      }
        |      while ((([8,6,2,5,0,2,4][5] - input) + !input)) {
        |        while ((var13 < var13)) {
        |          var13 = (var13 + 1);
        |        }
        |        while ((var0 < var18)) {
        |          while ((var20 < var7)) {
        |            while (1) {
        |              var0 = 7;
        |              output var7;
        |              output input;
        |              output var14;
        |            }
        |            var20 = (var20 + 1);
        |          }
        |          output var0;
        |          if (var13) {
        |            var21[1] = 8;
        |            while ((var20 < var11)) {
        |              var20 = (var20 + 1);
        |            }
        |            if (5) {
        |              var4 = 7;
        |              output input;
        |              var15 = {cVpzpMRNpn:0,GeVkvIOfCZ:alloc 3,lnKuUWuyyP:alloc 2,cPrWvFubKO:-1};
        |            } else {
        |              output var21[0];
        |              var2 = alloc -1;
        |              var12 = alloc 4;
        |              output (var21[2] - var20);
        |            }
        |          } else {}
        |          while ((var18 < var4)) {
        |            while ((var13 < var7)) {
        |              var3 = 8;
        |              output var8[2];
        |              output !var7;
        |              var13 = (var13 + 1);
        |            }
        |            output 3;
        |            var18 = (var18 + 1);
        |          }
        |          var0 = (var0 + 1);
        |        }
        |        var8[5] = input;
        |      }
        |      var20 = (var20 + 1);
        |    }
        |    if (input) {
        |      output !var8[4];
        |      while ((var4 < var7)) {
        |        var9 = var9;
        |        var0 = var21[1];
        |        while ((var7 < var7)) {
        |          while ((var17 < var17)) {
        |            var17 = (var17 + 1);
        |          }
        |          while ((var3 < var17)) {
        |            var3 = (var3 + 1);
        |          }
        |          while ((var1 < var11)) {
        |            var8[7] = 5;
        |            var1 = (var1 + 1);
        |          }
        |          while ((var7 < var0)) {
        |            while ((var18 < var1)) {
        |              output var10.vCNqPeruCi;
        |              output ((input - var19) * var21[1]);
        |              output input;
        |              var18 = (var18 + 1);
        |            }
        |            while ((var0 < var11)) {
        |              var5 = alloc 7;
        |              output var10.vCNqPeruCi;
        |              var1 = 3;
        |              output input;
        |              var0 = (var0 + 1);
        |            }
        |            while ((var14 < var0)) {
        |              output ((var21[1] - !var21[1]) + var18);
        |              var14 = (var14 + 1);
        |            }
        |            var7 = (var7 + 1);
        |          }
        |          var7 = (var7 + 1);
        |        }
        |        var4 = (var4 + 1);
        |      }
        |    } else {
        |      output input;
        |      var21[0] = var17;
        |    }
        |    var11 = (var11 + 1);
        |  }
        |  while ((var4 < var18)) {
        |    while ((var0 < var17)) {
        |      var0 = (var0 + 1);
        |    }
        |    while (!(input + var15.cPrWvFubKO)) {
        |      while ((var3 < var0)) {
        |        var8[6] = var15.cVpzpMRNpn;
        |        while ((var11 < var19)) {
        |          while (input) {
        |            output 2;
        |            var8 = [7,0,4,7,4,1];
        |            while ((var1 < var4)) {
        |              var1 = (var1 + 1);
        |            }
        |          }
        |          var11 = (var11 + 1);
        |        }
        |        var3 = (var3 + 1);
        |      }
        |      while ((var0 < var19)) {
        |        var0 = (var0 + 1);
        |      }
        |    }
        |    var8[7] = var3;
        |    var4 = (var4 + 1);
        |  }
        |  while (var10.IXaVgQimeE) {
        |    var8[1] = input;
        |    while (input) {
        |      var16 = &var6;
        |      while ((var13 < var18)) {
        |        if (input) {} else {}
        |        while ((var0 < var7)) {
        |          while ((var19 < var17)) {
        |            while (7) {
        |              output input;
        |              output (var8[6] * var13);
        |              output input;
        |              var11 = 7;
        |            }
        |            while ((var13 < var0)) {
        |              var13 = (var13 + 1);
        |            }
        |            var19 = (var19 + 1);
        |          }
        |          var0 = (var0 + 1);
        |        }
        |        while ((var3 < var1)) {
        |          while (!1) {}
        |          while ((var11 < var14)) {
        |            while ((var13 < var11)) {
        |              var13 = (var13 + 1);
        |            }
        |            while (8) {
        |              output var9.LvMFFkUQmf;
        |              output var18;
        |            }
        |            while (4) {
        |              output var8[2];
        |              var11 = 6;
        |            }
        |            var8 = [-1,8,7,3,-1,8];
        |            var11 = (var11 + 1);
        |          }
        |          while ((3 * 3)) {
        |            while ((var4 < var13)) {
        |              var14 = 3;
        |              output !var21[4];
        |              var12 = alloc 7;
        |              var10 = {vCNqPeruCi:2,IXaVgQimeE:7,bWRyAXYiIf:5};
        |              var4 = (var4 + 1);
        |            }
        |          }
        |          var3 = (var3 + 1);
        |        }
        |        var13 = (var13 + 1);
        |      }
        |    }
        |  }
        |  while ((var20 < var7)) {
        |    var11 = var21[1];
        |    while ((var1 < var0)) {
        |      var1 = (var1 + 1);
        |    }
        |    var20 = (var20 + 1);
        |  }
        |  while ((var11 < var11)) {
        |    while (!var17) {
        |      while ((var4 < var20)) {
        |        while ((var7 < var18)) {
        |          if (input) {
        |            while ((var0 < var19)) {
        |              output var11;
        |              var0 = (var0 + 1);
        |            }
        |            while ((var11 < var18)) {
        |              var11 = 0;
        |              var0 = 0;
        |              output (var21[3] + input);
        |              var11 = (var11 + 1);
        |            }
        |          } else {}
        |          var7 = (var7 + 1);
        |        }
        |        if (var8[8]) {
        |          while ((var14 < var1)) {
        |            var14 = (var14 + 1);
        |          }
        |          while ((var14 < var17)) {
        |            var14 = (var14 + 1);
        |          }
        |          output input;
        |        } else {
        |          while ((var13 < var4)) {
        |            while ((var17 < var1)) {
        |              var16 = alloc alloc 7;
        |              output var8[4];
        |              var13 = 0;
        |              var10 = {vCNqPeruCi:5,IXaVgQimeE:0,bWRyAXYiIf:5};
        |              var17 = (var17 + 1);
        |            }
        |            var12 = alloc 7;
        |            var13 = (var13 + 1);
        |          }
        |        }
        |        while (!input) {
        |          while ((var14 < var17)) {
        |            while ((var20 < var7)) {
        |              var0 = 4;
        |              output !input;
        |              var20 = (var20 + 1);
        |            }
        |            while ((var7 < var4)) {
        |              var0 = 2;
        |              output var10.vCNqPeruCi;
        |              output input;
        |              var7 = (var7 + 1);
        |            }
        |            var14 = (var14 + 1);
        |          }
        |          while ((var0 < var7)) {
        |            while ((var19 < var0)) {
        |              output var0;
        |              var19 = (var19 + 1);
        |            }
        |            while ((var1 < var17)) {
        |              var17 = 7;
        |              var1 = (var1 + 1);
        |            }
        |            var0 = (var0 + 1);
        |          }
        |          output var10.bWRyAXYiIf;
        |          while ((var18 < var20)) {
        |            if (6) {
        |              output input;
        |            } else {
        |              output !var10.vCNqPeruCi;
        |              output (var8[1] - var21[4]);
        |              output input;
        |            }
        |            while ((var1 < var13)) {
        |              output !input;
        |              output var9.LvMFFkUQmf;
        |              var1 = (var1 + 1);
        |            }
        |            while ((var20 < var20)) {
        |              var6 = alloc 1;
        |              var20 = (var20 + 1);
        |            }
        |            var18 = (var18 + 1);
        |          }
        |        }
        |        var4 = (var4 + 1);
        |      }
        |      while ((var17 < var11)) {
        |        output ((8 * 5) * var9.LvMFFkUQmf);
        |        while ((var0 < var1)) {
        |          output [2,-1,3,-1,7,8][2];
        |          var8[1] = var10.IXaVgQimeE;
        |          var0 = (var0 + 1);
        |        }
        |        var17 = (var17 + 1);
        |      }
        |    }
        |    var10 = var10;
        |    var11 = (var11 + 1);
        |  }
        |  while ((var20 < var1)) {
        |    while ((var11 < var1)) {
        |      if (input) {
        |        while ((var7 < var20)) {
        |          while ((var20 < var14)) {
        |            while ((var0 < var3)) {
        |              output input;
        |              var0 = (var0 + 1);
        |            }
        |            var20 = (var20 + 1);
        |          }
        |          var7 = (var7 + 1);
        |        }
        |        while ((var11 < var19)) {
        |          output input;
        |          while ((var18 < var19)) {
        |            while ((var19 < var13)) {
        |              output input;
        |              var17 = 1;
        |              var9 = {OWLLOauFHj:alloc 5,UvgFHmcwmB:alloc alloc 5,LvMFFkUQmf:4};
        |              output !var21[3];
        |              var19 = (var19 + 1);
        |            }
        |            var18 = (var18 + 1);
        |          }
        |          if (input) {} else {
        |            while (6) {
        |              var12 = alloc 0;
        |              output var9.LvMFFkUQmf;
        |              output input;
        |              var5 = alloc 3;
        |            }
        |            output 8;
        |          }
        |          var11 = (var11 + 1);
        |        }
        |      } else {
        |        while (input) {
        |          while ((var4 < var3)) {
        |            var4 = (var4 + 1);
        |          }
        |          var21[4] = [6,3,8,8,2][2];
        |        }
        |      }
        |      while ((var8[0] * input)) {}
        |      var11 = (var11 + 1);
        |    }
        |    while ((var19 < var14)) {
        |      while ((var14 < var13)) {
        |        while ((var13 < var3)) {
        |          var13 = (var13 + 1);
        |        }
        |        while ((var18 < var14)) {
        |          output [7,5,-1,3,7,1][0];
        |          var18 = (var18 + 1);
        |        }
        |        var14 = (var14 + 1);
        |      }
        |      var15 = var15;
        |      while (input) {
        |        while ((var20 < var19)) {
        |          while (!0) {
        |            while ((var3 < var13)) {
        |              var3 = (var3 + 1);
        |            }
        |            while (0) {
        |              output var10.IXaVgQimeE;
        |              output input;
        |              output input;
        |              var19 = 4;
        |            }
        |            var8[8] = 7;
        |            while (7) {
        |              output var21[0];
        |              var6 = alloc -1;
        |              output !var10.IXaVgQimeE;
        |            }
        |          }
        |          while ([1,5,8,8,8,4,6][2]) {
        |            while ((var7 < var18)) {
        |              output input;
        |              output (var15.cVpzpMRNpn * (input - var18));
        |              var7 = (var7 + 1);
        |            }
        |            while ((var14 < var3)) {
        |              var16 = alloc alloc 2;
        |              output var15.cPrWvFubKO;
        |              var14 = (var14 + 1);
        |            }
        |            while ((var14 < var20)) {
        |              output !var8[6];
        |              var9 = {OWLLOauFHj:alloc 5,UvgFHmcwmB:alloc alloc 3,LvMFFkUQmf:2};
        |              output !(var10.bWRyAXYiIf + var14);
        |              var14 = 4;
        |              var14 = (var14 + 1);
        |            }
        |            while ((var7 < var20)) {
        |              output var21[4];
        |              var7 = (var7 + 1);
        |            }
        |          }
        |          if (input) {
        |            var8[4] = 2;
        |          } else {
        |            while ((var14 < var13)) {
        |              output var4;
        |              output input;
        |              var16 = alloc alloc 3;
        |              output !var4;
        |              var14 = (var14 + 1);
        |            }
        |            output 8;
        |          }
        |          var20 = (var20 + 1);
        |        }
        |        while (input) {
        |          while (var15.cPrWvFubKO) {}
        |          if ((4 + 0)) {
        |            while ((var14 < var1)) {
        |              var14 = (var14 + 1);
        |            }
        |            while ((var14 < var13)) {
        |              output input;
        |              output var9.LvMFFkUQmf;
        |              var13 = -1;
        |              var14 = (var14 + 1);
        |            }
        |            while ((var17 < var19)) {
        |              output input;
        |              var17 = (var17 + 1);
        |            }
        |          } else {
        |            var8[2] = 7;
        |          }
        |          while ((var7 < var11)) {
        |            while ((var18 < var17)) {
        |              output !var8[3];
        |              var11 = 7;
        |              var18 = (var18 + 1);
        |            }
        |            while ((var0 < var20)) {
        |              var17 = 8;
        |              var18 = 7;
        |              output (var10.vCNqPeruCi + !var21[3]);
        |              output input;
        |              var0 = (var0 + 1);
        |            }
        |            if (7) {
        |              output var14;
        |            } else {
        |              output var19;
        |              output input;
        |            }
        |            var7 = (var7 + 1);
        |          }
        |        }
        |        while ((var13 < var0)) {
        |          while ((var1 < var17)) {
        |            while ((var3 < var0)) {
        |              var16 = alloc alloc 5;
        |              output input;
        |              var14 = 5;
        |              var3 = (var3 + 1);
        |            }
        |            while ((var4 < var4)) {
        |              output input;
        |              var4 = (var4 + 1);
        |            }
        |            var1 = (var1 + 1);
        |          }
        |          var21[1] = (2 * 1);
        |          output [6,1,7,2,6,8,3,0,3][0];
        |          while ((var19 < var4)) {
        |            var19 = (var19 + 1);
        |          }
        |          var13 = (var13 + 1);
        |        }
        |      }
        |      var19 = (var19 + 1);
        |    }
        |    var20 = (var20 + 1);
        |  }
        |  while ((var13 < var18)) {
        |    while (input) {
        |      var21[3] = !input;
        |    }
        |    if (var8[8]) {} else {}
        |    while ((var13 < var7)) {
        |      var14 = (var15.cPrWvFubKO - var21[0]);
        |      while ((var20 < var7)) {
        |        var20 = (var20 + 1);
        |      }
        |      var13 = (var13 + 1);
        |    }
        |    var13 = (var13 + 1);
        |  }
        |  while ((var4 < var13)) {
        |    var1 = !(input - input);
        |    while ((var20 < var13)) {
        |      while ((var0 < var20)) {
        |        while ((var11 < var13)) {
        |          while ((var11 < var17)) {
        |            if (1) {
        |              output var8[8];
        |              output var15.cVpzpMRNpn;
        |            } else {
        |              output var0;
        |              output !input;
        |              output input;
        |              output input;
        |            }
        |            var21[4] = 2;
        |            var17 = 4;
        |            var11 = (var11 + 1);
        |          }
        |          while ((var20 < var18)) {
        |            while (8) {}
        |            var20 = (var20 + 1);
        |          }
        |          output input;
        |          var11 = (var11 + 1);
        |        }
        |        if (!input) {
        |          var21[0] = input;
        |          while (input) {
        |            output -1;
        |            while ((var17 < var17)) {
        |              var5 = alloc 1;
        |              var21 = [7,2,4,1,1];
        |              output (input + var8[1]);
        |              var17 = (var17 + 1);
        |            }
        |            while ((var13 < var20)) {
        |              var13 = (var13 + 1);
        |            }
        |          }
        |          while ((var13 < var20)) {
        |            while ((var4 < var3)) {
        |              var4 = (var4 + 1);
        |            }
        |            var13 = (var13 + 1);
        |          }
        |        } else {
        |          while ((var13 < var17)) {
        |            output 0;
        |            output -1;
        |            while ((var18 < var3)) {
        |              output input;
        |              var18 = (var18 + 1);
        |            }
        |            while ((var1 < var7)) {
        |              var13 = 8;
        |              output (var8[3] - !(input * var21[0]));
        |              output !var13;
        |              var1 = (var1 + 1);
        |            }
        |            var13 = (var13 + 1);
        |          }
        |        }
        |        var0 = (var0 + 1);
        |      }
        |      if ((input - var10.bWRyAXYiIf)) {
        |        while ((var11 < var20)) {
        |          while (var11) {}
        |          var11 = (var11 + 1);
        |        }
        |        while ((var18 < var18)) {
        |          while ((var14 < var17)) {
        |            var14 = (var14 + 1);
        |          }
        |          while ((var4 < var14)) {
        |            while (2) {
        |              output !var8[1];
        |              var10 = {vCNqPeruCi:6,IXaVgQimeE:8,bWRyAXYiIf:3};
        |            }
        |            while ((var11 < var3)) {
        |              var6 = alloc 5;
        |              var11 = (var11 + 1);
        |            }
        |            var4 = (var4 + 1);
        |          }
        |          var8[2] = var17;
        |          var18 = (var18 + 1);
        |        }
        |        while ((var0 < var20)) {
        |          var1 = input;
        |          output [2,5,5,-1,1,4][2];
        |          output [8,8,4,4,6,0,-1,3,5][3];
        |          var0 = (var0 + 1);
        |        }
        |      } else {
        |        while ((var7 < var13)) {
        |          while ([7,3,4,8,8,4][2]) {
        |            while ((var7 < var7)) {
        |              output !input;
        |              output (var8[0] + (!var10.IXaVgQimeE + input));
        |              var8 = [-1,7,4,7,7,2];
        |              var7 = (var7 + 1);
        |            }
        |          }
        |          while ((var20 < var4)) {
        |            while ((var20 < var3)) {
        |              output input;
        |              var20 = (var20 + 1);
        |            }
        |            var20 = (var20 + 1);
        |          }
        |          var7 = (var7 + 1);
        |        }
        |        while ((var1 < var7)) {
        |          while ((var20 < var7)) {
        |            while ((var3 < var7)) {
        |              var3 = (var3 + 1);
        |            }
        |            var20 = (var20 + 1);
        |          }
        |          while ((var17 < var19)) {
        |            var17 = (var17 + 1);
        |          }
        |          var1 = (var1 + 1);
        |        }
        |        while ((var3 < var18)) {
        |          while ((var7 < var19)) {
        |            while ((var13 < var11)) {
        |              output !var10.vCNqPeruCi;
        |              output var9.LvMFFkUQmf;
        |              var13 = (var13 + 1);
        |            }
        |            while ((var0 < var1)) {
        |              var1 = 0;
        |              var0 = (var0 + 1);
        |            }
        |            while ((var11 < var0)) {
        |              output input;
        |              var11 = (var11 + 1);
        |            }
        |            while (7) {
        |              var7 = -1;
        |              var13 = 3;
        |            }
        |            var7 = (var7 + 1);
        |          }
        |          var3 = (var3 + 1);
        |        }
        |      }
        |      while ((var17 < var19)) {
        |        var8[2] = var10.IXaVgQimeE;
        |        while ((var3 < var4)) {
        |          while ((var14 < var19)) {
        |            while ((var7 < var11)) {
        |              output var8[7];
        |              output input;
        |              var3 = 6;
        |              var7 = (var7 + 1);
        |            }
        |            while ((var7 < var4)) {
        |              var7 = (var7 + 1);
        |            }
        |            while ((var20 < var0)) {
        |              output !(input - var10.IXaVgQimeE);
        |              output input;
        |              var20 = (var20 + 1);
        |            }
        |            while ((var0 < var13)) {
        |              var2 = alloc -1;
        |              var10 = {vCNqPeruCi:8,IXaVgQimeE:4,bWRyAXYiIf:2};
        |              var18 = -1;
        |              var19 = 6;
        |              var0 = (var0 + 1);
        |            }
        |            var14 = (var14 + 1);
        |          }
        |          var3 = (var3 + 1);
        |        }
        |        while ((var13 < var3)) {
        |          var13 = (var13 + 1);
        |        }
        |        var17 = (var17 + 1);
        |      }
        |      output var10.IXaVgQimeE;
        |      var20 = (var20 + 1);
        |    }
        |    var4 = (var4 + 1);
        |  }
        |  return ((input - [2,1,8,6,0][3]) - var15.cPrWvFubKO);
        |}
        |
        |""".stripMargin

    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program)
    val stateHistory = new StateHistory()
    val tree = new RandomPathSelectionStrategy(stateHistory)

    val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
    executor.run()

  }


  test("nasty summarization test6") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26,var27,var28;
        |  var0 = 7;
        |  var1 = 6;
        |  var2 = {TRnFrOfoUr:alloc 2,fPXAqbxGaG:[6,7,5,0,8,8,7]};
        |  var3 = alloc 5;
        |  var4 = 3;
        |  var5 = alloc alloc 8;
        |  var6 = 2;
        |  var7 = {UYfmqvszXt:alloc 2,weYgbIPPem:alloc alloc 2};
        |  var8 = [7,2,7,0,6];
        |  var9 = {UwWXKhmlCg:alloc alloc -1,wSjliGVHIB:5,wcHGCoeKad:alloc alloc 1};
        |  var10 = alloc 7;
        |  var11 = 1;
        |  var12 = alloc 0;
        |  var13 = {gjFdRoDpea:1,YbzoIttZWL:6};
        |  var14 = {euUsrmQVbe:alloc alloc alloc 5,MlBCRWIMPG:3};
        |  var15 = 4;
        |  var16 = -1;
        |  var17 = 0;
        |  var18 = 2;
        |  var19 = [alloc 0,alloc 7,alloc -1,alloc 6,alloc 0,alloc 2,alloc 6];
        |  var20 = 7;
        |  var21 = 0;
        |  var22 = alloc 2;
        |  var23 = alloc [3,5,-1,3,7,0,2];
        |  var24 = 7;
        |  var25 = 7;
        |  var26 = 3;
        |  var27 = {ghMXybSFoP:alloc alloc alloc -1,tHnqSGydif:alloc 7,TtzDjjOHSq:alloc 7};
        |  var28 = [3,2,4,7,6,7];
        |  while ((var20 < var25)) {
        |    while (input) {
        |      output input;
        |    }
        |    var19[2] = alloc input;
        |    while ((var6 < var15)) {
        |      var19[3] = &var17;
        |      while ((var1 < var16)) {
        |        var1 = (var1 + 1);
        |      }
        |      output var13.gjFdRoDpea;
        |      while (var16) {
        |        while ((var6 < var4)) {
        |          while ((var26 < var20)) {
        |            while ((var24 < var16)) {
        |              var21 = 3;
        |              var24 = (var24 + 1);
        |            }
        |            while ((var0 < var20)) {
        |              output var15;
        |              var8 = [3,0,7,0,4];
        |              var0 = (var0 + 1);
        |            }
        |            var26 = (var26 + 1);
        |          }
        |          var6 = (var6 + 1);
        |        }
        |        while ((var4 < var11)) {
        |          while (input) {
        |            while (4) {
        |              output var8[2];
        |              var12 = alloc 3;
        |              output var28[0];
        |            }
        |            while (2) {}
        |          }
        |          output var1;
        |          var4 = (var4 + 1);
        |        }
        |      }
        |      var6 = (var6 + 1);
        |    }
        |    var20 = (var20 + 1);
        |  }
        |  while ((var0 < var26)) {
        |    while ((var25 < var0)) {
        |      while ((var20 < var11)) {
        |        while ((var17 < var11)) {
        |          while ((2 * 8)) {
        |            while ((var0 < var16)) {
        |              var0 = (var0 + 1);
        |            }
        |            while ((var24 < var4)) {
        |              output input;
        |              var24 = (var24 + 1);
        |            }
        |            while ((var25 < var21)) {
        |              var25 = (var25 + 1);
        |            }
        |            while ((var18 < var15)) {
        |              var10 = alloc -1;
        |              output var20;
        |              output input;
        |              var18 = (var18 + 1);
        |            }
        |          }
        |          var17 = (var17 + 1);
        |        }
        |        output var9.wSjliGVHIB;
        |        var20 = (var20 + 1);
        |      }
        |      if (input) {
        |        var11 = var18;
        |      } else {
        |        while ((var21 < var25)) {
        |          while ((var20 < var0)) {
        |            var20 = (var20 + 1);
        |          }
        |          var18 = input;
        |          var21 = (var21 + 1);
        |        }
        |        while ((var26 < var6)) {
        |          while ((var1 < var1)) {
        |            while ((var11 < var4)) {
        |              var11 = (var11 + 1);
        |            }
        |            var1 = (var1 + 1);
        |          }
        |          var26 = (var26 + 1);
        |        }
        |        if (input) {
        |          while ((var17 < var1)) {
        |            var17 = (var17 + 1);
        |          }
        |          var21 = input;
        |          var3 = var12;
        |          while ([3,1,6,3,4,8][5]) {}
        |        } else {
        |          while ((var16 < var17)) {
        |            output 3;
        |            var16 = (var16 + 1);
        |          }
        |          while ((var18 < var0)) {
        |            if (6) {
        |              var2 = {TRnFrOfoUr:alloc 7,fPXAqbxGaG:[4,3,5,6,0,0,5,7,3]};
        |              output !((((input * input) - var28[0]) * var28[1]) + input);
        |            } else {
        |              output !var8[2];
        |              output !(var28[0] + var11);
        |              var15 = 5;
        |              output var28[5];
        |            }
        |            while ((var25 < var11)) {
        |              var22 = alloc 8;
        |              output !input;
        |              var25 = (var25 + 1);
        |            }
        |            while (4) {
        |              var19 = [alloc 5,alloc 1,alloc 6,alloc 4,alloc 1,alloc 2,alloc 7];
        |              var12 = alloc 2;
        |              output !var28[0];
        |              var21 = 7;
        |            }
        |            var18 = (var18 + 1);
        |          }
        |          var19[4] = &var26;
        |        }
        |        var19[0] = alloc var9.wSjliGVHIB;
        |      }
        |      while ((var11 < var18)) {
        |        output input;
        |        while ((var17 < var21)) {
        |          while ((var1 < var21)) {
        |            var1 = (var1 + 1);
        |          }
        |          var17 = (var17 + 1);
        |        }
        |        while (!!7) {
        |          while ((var18 < var11)) {
        |            while ((var1 < var20)) {
        |              var0 = 2;
        |              var1 = (var1 + 1);
        |            }
        |            while ((var1 < var18)) {
        |              output (var8[1] * (var1 + input));
        |              output var8[3];
        |              var1 = (var1 + 1);
        |            }
        |            if (6) {
        |              var1 = 7;
        |              output input;
        |              var27 = {ghMXybSFoP:alloc alloc alloc -1,tHnqSGydif:alloc 0,TtzDjjOHSq:alloc 3};
        |              output !!input;
        |            } else {
        |              output !var21;
        |              var7 = {UYfmqvszXt:alloc 3,weYgbIPPem:alloc alloc 6};
        |              var11 = 8;
        |            }
        |            var18 = (var18 + 1);
        |          }
        |          var28[3] = [3,7,0,5,0,5,-1,-1,6][8];
        |        }
        |        while (input) {
        |          while ((var11 < var21)) {
        |            var11 = (var11 + 1);
        |          }
        |          output !6;
        |          while ((var1 < var17)) {
        |            if (6) {
        |              output var8[0];
        |            } else {
        |              output (!!var4 * var13.YbzoIttZWL);
        |              output var28[3];
        |              output input;
        |              var4 = 8;
        |            }
        |            while ((var4 < var18)) {
        |              output !(input * var24);
        |              output input;
        |              var28 = [5,0,8,6,0,5,7,2];
        |              var4 = (var4 + 1);
        |            }
        |            var1 = (var1 + 1);
        |          }
        |        }
        |        var11 = (var11 + 1);
        |      }
        |      var25 = (var25 + 1);
        |    }
        |    while ((var21 < var6)) {
        |      output input;
        |      while (var14.MlBCRWIMPG) {}
        |      var28[0] = !var13.gjFdRoDpea;
        |      var21 = (var21 + 1);
        |    }
        |    var0 = (var0 + 1);
        |  }
        |  while (input) {
        |    while ((var17 < var1)) {
        |      var3 = alloc input;
        |      while ((var26 < var17)) {
        |        var26 = (var26 + 1);
        |      }
        |      var28[1] = !var9.wSjliGVHIB;
        |      while ((var4 < var17)) {
        |        var28[5] = input;
        |        output (!6 * var6);
        |        while ((var0 < var17)) {
        |          while ((var21 < var26)) {
        |            var21 = (var21 + 1);
        |          }
        |          var0 = (var0 + 1);
        |        }
        |        var4 = (var4 + 1);
        |      }
        |      var17 = (var17 + 1);
        |    }
        |    while ((var26 < var1)) {
        |      var26 = (var26 + 1);
        |    }
        |    while (input) {
        |      while ((var6 < var6)) {
        |        var6 = (var6 + 1);
        |      }
        |      while ((var18 < var17)) {
        |        output var13.gjFdRoDpea;
        |        output var13.YbzoIttZWL;
        |        if (input) {
        |          while ((var26 < var24)) {
        |            var26 = (var26 + 1);
        |          }
        |          while ((2 - 3)) {}
        |        } else {
        |          while ((var24 < var21)) {
        |            while ((var11 < var26)) {
        |              output input;
        |              output (input - var13.gjFdRoDpea);
        |              output var9.wSjliGVHIB;
        |              var11 = (var11 + 1);
        |            }
        |            while ((var0 < var18)) {
        |              var0 = (var0 + 1);
        |            }
        |            output 2;
        |            var24 = (var24 + 1);
        |          }
        |        }
        |        var19[4] = alloc var1;
        |        var18 = (var18 + 1);
        |      }
        |      while ((var18 < var0)) {
        |        while ((var11 < var16)) {
        |          while ((var6 < var16)) {
        |            var6 = (var6 + 1);
        |          }
        |          while ((var11 < var20)) {
        |            var11 = (var11 + 1);
        |          }
        |          while ((var4 < var21)) {
        |            while ((var26 < var24)) {
        |              var26 = (var26 + 1);
        |            }
        |            var8[3] = 3;
        |            var4 = (var4 + 1);
        |          }
        |          var11 = (var11 + 1);
        |        }
        |        var18 = (var18 + 1);
        |      }
        |      while (var4) {
        |        while ((var17 < var4)) {
        |          var17 = (var17 + 1);
        |        }
        |        while ((var20 < var11)) {
        |          var0 = (4 - 6);
        |          var20 = (var20 + 1);
        |        }
        |      }
        |    }
        |  }
        |  if ((input + var8[0])) {
        |    while ((var20 < var15)) {
        |      var20 = (var20 + 1);
        |    }
        |    var23 = var23;
        |    output var8[3];
        |  } else {
        |    output var17;
        |    while ((var24 < var11)) {
        |      while ((var26 < var15)) {
        |        var26 = (var26 + 1);
        |      }
        |      while ((var6 < var18)) {
        |        var6 = (var6 + 1);
        |      }
        |      var24 = (var24 + 1);
        |    }
        |  }
        |  while (!var8[0]) {}
        |  output var8[2];
        |  return var9.wSjliGVHIB;
        |}
        |
        |""".stripMargin

    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program)
    val stateHistory = new StateHistory()
    val tree = new RandomPathSelectionStrategy(stateHistory)

    val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
    executor.run()

  }



  test("random factory test") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16;
        |  var0 = {KXjwsMbKfZ:7,CUXjOPLzcB:5,AroajAuMYC:5,grcHZwdmwQ:4};
        |  var1 = -1;
        |  var2 = -1;
        |  var3 = alloc 4;
        |  var4 = 8;
        |  var5 = 7;
        |  var6 = 8;
        |  var7 = alloc 3;
        |  var8 = alloc 0;
        |  var9 = 8;
        |  var10 = alloc 8;
        |  var11 = alloc 7;
        |  var12 = {zpQComXSGL:6,XOdWMGoYuo:6,hGRPSsjUqp:0,ILmVIeAGOE:5};
        |  var13 = 5;
        |  var14 = {jMeoQCuGeh:8,HPRRmnwFjc:[alloc -1,alloc 2,alloc 7,alloc 0,alloc 5,alloc 0]};
        |  var15 = 7;
        |  var16 = [4,0,8,6,-1,5];
        |  output input;
        |  var7 = &var9;
        |  while ((var13 < var6)) {
        |    while (input) {
        |      while ((var15 < var4)) {
        |        output var15;
        |        var15 = (var15 + 1);
        |      }
        |      var16[5] = input;
        |      var16[0] = input;
        |    }
        |    output 4;
        |    var16 = var16;
        |    var13 = (var13 + 1);
        |  }
        |  while (var12.ILmVIeAGOE) {}
        |  if (8) {
        |    var16[1] = input;
        |    var13 = (((var5 * !-1) * 5) * var12.hGRPSsjUqp);
        |    output 9;
        |    output var4;
        |  } else {
        |    var1 = 2;
        |  }
        |  output 6;
        |  while ((var15 < var4)) {
        |    var16 = var16;
        |    var1 = input;
        |    var6 = (input * !var1);
        |    var15 = (var15 + 1);
        |  }
        |  return !((7 - 4) - input);
        |}
        |""".stripMargin

    val program = parseUnsafe(code)

    new SymbolicExecutorFactory(false, false, Some("querycount"), Some(5), Some(5), "tree").get(program).run()

  }


}

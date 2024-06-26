package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.{Examples, MicrocSupport}
import microc.cfg.IntraproceduralCfgFactory
import microc.symbolic_execution.optimizations.subsumption.PathSubsumption
import microc.symbolic_execution.optimizations.summarization.LoopSummarization
import munit.FunSuite

import scala.concurrent.{Await, Future, TimeoutException}
import scala.util.control.NonFatal

import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

class SymbolicExecutorTest3 extends FunSuite with MicrocSupport with Examples {

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


  test("unreachable error") {
    val code =
      """
        |main() {
        |  var a, i, n;
        |  i = input;
        |  n = input;
        |  a = input;
        |  if (i >= n) {
        |    i = n - 1;
        |  }
        |  while (i < n) {
        |    a = a + 1;
        |  }
        |  a = 1 / 0;
        |  return a;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
    val executor = new LoopSummarization(cfg)
    executor.run()
  }




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


  test("sequential unbounded loop with error inside") {
    var code =
      """
        |main() {
        |  var k, i, n, m;
        |  k = 0;
        |  i = input;
        |  n = input;
        |  m = input;
        |  if (i != 0) {
        |     output 1;
        |  }
        |  else {
        |     output 2;
        |     i = 1;
        |  }
        |  while (n < m) {
        |     k = 1 / i;
        |  }
        |  return 0;
        |}
        |""".stripMargin;

    val future = Future {
      val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
      val executor = new LoopSummarization(cfg)
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException =>
      case NonFatal(e) => fail("")
    }



    code =
      """
        |main() {
        |  var k, i, n, m;
        |  k = 0;
        |  i = 0;
        |  n = input;
        |  m = input;
        |  if (i != 0) {
        |     output 1;
        |  }
        |  else {
        |     output 2;
        |  }
        |  while (n < m) {
        |     k = 1 / i;
        |  }
        |  return 0;
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new LoopSummarization(cfg)
    try {
      executor.run()
      fail("this should end with an exception.")
    }
    catch {
      case e: Exception =>
    }



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


  test("unbounded periodic loop finishes with summarization correctly") {
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


  test("unbounded periodic loop finishes with summarization correctly 2") {
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


    var future = Future {
      val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
      val executor = new LoopSummarization(cfg)
      executor.run()
      fail("should be killed by timeout")
    }

    try {
      Await.ready(future, 5.seconds)
    }
    catch {
      case _: TimeoutException =>
      case e: Throwable =>
        fail(e.toString)
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
        |  return 1 / (x - n);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new LoopSummarization(cfg)
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



    future = Future {
      val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
      val executor = new LoopSummarization(cfg)
      executor.run()
      fail("should be killed by timeout")
    }

    try {
      Await.ready(future, 5.seconds)
    }
    catch {
      case _: TimeoutException =>
      case e: Throwable =>
        fail(e.toString)
    }
  }

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


}

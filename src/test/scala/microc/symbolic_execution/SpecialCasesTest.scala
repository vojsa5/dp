package microc.symbolic_execution

import microc.cfg.IntraproceduralCfgFactory
import microc.symbolic_execution.optimizations.merging.AggressiveStateMerging
import microc.symbolic_execution.optimizations.summarization.LoopSummarization
import microc.{Examples, MicrocSupport}
import munit.FunSuite

import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.util.control.NonFatal

class SpecialCasesTest extends FunSuite with MicrocSupport with Examples {

  test("possible uninitialized var") {
    val code =
      """
        |main() {
        |  var x, i, n, a;
        |  i = 0;
        |  a = 0;
        |  n = input;
        |  while (i < n) {
        |     a = a + 1;
        |     i = i + 1;
        |  }
        |  if (a != 10) {
        |     x = 1;
        |  }
        |  return x + 1;
        |}
        |""".stripMargin;
    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new SymbolicExecutor(cfg, searchStrategy = new AggressiveStateMerging(new RandomSearchStrategy()));
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }


    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummarization(cfg, searchStrategy = new AggressiveStateMerging(new RandomSearchStrategy()));
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("no error") {
    val code =
      """
        |main() {
        |  var x, i, n, a;
        |  i = 0;
        |  a = 0;
        |  n = input;
        |  while (i < n) {
        |     a = a + 1;
        |     i = i + 1;
        |  }
        |  i = 0;
        |  while (i < n) {
        |     i = i + 1;
        |  }
        |  return 1;
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
    var executor = new SymbolicExecutor(cfg)
    val future = Future {
      executor.run()
      fail("executor should not stop")
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException =>
      case NonFatal(e) => fail("")
    }


    //loop summary is very fast
    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code))
    executor = new LoopSummarization(cfg)
    executor.run()
  }





  test("multiple possible indexes") {
    val code =
      """
        |main() {
        |  var arr, i, res;
        |  arr = [0, 1, 2];
        |  i = input;
        |  res = 0;
        |  if (i < 3 && i >= 0) {
        |     output arr[i];
        |     arr[i] = -1;
        |     res = arr[i];
        |  }
        |  return res;
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new SymbolicExecutor(cfg);
    executor.run()
  }


  test("multiple possible indexes create new path") {
    val code =
      """
        |main() {
        |  var arr, i, res;
        |  arr = [0, 1, 2];
        |  i = input;
        |  res = 0;
        |  if (i < 3 && i >= 0) {
        |     output arr[i];
        |     arr[i] = -1;
        |     res = arr[i];
        |  }
        |  return res;
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new SymbolicExecutor(cfg, createITEAtSymbolicArrayAccess = true);
    executor.run()
  }


  test("multiple possible indexes 2") {
    val code =
      """
        |main() {
        |  var arr, i, res;
        |  arr = [0, 1, 2];
        |  i = input;
        |  res = 0;
        |  if (i < 3 && i >= 0) {
        |     arr[i] = -1;
        |     res = arr[i];
        |  }
        |  return res;
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new SymbolicExecutor(cfg);
    executor.run()
  }


  test("multiple possible indexes 2 create new path") {
    val code =
      """
        |main() {
        |  var arr, i, res;
        |  arr = [0, 1, 2];
        |  i = input;
        |  res = 0;
        |  if (i < 3 && i >= 0) {
        |     arr[i] = -1;
        |     res = arr[i];
        |  }
        |  return res;
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new SymbolicExecutor(cfg, createITEAtSymbolicArrayAccess = true);
    executor.run()
  }


  test("multiple possible indexes 3") {
    val code =
      """
        |main() {
        |  var arr, i, res;
        |  arr = [0, 1, 2];
        |  i = input;
        |  res = 0;
        |  if (i < 2 && i >= 0) {
        |     res = arr[i + 1];
        |     arr[arr[i]] = i;
        |  }
        |  return res;
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new SymbolicExecutor(cfg);
    executor.run()
  }

}

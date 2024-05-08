package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.{Examples, MicrocSupport}
import microc.cfg.IntraproceduralCfgFactory
import microc.symbolic_execution.optimizations.summarization.LoopSummarization
import munit.FunSuite

import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

class SymbolicExecutorTest2 extends FunSuite with MicrocSupport with Examples {

  test("non-increment-update") {
    val code =
      """
        |main() {
        |  var i, n, k, l;
        |  i = input;
        |  n = input;
        |  k = 0;
        |  l = 1;
        |  if (i >= n) {
        |   i = n - 1;
        |  }
        |  while (i < n) {
        |     k = l;
        |     i = i + 1;
        |  }
        |  return 1 / k;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new LoopSummarization(cfg);
    executor.run()
    null
  }

  test("loop with multiple updated statements") {
    val code =
      """
        |main() {
        |  var i, n;
        |  i = input;
        |  n = input;
        |  while (i < n) {
        |     i = i + 1;
        |     i = i + 1;
        |  }
        |  return i;
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


  test("loop with multiple updated statements2") {
    val code =
      """
        |main() {
        |  var i, j, n;
        |  i = input;
        |  n = input;
        |  while (i < n) {
        |     i = i + 1;
        |     j = i;
        |     j = j + 1;
        |  }
        |  return i;
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


  test("type 1 nested loop summarizable") {
    val code =
      """
        |main() {
        |  var i, j, k, n, l;
        |  i = input;
        |  k = input;
        |  n = input;
        |  j = 1;
        |  l = input;
        |  while (i < n) {
        |     while (l < n) {
        |       j = 1;
        |       l = l + 1;
        |     }
        |     i = i + j;
        |     k = k + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new LoopSummarization(cfg);
    executor.run()

  }


  test("type 3 nested loop unsummarizable") {
    var code =
      """
        |main() {
        |  var i, j, k, n, l;
        |  i = input;
        |  k = input;
        |  n = input;
        |  j = 1;
        |  l = 0;
        |  while (i < n) {
        |     l = 0;
        |     while (l < n) {
        |       j = input;
        |       l = l + 1;
        |     }
        |     i = i + j;
        |     k = k + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;
    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummarization(cfg);
    var future = Future {
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


    code =
      """
        |main() {
        |  var i, j, k, n, l, o;
        |  i = input;
        |  k = input;
        |  n = input;
        |  j = 1;
        |  l = 0;
        |  o = 0;
        |  while (i < n) {
        |     o = 0;
        |     while (o < n) {
        |       l = 0;
        |       while (l < n) {
        |         j = input;
        |         l = l + 1;
        |       }
        |       o = o + 1;
        |     }
        |     i = i + j;
        |     k = k + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;
    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummarization(cfg);
    future = Future {
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


  test("type 3 nested loop unsummarizable2") {
    var code =
      """
        |main() {
        |  var i, j, k, n, l;
        |  i = input;
        |  k = input;
        |  n = input;
        |  j = 1;
        |  l = 0;
        |  while (i < n) {
        |     l = 0;
        |     i = i + j;
        |     while (l < n) {
        |       j = input;
        |       l = l + 1;
        |     }
        |     k = k + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;
    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummarization(cfg);
    var future = Future {
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


    code =
      """
        |main() {
        |  var i, j, k, n, l, o;
        |  i = input;
        |  k = input;
        |  n = input;
        |  j = 1;
        |  l = 0;
        |  o = 0;
        |  while (i < n) {
        |     o = 0;
        |     i = i + j;
        |     while (o < n) {
        |       l = 0;
        |       while (l < n) {
        |         j = input;
        |         l = l + 1;
        |       }
        |       o = o + 1;
        |     }
        |     k = k + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;
    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummarization(cfg);
    future = Future {
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

  test("type 3 nested loop unsummarizable3") {
  var code =
      """
        |main() {
        |  var i, j, k, n, l;
        |  i = input;
        |  k = input;
        |  n = input;
        |  j = 1;
        |  l = 0;
        |  while (i < n) {
        |     l = 0;
        |     while (l < n) {
        |       i = input;
        |       l = l + 1;
        |     }
        |     k = k + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;
    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummarization(cfg);
    var future = Future {
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



    code =
      """
        |main() {
        |  var i, j, k, n, l, o;
        |  i = input;
        |  k = input;
        |  n = input;
        |  j = 1;
        |  l = 0;
        |  o = 0;
        |  while (i < n) {
        |     o = 0;
        |     while (o < n) {
        |       l = 0;
        |       while (l < n) {
        |         i = input;
        |         l = l + 1;
        |       }
        |       o = o + 1;
        |     }
        |     k = k + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;
    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummarization(cfg);
    future = Future {
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


  test("unreachable error") {
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

  test("basic loop test") {
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





}

package microc.symbolic_execution

import microc.cfg.IntraproceduralCfgFactory
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class SymbolicExecutorTest extends FunSuite with MicrocSupport with Examples{
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

  test("my5") {
    val code =
      """
        |main() {
        |  var y;
        |  y = 3;
        |  while (y > 0) {
        |   y = y - 1;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
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

  test("multi functional") {
    val code =
      """
        |
        |fce(n) {
        |  while (n == 0) {
        |     n = 1 / 0;
        |  }
        |  return n + 2;
        |}
        |
        |main() {
        |  var a,b;
        |  b = 5;
        |  a = fce(b);
        |  return a;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

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
        |  b = 3;
        |  a = fac(b);
        |  return a;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

}

package microc.symbolic_execution

import microc.cfg.IntraproceduralCfgFactory
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class SymbolicExecutorTest extends FunSuite with MicrocSupport with Examples{
  test("my") {
    val code =
      """
        |f() {
        |  var x,y,z,a,b;
        |  z = a+b;
        |  y = a*b;
        |  while (y > a+b) {
        |    a = a+1;
        |    x = a+b;
        |  }
        |  return 0;
        |}
        |main() {
        |  var x;
        |  x = f();
        |  return x;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

  test("infinite paths") {
    val code =
      """
        |main() {
        |  var y;
        |  y = input;
        |  while (y > 0) {
        |   y = y - 1;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a StackOverflowError but it did not occur.")
    }
    catch {
      case _: StackOverflowError =>
      case other: Throwable => fail("Expected a StackOverflowError, but caught different exception: " + other)
    }

    null
  }


  test("infinite paths 2") {
    val code =
      """
        |main() {
        |  var y;
        |  y = input;
        |  y = y + 1;
        |  while (y > 0) {
        |   y = y - 1;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a StackOverflowError but it did not occur.")
    }
    catch {
      case _: StackOverflowError =>
      case other: Throwable => fail("Expected a StackOverflowError, but caught different exception: " + other)
    }

    null
  }

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

  test("my3") {
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

  /*test("multi functional") {
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
        |  var x,y,z,a,b;
        |  b = 5;
        |  a = fce(b);
        |  return a;
        |}
        |""".stripMargin;
    val (cfg, declarations) = parseCfg(code);
    val executor = new SymbolicExecutor(cfg, declarations);
    executor.run()
    null
  }
*/
}

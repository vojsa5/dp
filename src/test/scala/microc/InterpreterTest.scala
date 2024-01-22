package microc

import munit.FunSuite
import microc.interpreter.MicroCInterpreter

class InterpreterTest extends FunSuite with MicrocSupport {
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
        |  b = 5;
        |  a = fac(b);
        |  return a;
        |}
        |""".stripMargin;
    val interpreter = new MicroCInterpreter(parseUnsafe(code), null, null, false);
    val res = interpreter.run(List.empty)
    null
  }

  test("indirect-assign") {
    val code =
      """
        |main() {
        |   var x, y;
        |   x = 1;
        |   y = &x;
        |   *y = 42;
        |   return x;
        | }
        |
        |""".stripMargin;
    val interpreter = new MicroCInterpreter(parseUnsafe(code), null, null, false);
    val res = interpreter.run(List.empty)
    null
  }
}

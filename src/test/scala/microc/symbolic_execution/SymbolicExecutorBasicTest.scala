package microc.symbolic_execution

import microc.cfg.IntraproceduralCfgFactory
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class SymbolicExecutorBasicTest extends FunSuite with MicrocSupport with Examples {


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
        |  b = 5;
        |  a = fac(b);
        |  output(a);
        |  return a;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }


  test("paths must finish main") {
    val code =
      """
        | foo(n) {
        |   var r;
        |   if (n == 1) {
        |     r = 1;
        |   }
        |   else {
        |     r = 0;
        |   }
        |   return r;
        | }
        |
        | main() {
        |   var x;
        |   x = input;
        |   x = 1 / foo(x);
        |   return x;
        | }
        |
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

  // valid programs without any input
  test("return 42") {
    val code =
      """
        | main() {
        |   return 42;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("basic-expressions") {
    val code =
      """
        | main() {
        |   return 1932/2/23;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("function-call-1") {
    val code =
      """
        | f(z) {
        |   return z + 1;
        | }
        |
        | main() {
        |   return f(f(2) + f(3));
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 8)
    null
  }

  test("direct assign") {
    val code =
      """
        | main() {
        |   var x, y;
        |   x = 21;
        |   y = x + 21;
        |   return y;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }


  test("indirect assign") {
    val code =
      """
        | main() {
        |   var x, y;
        |   x = 1;
        |   y = &x;
        |   *y = 42;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    val t = executor.run()
    assert(t == 42)
    null
  }

  test("basic recursion") {
    val code =
      """
        | f(n) {
        |  var r;
        |
        |  if (n == 0) {
        |    r = 1;
        |  } else {
        |    r = n * f(n - 1);
        |  }
        |  return r;
        |}
        |
        | main() {
        |   return f(5);
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 120)
    null
  }

  test("return var") {
    val code =
      """
        | main() {
        |  var x;
        |  x = 42;
        |  return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("return expr") {
    val code =
      """
        | main() {
        |  var x, y;
        |  x = 43;
        |  y = 1;
        |  return x-y;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("return comparison") {
    val code =
      """
        | main() {
        |  var x, y;
        |  x = 1;
        |  y = 1;
        |  return x == y;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 1)
    null
  }

  test("pointer-cmp-1") {
    val code =
      """
        | main() {
        |  var x;
        |  x = null;
        |  return x == null;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 1)
    null
  }

  test("pointer-cmp-2") {
    val code =
      """
        | main() {
        |  var x;
        |  x = alloc null;
        |  return *x == null;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 1)
    null
  }

  test("pointer-cmp-3") {
    val code =
      """
        | main() {
        |  var x, y;
        |  x = alloc null;
        |  y = x;
        |  return x == y;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 1)
    null
  }

  test("nested-blocks") {
    val code =
      """
        | main() {
        |   var x;
        |   x = 1;
        |   {
        |     x = x + 41;
        |   }
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("deref") {
    val code =
      """
        | main() {
        |   var x;
        |   x = alloc 1;
        |   *x = 42;
        |   return *x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("deref-null") {
    val code =
      """
        | main() {
        |   var x;
        |   x = null;
        |   *x = 42;
        |   return *x;
        | }
        |
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

  test("basic-pointer") {
    val code =
      """
        | main() {
        |   var x, y;
        |   x = 43;
        |   y = &x;
        |   *y = *y - 1;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("doubler-pointer") {
    val code =
      """
        | main() {
        |   var x, y, z;
        |   x = 43;
        |   y = &x;
        |   z = &y;
        |   **z = *y - 1;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("ret-non-int-from-main") {
    val code =
      """
        |  main() {
        |   var x;
        |   x = 1;
        |   return &x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
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

  test("uninitialized-1") {
    val code =
      """
        |  main() {
        |   var x;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
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

  test("uninitialized-2") {
    val code =
      """
        | main() {
        |   var x;
        |   *x = 1;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
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

  test("array") {
    val code =
      """
        | main() {
        |   var a, b;
        |   a = [1,2];
        |   b = a[a[0]];
        |   a[a[0]-1] = 40;
        |   return b + a[0];
        | }
        |""".stripMargin
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }

  test("array out of bounds") {
    val code =
      """
        | main() {
        |   var a;
        |   a = [1,2];
        |   a[2] = 1;
        |   return 0;
        | }
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }

  test("array out of bounds 2") {
    val code =
      """
        | main() {
        |   var a, b;
        |   a = [1,2];
        |   b = -1;
        |   a[b] = 1;
        |   return 0;
        | }
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }

  test("array wih multiple dimensions") {
    val code =
      """
        | main() {
        |   var a, b;
        |   a = [[0,1],[2,3,4]];
        |   b = a[0];
        |   b[1] = b[1] + 1;
        |   a[1][2] = a[1][0] * 2 * 10;
        |   return a[0][1] + a[1][2];
        | }
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }


  test("basic records") {
    val code =
      """
        |  main() {
        |   var r;
        |   r = { x: 1, y: 41};
        |   return r.x + r.y;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }

  test("missing field") {
    val code =
      """
        | main() {
        |   var r;
        |   r = { x: 1 };
        |   r.y = 42;
        |   return r.x;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("non-record-access") {
    val code =
      """
        | main() {
        |   var r;
        |   r = 1;
        |   return r.x;
        | }
        |
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("non-pointer-access") {
    val code =
      """
        | main() {
        |   var r;
        |   r = 1;
        |   (*r).x = 41;
        |   return r.x;
        | }
        |
        |
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("direct-field-assign") {
    val code =
      """
        | main() {
        |   var r;
        |   r = { x: 1 };
        |   r.x = 42;
        |   return r.x;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }


  test("indirect-field-assign") {
    val code =
      """
        | main() {
        |   var r, s, t;
        |   r = { x: 1 };
        |   s = &r;
        |   t = &s;
        |   (**t).x = 42;
        |   return r.x;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }

  test("nested records") {
    val code =
      """
        | main() {
        |   var r, s;
        |   r = { a: 1 };
        |   s = { a: &r, b: 2 };
        |   (*(s.a)).a = 40 + s.b;
        |   return r.a;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }


  test("missing fields") {
    val code =
      """
        | main() {
        |   var r;
        |   r = { a: 1 };
        |   r.b = 1;
        |   return r.b;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("no-nested-records") {
    val code =
      """
        | main() {
        |   var r1, r2;
        |   r1 = { a: 1 };
        |   r2 = { a: 1, b: r1 };
        |   return 0;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("assign to records") {
    val code =
      """
        | main() {
        |   var r,s;
        |   r = { a: null, b: null };
        |   s = { c: 1 };
        |   r.a = &s;
        |   r.b = &s;
        |   s.c = 2;
        |   return (*(r.a)).c + (*(r.b)).c;
        | }
        |
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 4)
  }


  test("records-copy-1") {
    val code =
      """
        |main() {
        |   var a,b;
        |   a = { n:1 };
        |   b = a;
        |   b.n = 2;
        |   output a.n;
        |   output b.n;
        |   return 0;
        | }
        |
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 0)
  }


  test("records-copy-2") {
    val code =
      """
        |main() {
        |   var a,b,c,d;
        |   a = { n:1 };
        |   b = { m: &a };
        |   c = b;
        |   d = a;
        |   d.n = 2;
        |   (*b.m).n = 3;
        |   (*c.m).n = 4;
        |   output a.n;
        |   output (*b.m).n;
        |   output (*c.m).n;
        |   output d.n;
        |   return 0;
        | }
        |
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 0)
  }

}
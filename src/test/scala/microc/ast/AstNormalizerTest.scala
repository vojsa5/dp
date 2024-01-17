package microc.ast

import microc.MicrocSupport
import munit.{FunSuite, Location}

// TODO: enable when implemented
@munit.IgnoreSuite
class AstNormalizerTest extends FunSuite with MicrocSupport {

  check(
    "My1",
    """
      | foo(f, y) {
      |   var x;
      |   x = 5;
      |   return x;
      | }
      |""".stripMargin,
    """
      | foo(f,y) {
      |   var x;
      |   x = 5;
      |   return x;
      | }
      |""".stripMargin
  )

  check(
    "My2",
    """
      | foo(f, y) {
      |   var x;
      |   x = f(y+3);
      |   return x;
      | }
      |""".stripMargin,
    """
      | foo(f,y) {
      |   var _t1;
      |   var x;
      |   _t1 = (y + 3);
      |   x = f(_t1);
      |   return x;
      | }
      |""".stripMargin
  )

  check(
    "Book - section 2.3",
    """
      | foo(f, y) {
      |   var x;
      |   x = f(y+3)*5;
      |   return x;
      | }
      |""".stripMargin,
    """
      | foo(f,y) {
      |   var _t1,_t2;
      |   var x;
      |   _t1 = (y + 3);
      |   _t2 = f(_t1);
      |   x = (_t2 * 5);
      |   return x;
      | }
      |""".stripMargin
  )

  check(
    "Book - exercise 2.3",
    """
      | foo(f, g, h) {
      |   var x;
      |   x = (**f)(g()+h());
      |   return x;
      | }
      |""".stripMargin,
    """
      | foo(f,g,h) {
      |   var _t1,_t2,_t3,_t4,_t5;
      |   var x;
      |   _t1 = (*f);
      |   _t2 = (*_t1);
      |   _t3 = g();
      |   _t4 = h();
      |   _t5 = (_t3 + _t4);
      |   x = _t2(_t5);
      |   return x;
      | }
      |""".stripMargin
  )

  check(
    "Book - exercise 2.4",
    """
      | foo(x, y) {
      |   **x = **y;
      |   return **x;
      | }
      |""".stripMargin,
    """
      | foo(x,y) {
      |   var _t1,_t2,_t3,_t4;
      |   _t1 = (*x);
      |   _t2 = (*y);
      |   (*_t1) = (*_t2);
      |   _t3 = (*x);
      |   _t4 = (*_t3);
      |   return _t4;
      | }
      |""".stripMargin
  )

  check(
    "Bin",
    """
      | f(x, g) {
      |   var y, z;
      |   y = alloc x + 2;
      |   output y + 2;
      |   z = g(x + 2, x - 5) + 4;
      |   return z + x;
      | }
      |""".stripMargin,
    """
      | f(x,g) {
      |   var _t1,_t2,_t3,_t4,_t5,_t6;
      |   var y,z;
      |   _t1 = (x + 2);
      |   y = alloc _t1;
      |   _t2 = (y + 2);
      |   output _t2;
      |   _t3 = (x + 2);
      |   _t4 = (x - 5);
      |   _t5 = g(_t3,_t4);
      |   z = (_t5 + 4);
      |   _t6 = (z + x);
      |   return _t6;
      | }
      |""".stripMargin
  )

  check(
    "My3",
    """
      | f(x) {
      |   var a;
      |   a = 1;
      |   if (a + 1 > a) {
      |     a = a + a + 1;
      |   }
      |   return a;
      | }
      |""".stripMargin,
    """
      | f(x) {
      |   var _t1,_t2,_t3;
      |   var a;
      |   a = 1;
      |   _t1 = (a + 1);
      |   _t2 = (_t1 > a);
      |   if (_t2) {
      |     _t3 = (a + a);
      |     a = (_t3 + 1);
      |   }
      |   return a;
      |}
      |""".stripMargin
  )

  check(
    "If",
    """
      | f(x) {
      |   var a,b,c,d;
      |   a = 1;
      |   if (a + 1 > a) {
      |     a = a + a + 1;
      |   }
      |   if (a + a > f(a * a)) {
      |     a = a + 1;
      |   } else {
      |     a = a / 2 / a;
      |   }
      |   return a;
      | }
      |""".stripMargin,
    """
      | f(x) {
      |   var _t1,_t2,_t3,_t4,_t5,_t6,_t7,_t8;
      |   var a,b,c,d;
      |   a = 1;
      |   _t1 = (a + 1);
      |   _t2 = (_t1 > a);
      |   if (_t2) {
      |     _t3 = (a + a);
      |     a = (_t3 + 1);
      |   }
      |   _t4 = (a + a);
      |   _t5 = (a * a);
      |   _t6 = f(_t5);
      |   _t7 = (_t4 > _t6);
      |   if (_t7) {
      |     a = (a + 1);
      |   } else {
      |     _t8 = (a / 2);
      |     a = (_t8 / a);
      |   }
      |   return a;
      |}
      |""".stripMargin
  )

  check(
    "While",
    """
      | f() {
      |   var a,b,c,d;
      |   a = 1;
      |   b = 2;
      |   c = 30;
      |   d = 40;
      |   while (a + b > c + d) {
      |     a = a + 1;
      |     d = d - 1;
      |   }
      |   return a;
      | }
      |""".stripMargin,
    """
      | f() {
      |   var _t1,_t2,_t3;
      |   var a,b,c,d;
      |   a = 1;
      |   b = 2;
      |   c = 30;
      |   d = 40;
      |   _t1 = (a + b);
      |   _t2 = (c + d);
      |   _t3 = (_t1 > _t2);
      |   while (_t3) {
      |     {
      |       a = (a + 1);
      |       d = (d - 1);
      |     }
      |     _t1 = (a + b);
      |     _t2 = (c + d);
      |     _t3 = (_t1 > _t2);
      |   }
      |   return a;
      | }
      |""".stripMargin
  )

  check(
    "Fun",
    """
      | f(x, y) {
      |   var y;
      |   y = f(f(x + 2 * 3, x), x * 10) + 2;
      |   return y * g(x);
      | }
      |""".stripMargin,
    """
      | f(x,y) {
      |   var _t1,_t2,_t3,_t4,_t5,_t6,_t7;
      |   var y;
      |   _t1 = (2 * 3);
      |   _t2 = (x + _t1);
      |   _t3 = f(_t2,x);
      |   _t4 = (x * 10);
      |   _t5 = f(_t3,_t4);
      |   y = (_t5 + 2);
      |   _t6 = g(x);
      |   _t7 = (y * _t6);
      |   return _t7;
      | }
      |""".stripMargin
  )

  check(
    "Point",
    """
      | f() {
      |   var a, _t3;
      |   a = alloc 1 + 1;
      |   _t3 = &a;
      |   **_t3 = 2;
      |   return 10 + *a;
      | }
      |""".stripMargin,
    """
      | f() {
      |   var _t1,_t2,_t4,_t5;
      |   var a,_t3;
      |   _t1 = (1 + 1);
      |   a = alloc _t1;
      |   _t3 = &a;
      |   _t2 = (*_t3);
      |   (*_t2) = 2;
      |   _t4 = (*a);
      |   _t5 = (10 + _t4);
      |   return _t5;
      | }
      |""".stripMargin
  )

  check(
    "Record",
    """
      | f() {
      |   var x, y, z;
      |   x = {a: g(2 * 2) + 3, b: 2 * 3 * 4 };
      |   y = {c: &x};
      |   z = &y;
      |   (*(*z).c).b = 2 + 3;
      |   return 0;
      | }
      |""".stripMargin,
    """
      | f() {
      |   var _t1,_t2,_t3,_t4,_t5,_t6,_t7;
      |   var x,y,z;
      |   _t1 = (2 * 2);
      |   _t2 = g(_t1);
      |   _t3 = (_t2 + 3);
      |   _t4 = (2 * 3);
      |   _t5 = (_t4 * 4);
      |   x = {a:_t3,b:_t5};
      |   _t6 = &x;
      |   y = {c:_t6};
      |   z = &y;
      |   _t7 = (*z).c;
      |   (*_t7).b = (2 + 3);
      |   return 0;
      | }
      |""".stripMargin
  )

  check("SExpr in functions, allocations and records",
  """
      |f() {
      |  var x, y;
      |  x = 1;
      |  y = alloc 1;
      |  y = alloc x;
      |  y = alloc x + 1;
      |  return g(x + 1, x, 1, {a: x+1, b:x, c: 1});
      |}
      |""".stripMargin,
    """
      |f() {
      |  var _t1,_t2,_t3,_t4,_t5;
      |  var x,y;
      |  x = 1;
      |  y = alloc 1;
      |  y = alloc x;
      |  _t1 = (x + 1);
      |  y = alloc _t1;
      |  _t2 = (x + 1);
      |  _t3 = (x + 1);
      |  _t4 = {a:_t3,b:x,c:1};
      |  _t5 = g(_t2,x,1,_t4);
      |  return _t5;
      |}
      |""".stripMargin)

  check("Nested record",
    """
      |f(z) {
      |  (*(*z).x).a = 15;
      |  return 0;
      |}
      |
      |""".stripMargin,
    """
      |f(z) {
      |  var _t1;
      |  _t1 = (*z).x;
      |  (*_t1).a = 15;
      |  return 0;
      |}
      |""".stripMargin)

  check("Two nested records",
    """
      |f(z) {
      | (*(*(*z).x).a).b = 15;
      |  return 0;
      |}
      |
      |""".stripMargin,
    """
      |f(z) {
      |  var _t1,_t2;
      |  _t1 = (*z).x;
      |  _t2 = (*_t1).a;
      |  (*_t2).b = 15;
      |  return 0;
      |}
      |""".stripMargin)

  private val printer = new AstPrinter()

  private def check(name: String, before: String, after: String)(implicit loc: Location): Unit =
    test(name) {
      assertEquals(printer.print(normalize(before)), printer.print(parseUnsafe(after)))
    }

  private def normalize(code: String): Program = {
    val prg = parseUnsafe(code)
    val norm = new AstNormalizer
    norm.normalize(prg)
  }
}

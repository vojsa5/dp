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
    executor.run()
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
        |  sum = 0;
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
      fail("the program should timeout")
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) =>
        println(s"Test failed due to an unexpected error: ${e.getMessage}")
        fail("")
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





  test("random generated test finishes with no error2") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19;
        |  var0 = 7;
        |  var1 = 2;
        |  var2 = alloc 4;
        |  var3 = -1;
        |  var4 = alloc alloc 2;
        |  var5 = {KSwRjCheyb:alloc alloc alloc -1,ZEuSRWDOdJ:alloc 7,XTIhcMfwCe:[7,2,4,7,7,5],hrlZQonvYe:alloc 8};
        |  var6 = alloc 0;
        |  var7 = 8;
        |  var8 = {PXLFHuRJYk:1,MeBUkbYZCx:0,mYggQuyGux:[alloc 1,alloc -1,alloc -1,alloc -1,alloc 0]};
        |  var9 = alloc alloc alloc 3;
        |  var10 = 7;
        |  var11 = alloc 2;
        |  var12 = -1;
        |  var13 = [2,1,2,1,7,5,3,3];
        |  var14 = 1;
        |  var15 = alloc alloc alloc 1;
        |  var16 = alloc 7;
        |  var17 = alloc 7;
        |  var18 = {BtHpRqdRKk:1,NcwtDZbsUK:1,TdCBmBjWpK:alloc alloc alloc 1};
        |  var19 = [0,2,8,6,2,2,0,3];
        |  if ((var3 - !var13[4])) {
        |    var18 = var18;
        |  } else {
        |    if (input) {
        |      while (var8.PXLFHuRJYk) {
        |        while (input) {
        |          output input;
        |        }
        |        while ((var0 < var7)) {
        |          output var0;
        |          output var13[7];
        |          var0 = (var0 + 1);
        |        }
        |        output input;
        |      }
        |      var13[3] = var18.NcwtDZbsUK;
        |    } else {
        |      if (var13[6]) {
        |        if (var18.NcwtDZbsUK) {
        |          output (!input - var13[7]);
        |          output input;
        |        } else {
        |          var14 = [3,1,5,7,7][3];
        |          var13 = var13;
        |          var2 = &var0;
        |        }
        |        while (!!4) {
        |          var0 = input;
        |          output (input - var13[1]);
        |          var18 = var18;
        |          output var19[6];
        |        }
        |      } else {
        |        output input;
        |        output ((-1 + 7) * input);
        |      }
        |      var19 = var19;
        |      var13[7] = input;
        |    }
        |    while (!(input + input)) {
        |      if (input) {
        |        if (var18.BtHpRqdRKk) {
        |          var3 = [5,-1,3,3,1,6,8,6,2][8];
        |          output var13[1];
        |        } else {
        |          var17 = &var7;
        |        }
        |        while ((var3 < var14)) {
        |          output (input * !(var7 - var12));
        |          var1 = input;
        |          output var18.NcwtDZbsUK;
        |          var2 = &var10;
        |          var3 = (var3 + 1);
        |        }
        |        var19[3] = var8.PXLFHuRJYk;
        |        var8 = var8;
        |      } else {
        |        while (input) {
        |          var16 = var2;
        |          var8 = var8;
        |          var1 = (5 - 8);
        |        }
        |        var13[0] = input;
        |        while ((var12 < var10)) {
        |          var2 = &var14;
        |          var12 = (var12 + 1);
        |        }
        |        output var10;
        |      }
        |      var5 = var5;
        |      if (input) {
        |        if (input) {
        |          var17 = &var1;
        |          output var14;
        |          output var19[1];
        |        } else {
        |          output var13[1];
        |          var0 = (7 - 4);
        |          output !(var7 * !var19[5]);
        |        }
        |        var5 = var5;
        |        var16 = var17;
        |      } else {}
        |      var3 = input;
        |    }
        |    while ((var10 < var14)) {
        |      while (!input) {}
        |      while (var3) {
        |        var13[0] = var19[4];
        |        while ((var7 < var14)) {
        |          var7 = (var7 + 1);
        |        }
        |        var4 = alloc alloc 0;
        |      }
        |      var10 = (var10 + 1);
        |    }
        |  }
        |  var13[3] = (var10 - input);
        |  while ((var1 < var1)) {
        |    var1 = (var1 + 1);
        |  }
        |  if (input) {
        |    if (input) {} else {
        |      if (var18.BtHpRqdRKk) {
        |        while (!var8.MeBUkbYZCx) {}
        |        while (var18.NcwtDZbsUK) {
        |          output var13[6];
        |          output var12;
        |          output var19[6];
        |          output var3;
        |        }
        |        var19[3] = input;
        |      } else {}
        |      var8 = var8;
        |      var6 = var17;
        |    }
        |    var13[1] = var12;
        |  } else {
        |    var13[2] = input;
        |    output var19[6];
        |  }
        |  var13[0] = !input;
        |  while ((var3 < var12)) {
        |    if (input) {
        |      if (input) {
        |        var13 = var13;
        |        while ((var0 < var14)) {
        |          var16 = var17;
        |          output input;
        |          output var13[6];
        |          var0 = (var0 + 1);
        |        }
        |      } else {
        |        while (var3) {
        |          var6 = var6;
        |          output !var13[2];
        |          output var18.BtHpRqdRKk;
        |          output (!(var14 + input) * var8.PXLFHuRJYk);
        |        }
        |        var19[7] = input;
        |        output input;
        |        while (var19[4]) {}
        |      }
        |      while (input) {
        |        while (input) {
        |          output input;
        |          var13 = var13;
        |          output input;
        |          var1 = var8.MeBUkbYZCx;
        |        }
        |        output !!-1;
        |        var13[4] = (!-1 + !0);
        |      }
        |      while (input) {
        |        while (![2,8,1,2,1,2,6,0][0]) {}
        |        while (var14) {
        |          output !input;
        |          output input;
        |        }
        |      }
        |      var13[7] = input;
        |    } else {}
        |    if (var19[2]) {} else {
        |      var12 = (input - var13[5]);
        |    }
        |    if (!input) {
        |      while ((!var8.PXLFHuRJYk * input)) {
        |        var13[4] = !var14;
        |        while (input) {
        |          var11 = &var1;
        |          var4 = var4;
        |        }
        |      }
        |    } else {
        |      var13[0] = input;
        |      var19[7] = var8.MeBUkbYZCx;
        |    }
        |    var3 = (var3 + 1);
        |  }
        |  return var3;
        |}
        |""".stripMargin



    val future = Future {
      val program = parseUnsafe(code)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)

      val covered = new mutable.HashSet[CfgNode]
      val executor = new SymbolicExecutor(cfg, covered = Some(covered), searchStrategy = new CoverageSearchStrategy(covered))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }
  }


  test("random generated test finishes with no error3") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16;
        |  var0 = 6;
        |  var1 = {nntAuyaHly:8,VODxYehZDa:-1,KxleKocfpB:2};
        |  var2 = 5;
        |  var3 = {bXnyhIljBP:2,vjtdOitzVq:5};
        |  var4 = alloc 2;
        |  var5 = 5;
        |  var6 = 1;
        |  var7 = alloc 3;
        |  var8 = alloc 6;
        |  var9 = 8;
        |  var10 = [4,8,5,6,7,4];
        |  var11 = 5;
        |  var12 = alloc alloc 5;
        |  var13 = alloc 5;
        |  var14 = alloc 6;
        |  var15 = {YGrruYqBBT:1,ivIAUUaSWZ:3,ZkIjxLLsXd:8,CAAwizUNTe:2,XlGkyEOzGO:6};
        |  var16 = [7,0,8,7,-1,2,3,7];
        |  while ((input + var2)) {
        |    while (input) {
        |      output (input - (var6 - [8,5,7,5,-1,-1,6,2][2]));
        |      while ((var2 < var6)) {
        |        if (var1.VODxYehZDa) {} else {
        |          while (var15.YGrruYqBBT) {}
        |          var16[3] = var15.ivIAUUaSWZ;
        |          if (!1) {} else {}
        |          var16 = var16;
        |        }
        |        var2 = (var2 + 1);
        |      }
        |    }
        |    var2 = (var11 - !var10[4]);
        |  }
        |  if (input) {
        |    output (input - !(var1.nntAuyaHly + var1.VODxYehZDa));
        |  } else {
        |    if (!var16[3]) {} else {
        |      var7 = alloc input;
        |      output !var10[0];
        |      output !var6;
        |      var6 = input;
        |    }
        |  }
        |  while (var15.ZkIjxLLsXd) {
        |    var14 = var14;
        |    while (var10[5]) {
        |      if (!var15.CAAwizUNTe) {
        |        var10[3] = input;
        |        if (var0) {
        |          output (2 - 5);
        |          while ((var11 < var0)) {
        |            var16[2] = -1;
        |            var11 = (var11 + 1);
        |          }
        |        } else {
        |          if (input) {
        |            var10 = [-1,3,2,0,5,6];
        |            var9 = 6;
        |          } else {}
        |          output var5;
        |        }
        |        while (var10[1]) {
        |          while ((var11 < var11)) {
        |            output 5;
        |            var10[5] = 0;
        |            var10[2] = 7;
        |            var16[3] = 3;
        |            var11 = (var11 + 1);
        |          }
        |        }
        |        var10[2] = input;
        |      } else {
        |        output var16[3];
        |        var10[1] = input;
        |        output var6;
        |      }
        |      var10[1] = var1.VODxYehZDa;
        |    }
        |    output var16[1];
        |    output !var10[2];
        |  }
        |  var10[5] = var16[5];
        |  var10[3] = input;
        |  if (input) {
        |    if (var6) {} else {
        |      while ((input + (var5 - var15.CAAwizUNTe))) {}
        |      while ((([2,6,2,5,5][1] + input) - var15.YGrruYqBBT)) {
        |        var16[6] = var15.CAAwizUNTe;
        |        if (var3.vjtdOitzVq) {
        |          if (var5) {
        |            if (4) {
        |              output var11;
        |            } else {}
        |            var4 = alloc 7;
        |            var3 = {bXnyhIljBP:8,vjtdOitzVq:8};
        |          } else {
        |            while ((var11 < var11)) {
        |              output input;
        |              output var15.CAAwizUNTe;
        |              var11 = (var11 + 1);
        |            }
        |            var11 = 2;
        |            if (3) {
        |              var14 = alloc 2;
        |            } else {
        |              output input;
        |              output var6;
        |              var6 = 4;
        |              var14 = alloc -1;
        |            }
        |            output 0;
        |          }
        |          output var15.YGrruYqBBT;
        |        } else {
        |          while ((var2 < var9)) {
        |            var7 = alloc 4;
        |            while ((var6 < var5)) {
        |              output (input + !var3.bXnyhIljBP);
        |              var8 = alloc 1;
        |              output input;
        |              var6 = (var6 + 1);
        |            }
        |            output 2;
        |            var2 = (var2 + 1);
        |          }
        |          while (var15.XlGkyEOzGO) {
        |            if (0) {
        |              output !var9;
        |            } else {}
        |            output 0;
        |            if (7) {
        |              var15 = {YGrruYqBBT:8,ivIAUUaSWZ:2,ZkIjxLLsXd:0,CAAwizUNTe:4,XlGkyEOzGO:6};
        |              output var0;
        |            } else {
        |              var12 = alloc alloc 2;
        |              output var11;
        |              var14 = alloc 4;
        |            }
        |            if (1) {
        |              var10 = [0,4,7,-1,-1,5];
        |            } else {
        |              output !input;
        |            }
        |          }
        |          var16[6] = input;
        |        }
        |      }
        |      while (var0) {
        |        while ((var11 < var6)) {
        |          var10[4] = var3.bXnyhIljBP;
        |          var0 = var9;
        |          while (input) {
        |            output 4;
        |          }
        |          var16[0] = [4,3,7,4,8,8][2];
        |          var11 = (var11 + 1);
        |        }
        |        output (input - input);
        |        while (var15.ZkIjxLLsXd) {}
        |      }
        |    }
        |    var16[2] = input;
        |  } else {
        |    if (input) {
        |      if (input) {
        |        var10[0] = !var15.ZkIjxLLsXd;
        |        var10[2] = input;
        |        while ((var5 < var0)) {
        |          output var15.CAAwizUNTe;
        |          var0 = !8;
        |          var5 = (var5 + 1);
        |        }
        |      } else {
        |        output !!7;
        |        while ((var5 < var5)) {
        |          var14 = var14;
        |          var11 = (5 + 5);
        |          var10[0] = input;
        |          while (!2) {
        |            while (7) {
        |              var12 = alloc alloc 1;
        |            }
        |          }
        |          var5 = (var5 + 1);
        |        }
        |        while ((var9 < var9)) {
        |          while (!4) {}
        |          while ((var0 < var9)) {
        |            while ((var2 < var5)) {
        |              var8 = alloc 5;
        |              var2 = (var2 + 1);
        |            }
        |            var0 = (var0 + 1);
        |          }
        |          var16[6] = [8,-1,3,4,3,7,1,1][5];
        |          var9 = (var9 + 1);
        |        }
        |      }
        |      if (input) {
        |        var10[2] = var16[5];
        |      } else {
        |        var16[0] = var16[5];
        |        var10[4] = var10[2];
        |        var16[5] = input;
        |        output var0;
        |      }
        |      while (var10[3]) {
        |        if (var10[4]) {} else {}
        |      }
        |      while (input) {
        |        var10 = var10;
        |        var6 = input;
        |        var15 = var15;
        |      }
        |    } else {}
        |  }
        |  return !input;
        |}
        |""".stripMargin


    val future = Future {
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
      val stateHistory = new ExecutionTree()
      val ctx = new Context()
      val executor = new SymbolicExecutor(cfg, searchStrategy = new RandomPathSelectionStrategy(stateHistory), executionTree = Some(stateHistory))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }
  }


  test("random generated test finishes with no error4") {
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



    val future = Future {
      val program = parseUnsafe(code)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)

      val stateHistory = new ExecutionTree()
      val executor = new SymbolicExecutor(cfg, searchStrategy = new RandomPathSelectionStrategy(stateHistory), executionTree = Some(stateHistory))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }
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


    val future = Future {
      val program = parseUnsafe(code)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)
      val stateHistory = new ExecutionTree()
      val tree = new RandomPathSelectionStrategy(stateHistory)

      val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }

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
    val stateHistory = new ExecutionTree()
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



  test("nasty summarization test3") {
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
    val stateHistory = new ExecutionTree()
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
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26,var27,var28;
        |  var6 = 8;
        |  var9 = {JeCvhXKPDz:alloc 4,nNSFVWEsja:6,MwOUwVqkbH:alloc 4,ZZhiKJdlch:2};
        |  var11 = 0;
        |  var28 = [7,3,-1,8,0,-1,-1,8];
        |  while (input) {
        |    while ((var11 < var6)) {
        |      var28 = var28;
        |      if (var9.ZZhiKJdlch) {
        |
        |      }
        |      var11 = (var11 + 1);
        |    }
        |    var28[5] = input;
        |  }
        |  return 0;
        |}
        |
        |""".stripMargin

    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program)
    val stateHistory = new ExecutionTree()
    val tree = new RandomPathSelectionStrategy(stateHistory)

    val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
    executor.run()


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



    val future = Future {
      val program = parseUnsafe(code)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)
      val stateHistory = new ExecutionTree()
      val tree = new RandomPathSelectionStrategy(stateHistory)

      val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }
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

    val future = Future {
      val program = parseUnsafe(code)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)
      val stateHistory = new ExecutionTree()
      val tree = new RandomPathSelectionStrategy(stateHistory)

      val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }

  }


  test("nasty summarization test7") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26,var27;
        |  var0 = 8;
        |  var1 = alloc 1;
        |  var2 = 6;
        |  var3 = 2;
        |  var4 = alloc alloc 6;
        |  var5 = {ZqemmtvlFK:0};
        |  var6 = alloc alloc alloc 8;
        |  var7 = {spAGlOQptt:1};
        |  var8 = 4;
        |  var9 = alloc alloc 8;
        |  var10 = 4;
        |  var11 = 0;
        |  var12 = 0;
        |  var13 = alloc alloc 2;
        |  var14 = [alloc alloc 4,alloc alloc 2,alloc alloc 8,alloc alloc 8,alloc alloc 8,alloc alloc 7,alloc alloc 6,alloc alloc 5,alloc alloc 0];
        |  var15 = 1;
        |  var16 = 2;
        |  var17 = alloc 2;
        |  var18 = 6;
        |  var19 = 3;
        |  var20 = 7;
        |  var21 = 8;
        |  var22 = 3;
        |  var23 = alloc alloc 3;
        |  var24 = alloc alloc 1;
        |  var25 = -1;
        |  var26 = 1;
        |  var27 = [4,7,5,-1,7];
        |  while (input) {
        |    while (var7.spAGlOQptt) {
        |      while ((var22 < var3)) {
        |        if (!var5.ZqemmtvlFK) {
        |          while ((var26 < var12)) {
        |            while ((var11 < var0)) {
        |              var17 = alloc 2;
        |              output input;
        |              var18 = 7;
        |              var11 = (var11 + 1);
        |            }
        |            var26 = (var26 + 1);
        |          }
        |          while (var12) {
        |            while ((var12 < var26)) {
        |              output var2;
        |              var12 = (var12 + 1);
        |            }
        |            while ((var15 < var11)) {
        |              var15 = (var15 + 1);
        |            }
        |          }
        |        } else {
        |          while (var5.ZqemmtvlFK) {
        |            var27 = [5,0,1,1,2,8,2];
        |            while (4) {
        |              var16 = 1;
        |              output !input;
        |              output 3;
        |            }
        |            var20 = 3;
        |            while ((var25 < var21)) {
        |              var9 = alloc alloc 2;
        |              var25 = (var25 + 1);
        |            }
        |          }
        |          var15 = !0;
        |          while (!6) {
        |            output 5;
        |          }
        |          while ((var3 < var3)) {
        |            while ((var3 < var21)) {
        |              var3 = (var3 + 1);
        |            }
        |            var3 = (var3 + 1);
        |          }
        |        }
        |        var22 = (var22 + 1);
        |      }
        |      while ((var26 < var11)) {
        |        while ((var12 < var16)) {
        |          var12 = (var12 + 1);
        |        }
        |        var26 = (var26 + 1);
        |      }
        |      while ((var18 < var15)) {
        |        while ((var8 < var0)) {
        |          while (var22) {
        |            while ((var2 < var21)) {
        |              output input;
        |              var27 = [6,4,5,6,-1,8,1,8];
        |              var2 = (var2 + 1);
        |            }
        |            while ((var10 < var0)) {
        |              var6 = alloc alloc alloc 0;
        |              output input;
        |              var10 = (var10 + 1);
        |            }
        |          }
        |          output input;
        |          var8 = (var8 + 1);
        |        }
        |        var18 = (var18 + 1);
        |      }
        |      var27[1] = input;
        |    }
        |    while ((var8 < var26)) {
        |      var14[1] = var23;
        |      if (var20) {
        |        while ((var0 < var15)) {
        |          while ((var21 < var20)) {
        |            var21 = (var21 + 1);
        |          }
        |          while ((var3 < var26)) {
        |            while ((var19 < var12)) {
        |              var2 = 8;
        |              output var5.ZqemmtvlFK;
        |              var10 = 3;
        |              var7 = {spAGlOQptt:4};
        |              var19 = (var19 + 1);
        |            }
        |            output 1;
        |            var3 = (var3 + 1);
        |          }
        |          while ((var15 < var11)) {
        |            while ((var20 < var11)) {
        |              output var25;
        |              var12 = 0;
        |              var24 = alloc alloc 5;
        |              output 9;
        |              var20 = (var20 + 1);
        |            }
        |            while ((var2 < var0)) {
        |              var15 = 2;
        |              var15 = 3;
        |              var25 = 2;
        |              var2 = (var2 + 1);
        |            }
        |            var15 = (var15 + 1);
        |          }
        |          var0 = (var0 + 1);
        |        }
        |        output !!7;
        |        while ((var3 < var18)) {
        |          while ((var21 < var22)) {
        |            var21 = (var21 + 1);
        |          }
        |          var27[3] = 9;
        |          while ((var19 < var25)) {
        |            var19 = (var19 + 1);
        |          }
        |          while ((var10 < var25)) {
        |            while (5) {}
        |            while ((var10 < var11)) {
        |              var26 = 2;
        |              var10 = (var10 + 1);
        |            }
        |            var10 = (var10 + 1);
        |          }
        |          var3 = (var3 + 1);
        |        }
        |      } else {
        |        if (var5.ZqemmtvlFK) {
        |          while ((var12 < var3)) {
        |            var12 = (var12 + 1);
        |          }
        |        } else {
        |          while (!0) {
        |            output 0;
        |            while ((var15 < var19)) {
        |              var15 = (var15 + 1);
        |            }
        |            while ((var21 < var19)) {
        |              var21 = (var21 + 1);
        |            }
        |            while ((var22 < var8)) {
        |              var22 = (var22 + 1);
        |            }
        |          }
        |        }
        |        output !0;
        |      }
        |      while ((var19 < var12)) {
        |        while ((var15 < var25)) {
        |          var15 = (var15 + 1);
        |        }
        |        while ((var16 < var26)) {
        |          while (7) {
        |            while (5) {}
        |            while (2) {
        |              output 4;
        |              var9 = alloc alloc -1;
        |              output 0;
        |            }
        |            while ((var22 < var20)) {
        |              output input;
        |              var19 = 0;
        |              output !input;
        |              var22 = (var22 + 1);
        |            }
        |            while ((var20 < var3)) {
        |              var24 = alloc alloc 6;
        |              output !input;
        |              output 9;
        |              var2 = 7;
        |              var20 = (var20 + 1);
        |            }
        |          }
        |          var16 = (var16 + 1);
        |        }
        |        while ((var12 < var0)) {
        |          while ((var20 < var19)) {
        |            while ((var21 < var0)) {
        |              var21 = (var21 + 1);
        |            }
        |            var20 = (var20 + 1);
        |          }
        |          var12 = (var12 + 1);
        |        }
        |        var27[4] = input;
        |        var19 = (var19 + 1);
        |      }
        |      var8 = (var8 + 1);
        |    }
        |    while ((var12 < var26)) {
        |      var12 = (var12 + 1);
        |    }
        |    var27[0] = var3;
        |  }
        |  while ((var21 < var12)) {
        |    output !6;
        |    if (input) {
        |      output var7.spAGlOQptt;
        |    } else {
        |      while ((var18 < var10)) {
        |        while ((var19 < var20)) {
        |          while ((var11 < var10)) {
        |            var11 = (var11 + 1);
        |          }
        |          var19 = (var19 + 1);
        |        }
        |        output input;
        |        var18 = (var18 + 1);
        |      }
        |      output 7;
        |      var1 = var17;
        |    }
        |    output !0;
        |    var21 = (var21 + 1);
        |  }
        |  return var5.ZqemmtvlFK;
        |}
        |
        |""".stripMargin

    val future = Future {
      val program = parseUnsafe(code)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)
      val stateHistory = new ExecutionTree()
      val tree = new RandomPathSelectionStrategy(stateHistory)

      val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }

  }


  test("nasty summarization test8") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22;
        |  var0 = -1;
        |  var1 = 0;
        |  var2 = 6;
        |  var3 = alloc 4;
        |  var4 = -1;
        |  var5 = 6;
        |  var6 = 3;
        |  var7 = [6,6,-1,4,0,4,2,8];
        |  var8 = alloc 1;
        |  var9 = alloc [4,0,7,0,7,4];
        |  var10 = 2;
        |  var11 = alloc 6;
        |  var12 = 5;
        |  var13 = alloc alloc 5;
        |  var14 = 4;
        |  var15 = 1;
        |  var16 = 7;
        |  var17 = 4;
        |  var18 = 3;
        |  var19 = alloc 1;
        |  var20 = {PUmklaIsxS:[alloc alloc -1,alloc alloc 6,alloc alloc 6,alloc alloc -1,alloc alloc -1,alloc alloc 5,alloc alloc 6,alloc alloc 8],uaavJKDWut:-1,VVJzmtSVQb:[alloc [5,0,6,8,2],alloc [5,2,0,8,1],alloc [-1,3,0,3,6,0,1,1,4],alloc [3,-1,4,8,6],alloc [7,6,8,0,3,6,1,-1,4]]};
        |  var21 = alloc 5;
        |  var22 = [0,-1,-1,6,1,8,5,6];
        |  var22[4] = var7[1];
        |  while ((var14 < var16)) {
        |    if (input) {} else {
        |      var7[4] = var22[5];
        |      while (!input) {
        |        while ((var0 < var15)) {
        |          if (var0) {
        |            while ((var18 < var17)) {
        |              output (input * var20.uaavJKDWut);
        |              var20 = {PUmklaIsxS:[alloc alloc 5,alloc alloc 6,alloc alloc -1,alloc alloc 7,alloc alloc 3,alloc alloc 4],uaavJKDWut:5,VVJzmtSVQb:[alloc [-1,8,3,-1,4,2,3,1],alloc [3,6,8,0,7,4,8,5,-1],alloc [3,-1,8,5,5,4,0,1],alloc [3,6,0,1,-1],alloc [7,7,4,7,2,4,7,2,7],alloc [6,5,8,8,4,7,1,1],alloc [6,-1,4,-1,4],alloc [6,0,5,-1,4]]};
        |              var18 = (var18 + 1);
        |            }
        |            while ((var12 < var0)) {
        |              output var22[1];
        |              var22 = [3,8,5,4,7,0];
        |              var12 = (var12 + 1);
        |            }
        |            if (6) {
        |              var7 = [2,7,1,5,5];
        |              output !!input;
        |            } else {
        |              output !var12;
        |              output var7[3];
        |            }
        |          } else {
        |            while ((var0 < var14)) {
        |              var0 = 7;
        |              var0 = (var0 + 1);
        |            }
        |            var18 = 0;
        |            var19 = alloc 1;
        |          }
        |          var7[0] = [5,6,6,0,-1,7,0][3];
        |          while (input) {
        |            output 1;
        |            while ((var2 < var1)) {
        |              output input;
        |              output input;
        |              var2 = (var2 + 1);
        |            }
        |            while ((var2 < var18)) {
        |              output var20.uaavJKDWut;
        |              var2 = (var2 + 1);
        |            }
        |          }
        |          var0 = (var0 + 1);
        |        }
        |        while ((var0 < var10)) {
        |          while ((var2 < var17)) {
        |            while (7) {
        |              var6 = 5;
        |              output var17;
        |              var4 = 2;
        |              output var12;
        |            }
        |            var2 = (var2 + 1);
        |          }
        |          var7[7] = var20.uaavJKDWut;
        |          var0 = (var0 + 1);
        |        }
        |        while (var20.uaavJKDWut) {
        |          while ((var4 < var5)) {
        |            while (-1) {
        |              var11 = alloc 4;
        |              var0 = 4;
        |            }
        |            while (3) {
        |              output (!var22[1] + input);
        |              var8 = alloc 5;
        |              output var14;
        |              output input;
        |            }
        |            while (3) {
        |              var15 = -1;
        |              var14 = 1;
        |              output input;
        |            }
        |            while ((var17 < var16)) {
        |              output (var20.uaavJKDWut + !(!var7[7] - var5));
        |              var17 = (var17 + 1);
        |            }
        |            var4 = (var4 + 1);
        |          }
        |        }
        |        while ((var0 < var14)) {
        |          while (var4) {
        |            while ((var18 < var15)) {
        |              var8 = alloc 8;
        |              var22 = [1,-1,1,7,-1,1,4];
        |              var18 = (var18 + 1);
        |            }
        |          }
        |          var0 = (var0 + 1);
        |        }
        |      }
        |      while (!var22[6]) {}
        |    }
        |    var14 = (var14 + 1);
        |  }
        |  if (!var12) {
        |    while (var1) {
        |      while (var2) {
        |        while ((var2 < var18)) {
        |          var2 = (var2 + 1);
        |        }
        |      }
        |      while ((var16 < var15)) {
        |        output var20.uaavJKDWut;
        |        while ((var4 < var2)) {
        |          while (input) {
        |            var20 = {PUmklaIsxS:[alloc alloc 7,alloc alloc 2,alloc alloc -1,alloc alloc 3,alloc alloc 8,alloc alloc 7,alloc alloc 0,alloc alloc -1],uaavJKDWut:2,VVJzmtSVQb:[alloc [7,2,4,-1,4,4,4,3,6],alloc [6,8,8,8,7],alloc [4,1,7,0,4],alloc [1,8,5,6,5,-1,2],alloc [4,-1,8,1,7,7,0],alloc [4,0,0,5,6,7],alloc [3,4,5,1,2,0,3,4],alloc [1,2,0,1,-1]]};
        |            while ((var4 < var18)) {
        |              var11 = alloc 4;
        |              output input;
        |              var4 = (var4 + 1);
        |            }
        |            while (3) {
        |              output var22[5];
        |            }
        |            output 1;
        |          }
        |          while (var20.uaavJKDWut) {
        |            while ((var5 < var15)) {
        |              var5 = (var5 + 1);
        |            }
        |            if (8) {
        |              var12 = 8;
        |              output var20.uaavJKDWut;
        |              var14 = 3;
        |              output var20.uaavJKDWut;
        |            } else {
        |              var20 = {PUmklaIsxS:[alloc alloc 1,alloc alloc 1,alloc alloc 0,alloc alloc 5,alloc alloc 0,alloc alloc -1,alloc alloc 3,alloc alloc 5,alloc alloc 5],uaavJKDWut:2,VVJzmtSVQb:[alloc [8,1,8,7,3],alloc [7,6,5,7,4,4,1],alloc [4,5,2,-1,7],alloc [3,4,-1,3,8,3,-1,0,4],alloc [2,-1,0,5,5,3,0,5,3],alloc [0,7,1,4,6,8]]};
        |              output input;
        |            }
        |            while (5) {
        |              var2 = 5;
        |            }
        |            while ((var6 < var16)) {
        |              output var6;
        |              var3 = alloc 1;
        |              var19 = alloc 4;
        |              output input;
        |              var6 = (var6 + 1);
        |            }
        |          }
        |          var4 = (var4 + 1);
        |        }
        |        while ((var0 < var6)) {
        |          while ((var12 < var5)) {
        |            var12 = (var12 + 1);
        |          }
        |          while ((var0 < var5)) {
        |            var7[7] = 4;
        |            output 7;
        |            var0 = (var0 + 1);
        |          }
        |          while ([1,-1,5,4,1,0][3]) {
        |            while ((var1 < var17)) {
        |              var1 = (var1 + 1);
        |            }
        |          }
        |          while ((var10 < var18)) {
        |            var10 = (var10 + 1);
        |          }
        |          var0 = (var0 + 1);
        |        }
        |        var16 = (var16 + 1);
        |      }
        |    }
        |    while (var14) {
        |      if (input) {
        |        while ((var6 < var5)) {
        |          while (var20.uaavJKDWut) {}
        |          var6 = (var6 + 1);
        |        }
        |        while ((var16 < var5)) {
        |          var7[1] = (3 * 7);
        |          var16 = (var16 + 1);
        |        }
        |        while (input) {
        |          while ((var6 < var10)) {
        |            var22[1] = 5;
        |            output 1;
        |            var6 = (var6 + 1);
        |          }
        |          while ((var6 < var17)) {
        |            if (3) {
        |              output var7[4];
        |              output var20.uaavJKDWut;
        |              output (var7[7] * (input - input));
        |              var21 = alloc 0;
        |            } else {
        |              output input;
        |            }
        |            while ((var18 < var14)) {
        |              var18 = (var18 + 1);
        |            }
        |            while (0) {
        |              var20 = {PUmklaIsxS:[alloc alloc 4,alloc alloc 3,alloc alloc 3,alloc alloc 2,alloc alloc 4,alloc alloc -1,alloc alloc 2,alloc alloc 8],uaavJKDWut:2,VVJzmtSVQb:[alloc [7,2,5,0,7,1,4,5,7],alloc [7,-1,5,3,0,5],alloc [3,3,2,2,2,4,8],alloc [0,3,8,2,7],alloc [-1,-1,6,2,3,6,1,0,6],alloc [5,8,-1,7,0,7,5,6],alloc [4,4,5,0,4,2,-1],alloc [3,4,-1,0,0,8],alloc [6,8,0,4,6,2,0]]};
        |              output input;
        |            }
        |            var6 = (var6 + 1);
        |          }
        |        }
        |      } else {
        |        while ((var6 < var14)) {
        |          while ((var18 < var4)) {
        |            var18 = (var18 + 1);
        |          }
        |          while ((var2 < var0)) {
        |            output 7;
        |            var2 = (var2 + 1);
        |          }
        |          var6 = (var6 + 1);
        |        }
        |      }
        |    }
        |    while ((var0 < var14)) {
        |      var1 = var22[3];
        |      var0 = (var0 + 1);
        |    }
        |    while ((var15 < var6)) {
        |      var15 = (var15 + 1);
        |    }
        |  } else {
        |    if (input) {} else {
        |      while ((var4 < var16)) {
        |        while ((var12 < var0)) {
        |          while ((var6 < var14)) {
        |            var6 = (var6 + 1);
        |          }
        |          while (!4) {}
        |          var12 = (var12 + 1);
        |        }
        |        while ((var10 < var18)) {
        |          if ((0 + 6)) {
        |            while (7) {
        |              var14 = 7;
        |              var20 = {PUmklaIsxS:[alloc alloc 4,alloc alloc 8,alloc alloc 0,alloc alloc 3,alloc alloc -1,alloc alloc -1,alloc alloc 8],uaavJKDWut:-1,VVJzmtSVQb:[alloc [6,2,8,5,-1,4,8,5,-1],alloc [0,4,5,7,4,2,8,8,3],alloc [8,0,0,2,0,3,1,8],alloc [7,0,8,5,6,6,2],alloc [0,8,8,2,-1,7,1,0,3],alloc [7,4,1,4,4,7],alloc [0,3,6,4,5,4,1,3,4]]};
        |            }
        |            while (5) {
        |              output input;
        |              output var22[0];
        |            }
        |            var0 = 5;
        |          } else {
        |            while ((var15 < var16)) {
        |              var15 = (var15 + 1);
        |            }
        |            var22[5] = 5;
        |            while ((var5 < var14)) {
        |              var5 = (var5 + 1);
        |            }
        |          }
        |          var10 = (var10 + 1);
        |        }
        |        while ((var5 < var2)) {
        |          var12 = var1;
        |          while ((var15 < var4)) {
        |            var15 = (var15 + 1);
        |          }
        |          while ((var0 < var2)) {
        |            while ((var5 < var17)) {
        |              var5 = (var5 + 1);
        |            }
        |            while (7) {
        |              var14 = 4;
        |              output input;
        |            }
        |            var0 = (var0 + 1);
        |          }
        |          var5 = (var5 + 1);
        |        }
        |        while ((var12 + input)) {
        |          if (var20.uaavJKDWut) {
        |            while ((var12 < var12)) {
        |              output !var7[6];
        |              var11 = alloc 6;
        |              var12 = (var12 + 1);
        |            }
        |            while ((var15 < var18)) {
        |              var14 = 7;
        |              var20 = {PUmklaIsxS:[alloc alloc 1,alloc alloc 1,alloc alloc 7,alloc alloc 0,alloc alloc 6],uaavJKDWut:7,VVJzmtSVQb:[alloc [1,1,5,2,7,7,7],alloc [0,-1,-1,7,2,8],alloc [3,1,-1,7,-1,7,8,6],alloc [5,7,0,-1,3],alloc [8,1,6,7,8,1,5],alloc [0,7,5,-1,7],alloc [1,3,0,8,0,8,5],alloc [3,4,6,1,-1,0,3,3,-1],alloc [3,7,4,1,5,4,8]]};
        |              var13 = alloc alloc 6;
        |              output (input * input);
        |              var15 = (var15 + 1);
        |            }
        |          } else {
        |            while ((var18 < var2)) {
        |              output var12;
        |              var5 = -1;
        |              var18 = (var18 + 1);
        |            }
        |            while ((var12 < var5)) {
        |              var15 = 7;
        |              var6 = -1;
        |              var12 = (var12 + 1);
        |            }
        |          }
        |          var0 = var20.uaavJKDWut;
        |          var22[2] = var20.uaavJKDWut;
        |        }
        |        var4 = (var4 + 1);
        |      }
        |      var4 = !input;
        |      while ((var18 < var4)) {
        |        output var10;
        |        output input;
        |        while ((var2 < var14)) {
        |          output [3,3,7,0,6][0];
        |          while ((var4 < var12)) {
        |            while ((var5 < var17)) {
        |              output var7[6];
        |              output var20.uaavJKDWut;
        |              var5 = (var5 + 1);
        |            }
        |            while ((var16 < var10)) {
        |              var6 = 8;
        |              var7 = [2,8,5,0,5];
        |              var16 = (var16 + 1);
        |            }
        |            var7[0] = -1;
        |            var4 = (var4 + 1);
        |          }
        |          var2 = (var2 + 1);
        |        }
        |        var22[0] = (!8 + var15);
        |        var18 = (var18 + 1);
        |      }
        |      while ((var1 < var16)) {
        |        var1 = (var1 + 1);
        |      }
        |    }
        |    while ((var0 < var15)) {
        |      while ((var16 < var12)) {
        |        while (var20.uaavJKDWut) {
        |          output var20.uaavJKDWut;
        |          while ((var4 < var4)) {
        |            while ((var4 < var4)) {
        |              output !!var22[1];
        |              var4 = (var4 + 1);
        |            }
        |            output 2;
        |            while ((var18 < var17)) {
        |              output input;
        |              output (!input + var22[1]);
        |              output (input - var20.uaavJKDWut);
        |              output input;
        |              var18 = (var18 + 1);
        |            }
        |            var4 = (var4 + 1);
        |          }
        |        }
        |        var16 = (var16 + 1);
        |      }
        |      var0 = (var0 + 1);
        |    }
        |    while ((var14 < var12)) {
        |      while ((var1 < var6)) {
        |        while ((var0 < var16)) {
        |          var7[6] = !0;
        |          if ((1 + 4)) {
        |            while ((var14 < var4)) {
        |              output input;
        |              output var22[6];
        |              output (!!input - var0);
        |              var14 = (var14 + 1);
        |            }
        |          } else {
        |            while (8) {
        |              output !var20.uaavJKDWut;
        |              output input;
        |              var17 = 0;
        |              var8 = alloc 7;
        |            }
        |          }
        |          var0 = (var0 + 1);
        |        }
        |        var1 = (var1 + 1);
        |      }
        |      var1 = input;
        |      var14 = (var14 + 1);
        |    }
        |    output input;
        |  }
        |  while ((var18 < var0)) {
        |    while (input) {
        |      while (input) {
        |        var3 = &var12;
        |      }
        |      while ((var5 < var10)) {
        |        while ((var4 < var14)) {
        |          while ((var4 < var6)) {
        |            while ((var1 < var4)) {
        |              output !((var6 * var20.uaavJKDWut) - !(var22[0] * var10));
        |              output input;
        |              var1 = (var1 + 1);
        |            }
        |            while ((var14 < var12)) {
        |              var14 = (var14 + 1);
        |            }
        |            while (-1) {
        |              var14 = 0;
        |              var5 = -1;
        |              output var20.uaavJKDWut;
        |            }
        |            while ((var1 < var1)) {
        |              var1 = (var1 + 1);
        |            }
        |            var4 = (var4 + 1);
        |          }
        |          while ((var17 < var12)) {
        |            if (2) {
        |              var13 = alloc alloc 8;
        |              output input;
        |            } else {}
        |            if (4) {
        |              var4 = 3;
        |              output var20.uaavJKDWut;
        |              var12 = 0;
        |            } else {
        |              var13 = alloc alloc 1;
        |            }
        |            while ((var14 < var16)) {
        |              output input;
        |              var14 = (var14 + 1);
        |            }
        |            output 7;
        |            var17 = (var17 + 1);
        |          }
        |          var4 = (var4 + 1);
        |        }
        |        while ((var5 < var1)) {
        |          var5 = (var5 + 1);
        |        }
        |        var5 = (var5 + 1);
        |      }
        |      output (input * input);
        |      output input;
        |    }
        |    while ((var18 < var0)) {
        |      while (var15) {
        |        while (input) {
        |          while (input) {
        |            output 2;
        |            while ((var15 < var14)) {
        |              var16 = 5;
        |              var16 = 3;
        |              var15 = (var15 + 1);
        |            }
        |            var22[7] = 7;
        |          }
        |        }
        |        while ((var15 < var1)) {
        |          var15 = (var15 + 1);
        |        }
        |        while ((var2 < var14)) {
        |          while ((var5 < var15)) {
        |            while ((var17 < var10)) {
        |              output var22[7];
        |              var14 = -1;
        |              var17 = (var17 + 1);
        |            }
        |            while ((var10 < var16)) {
        |              var10 = (var10 + 1);
        |            }
        |            while (1) {}
        |            var5 = (var5 + 1);
        |          }
        |          while ((var18 < var10)) {
        |            while ((var18 < var15)) {
        |              var19 = alloc -1;
        |              var18 = (var18 + 1);
        |            }
        |            var12 = 2;
        |            var18 = (var18 + 1);
        |          }
        |          var2 = (var2 + 1);
        |        }
        |        var22[5] = var22[4];
        |      }
        |      var18 = (var18 + 1);
        |    }
        |    output var20.uaavJKDWut;
        |    while ((var18 < var1)) {
        |      while ((var17 < var16)) {
        |        while ((var16 < var16)) {
        |          while ((var12 < var12)) {
        |            while (8) {
        |              output ((var20.uaavJKDWut * !var20.uaavJKDWut) - input);
        |              var22 = [8,5,8,6,-1];
        |            }
        |            while ((var14 < var6)) {
        |              var8 = alloc 8;
        |              output (var20.uaavJKDWut * var20.uaavJKDWut);
        |              var21 = alloc 8;
        |              var14 = (var14 + 1);
        |            }
        |            var12 = (var12 + 1);
        |          }
        |          if (input) {} else {}
        |          var16 = (var16 + 1);
        |        }
        |        while ((var18 < var14)) {
        |          var12 = (0 * 2);
        |          while ((var2 < var14)) {
        |            var2 = (var2 + 1);
        |          }
        |          while ((var2 < var1)) {
        |            while (6) {
        |              var6 = 3;
        |            }
        |            var2 = (var2 + 1);
        |          }
        |          while ((var15 < var15)) {
        |            while ((var18 < var14)) {
        |              var18 = (var18 + 1);
        |            }
        |            var17 = -1;
        |            output 4;
        |            var15 = (var15 + 1);
        |          }
        |          var18 = (var18 + 1);
        |        }
        |        var17 = (var17 + 1);
        |      }
        |      if (input) {
        |        if (input) {} else {
        |          while ((var15 < var2)) {
        |            var7[3] = 8;
        |            while ((var17 < var14)) {
        |              output var7[4];
        |              output !var17;
        |              var2 = -1;
        |              var17 = (var17 + 1);
        |            }
        |            while (2) {
        |              output var5;
        |              output input;
        |            }
        |            while (2) {
        |              output var7[6];
        |              output var6;
        |              var12 = 4;
        |            }
        |            var15 = (var15 + 1);
        |          }
        |          while ((var5 < var15)) {
        |            var5 = (var5 + 1);
        |          }
        |          output !1;
        |          var22[7] = var20.uaavJKDWut;
        |        }
        |        while ((var14 < var15)) {
        |          while ((var12 < var18)) {
        |            while ((var15 < var18)) {
        |              var8 = alloc 7;
        |              output input;
        |              output input;
        |              var15 = (var15 + 1);
        |            }
        |            while (7) {
        |              var16 = -1;
        |              var0 = 8;
        |              output input;
        |              var2 = 6;
        |            }
        |            var12 = (var12 + 1);
        |          }
        |          while ((var6 < var2)) {
        |            while ((var17 < var1)) {
        |              output !input;
        |              output input;
        |              var17 = (var17 + 1);
        |            }
        |            while ((var1 < var4)) {
        |              output input;
        |              var1 = (var1 + 1);
        |            }
        |            while ((var4 < var5)) {
        |              output (input * (input * input));
        |              output (var7[4] - !var7[2]);
        |              var11 = alloc 0;
        |              var4 = (var4 + 1);
        |            }
        |            while ((var15 < var2)) {
        |              var5 = 0;
        |              var15 = (var15 + 1);
        |            }
        |            var6 = (var6 + 1);
        |          }
        |          if (input) {} else {}
        |          while ((var16 < var6)) {
        |            var4 = 7;
        |            while ((var17 < var5)) {
        |              var17 = (var17 + 1);
        |            }
        |            var12 = 2;
        |            var16 = (var16 + 1);
        |          }
        |          var14 = (var14 + 1);
        |        }
        |        while ((var16 < var2)) {
        |          var16 = (var16 + 1);
        |        }
        |      } else {
        |        var17 = (!0 * input);
        |      }
        |      output var22[3];
        |      var6 = var1;
        |      var18 = (var18 + 1);
        |    }
        |    var18 = (var18 + 1);
        |  }
        |  return var7[4];
        |}
        |
        |""".stripMargin
    val future = Future {
      val program = parseUnsafe(code)
      val cfg = new IntraproceduralCfgFactory().fromProgram(program)
      val stateHistory = new ExecutionTree()
      val tree = new RandomPathSelectionStrategy(stateHistory)

      val executor = new LoopSummarization(cfg, searchStrategy = tree, stateHistory = Some(stateHistory))
      executor.run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }

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


    val future = Future {
      val program = parseUnsafe(code)

      new SymbolicExecutorFactory(false, false, Some("aggresive"), 5, 5, "tree").get(program).run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }

  }


  test("random factory test2") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22;
        |  var0 = 0;
        |  var1 = alloc 3;
        |  var2 = 4;
        |  var3 = {KrdRjIpsXz:6,cULmqjOLdc:alloc 8,GZalvKWqZl:alloc alloc -1,sZATslPPrs:4,qxIoQWtvcJ:[0,-1,1,0,0]};
        |  var4 = 2;
        |  var5 = 1;
        |  var6 = alloc alloc 3;
        |  var7 = 7;
        |  var8 = 4;
        |  var9 = 5;
        |  var10 = alloc alloc -1;
        |  var11 = 2;
        |  var12 = -1;
        |  var13 = alloc alloc alloc 1;
        |  var14 = alloc 2;
        |  var15 = 8;
        |  var16 = 4;
        |  var17 = {YObdYDaech:[3,7,-1,1,3,6],vKJkDditvP:alloc 6};
        |  var18 = [6,7,-1,-1,3,8,3,7];
        |  var19 = -1;
        |  var20 = 7;
        |  var21 = 3;
        |  var22 = [8,4,-1,2,-1,8];
        |  if (var18[5]) {
        |    var18[0] = var3.KrdRjIpsXz;
        |  } else {}
        |  if (var18[7]) {} else {
        |    if (var18[0]) {
        |      output !input;
        |    } else {
        |      output var3.sZATslPPrs;
        |      var20 = var22[1];
        |      output var0;
        |    }
        |    while (var3.sZATslPPrs) {}
        |    while ((var19 < var9)) {
        |      while (var12) {
        |        var18[7] = var3.KrdRjIpsXz;
        |        output var18[4];
        |      }
        |      var9 = !input;
        |      while ((var0 < var15)) {
        |        output input;
        |        var0 = (var0 + 1);
        |      }
        |      if (input) {
        |        if (var18[1]) {
        |          var14 = alloc 0;
        |        } else {
        |          output input;
        |          output (input - var3.KrdRjIpsXz);
        |          output input;
        |        }
        |        while (input) {}
        |        while (((0 - 6) + [1,3,6,4,7][3])) {
        |          output input;
        |          var0 = var3.KrdRjIpsXz;
        |        }
        |        var14 = var1;
        |      } else {}
        |      var19 = (var19 + 1);
        |    }
        |    while ((var15 < var8)) {
        |      var15 = (var15 + 1);
        |    }
        |  }
        |  var22[1] = input;
        |  var17 = var17;
        |  var16 = var3.sZATslPPrs;
        |  if (var3.sZATslPPrs) {
        |    if (!var5) {
        |      if (var3.sZATslPPrs) {} else {}
        |      var7 = var9;
        |    } else {
        |      output input;
        |      if ((((4 - -1) - input) - input)) {
        |        while (var3.sZATslPPrs) {
        |          var0 = !1;
        |          output var18[7];
        |        }
        |        if (var3.KrdRjIpsXz) {
        |          output (input - input);
        |          var22 = var22;
        |          output input;
        |        } else {
        |          var13 = &var6;
        |          var14 = alloc 0;
        |          output input;
        |          var14 = var1;
        |        }
        |      } else {}
        |    }
        |    while ((var22[4] + (!input + var22[5]))) {
        |      var6 = &var14;
        |      if (input) {
        |        var22[3] = input;
        |        while ((var11 < var20)) {
        |          var0 = var3.sZATslPPrs;
        |          output input;
        |          var11 = (var11 + 1);
        |        }
        |        while ((var11 < var7)) {
        |          output var3.sZATslPPrs;
        |          var11 = (var11 + 1);
        |        }
        |        output var3.KrdRjIpsXz;
        |      } else {
        |        while (var11) {}
        |        var5 = var2;
        |      }
        |    }
        |    output !input;
        |  } else {}
        |  return (input + var20);
        |}
        |""".stripMargin



    val future = Future {
      val program = parseUnsafe(code)

      new SymbolicExecutorFactory(false, false, None, 5, 5, "klee").get(program).run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }

  }


  test("random factory test 3") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23;
        |  var0 = 0;
        |  var1 = 7;
        |  var2 = -1;
        |  var3 = alloc 8;
        |  var4 = 1;
        |  var5 = -1;
        |  var6 = 5;
        |  var7 = 5;
        |  var8 = alloc alloc 5;
        |  var9 = {IlLgXvdtWf:-1,rvGQCbJavr:[4,6,8,3,3],WIJjEDahpZ:alloc 6};
        |  var10 = 6;
        |  var11 = alloc 0;
        |  var12 = alloc 0;
        |  var13 = 4;
        |  var14 = alloc 4;
        |  var15 = -1;
        |  var16 = 5;
        |  var17 = alloc 7;
        |  var18 = -1;
        |  var19 = [alloc 3,alloc 3,alloc -1,alloc 6,alloc 7];
        |  var20 = alloc alloc 7;
        |  var21 = 0;
        |  var22 = {OjgoxaosnM:-1,nufdKxRylg:7,pFGMQIQZCG:3};
        |  var23 = [8,0,7,4,5,1,1,8];
        |  var20 = alloc alloc input;
        |  var23[2] = (input + (!!input - var22.pFGMQIQZCG));
        |  if (input) {
        |    if (!7) {} else {
        |      var4 = (var22.nufdKxRylg - var2);
        |      if (var22.nufdKxRylg) {
        |        output input;
        |      } else {
        |        var19[1] = alloc var22.pFGMQIQZCG;
        |        var19[4] = &var5;
        |        if ((6 * input)) {
        |          if ((3 - 8)) {
        |            var19[1] = alloc 6;
        |            var5 = 5;
        |            var1 = 8;
        |          } else {
        |            var19[3] = alloc 5;
        |            if (0) {
        |              output var9.IlLgXvdtWf;
        |              output (input * input);
        |              output 4;
        |              output input;
        |            } else {}
        |          }
        |          output !4;
        |          var3 = &var1;
        |        } else {
        |          var10 = !0;
        |          output input;
        |        }
        |        while ((var16 < var21)) {
        |          var16 = (var16 + 1);
        |        }
        |      }
        |    }
        |  } else {
        |    var23 = var23;
        |    while ((var18 < var2)) {
        |      var18 = (var18 + 1);
        |    }
        |    while (!var10) {
        |      var17 = &var6;
        |    }
        |    var23 = var23;
        |  }
        |  while ((var1 < var21)) {
        |    while (input) {
        |      while (var10) {
        |        output !input;
        |        output input;
        |        var0 = !!-1;
        |      }
        |      output input;
        |      if (var9.IlLgXvdtWf) {
        |        while (var22.OjgoxaosnM) {
        |          var4 = var22.nufdKxRylg;
        |        }
        |        if (!var22.nufdKxRylg) {} else {
        |          var17 = &var0;
        |          var3 = var12;
        |          var10 = input;
        |        }
        |        output var22.nufdKxRylg;
        |      } else {}
        |    }
        |    if (var22.pFGMQIQZCG) {} else {
        |      var20 = &var14;
        |      output var10;
        |      var11 = var14;
        |    }
        |    var1 = (var1 + 1);
        |  }
        |  var17 = alloc input;
        |  if ((input - (input + !input))) {
        |    var19[3] = alloc var22.pFGMQIQZCG;
        |    var19[0] = var11;
        |    if (input) {
        |      var15 = input;
        |      while ((var15 < var5)) {
        |        var16 = var10;
        |        var15 = (var15 + 1);
        |      }
        |      var10 = var22.OjgoxaosnM;
        |      var9 = var9;
        |    } else {
        |      if (input) {} else {
        |        while ((var18 < var16)) {
        |          while (var22.pFGMQIQZCG) {
        |            var19[4] = alloc 8;
        |          }
        |          if (var0) {
        |            if (-1) {
        |              var19 = [alloc 2,alloc -1,alloc 0,alloc 7,alloc 0];
        |              var13 = 3;
        |              output 4;
        |              output var22.pFGMQIQZCG;
        |            } else {}
        |          } else {
        |            if (2) {
        |              var22 = {OjgoxaosnM:6,nufdKxRylg:7,pFGMQIQZCG:6};
        |              output var18;
        |            } else {}
        |            while (2) {
        |              var1 = 5;
        |              var14 = alloc 8;
        |            }
        |          }
        |          while (var22.nufdKxRylg) {
        |            if (6) {
        |              output !var22.pFGMQIQZCG;
        |              var9 = {IlLgXvdtWf:3,rvGQCbJavr:[1,8,3,4,3,5,0],WIJjEDahpZ:alloc 1};
        |              var20 = alloc alloc 4;
        |              var6 = 8;
        |            } else {
        |              output var4;
        |              output 5;
        |              output (var7 - 5);
        |            }
        |          }
        |          output !-1;
        |          var18 = (var18 + 1);
        |        }
        |        while ((var15 < var21)) {
        |          var15 = (var15 + 1);
        |        }
        |        while ((var2 < var18)) {
        |          var2 = (var2 + 1);
        |        }
        |      }
        |      if (6) {
        |        if (var4) {} else {
        |          var23[5] = !4;
        |          output var2;
        |          while ((var6 < var5)) {
        |            while ((var21 < var7)) {
        |              output var22.OjgoxaosnM;
        |              var18 = 7;
        |              var21 = (var21 + 1);
        |            }
        |            var19[1] = alloc 7;
        |            while (5) {
        |              output input;
        |            }
        |            if (2) {} else {}
        |            var6 = (var6 + 1);
        |          }
        |          output var6;
        |        }
        |      } else {}
        |    }
        |    var10 = input;
        |  } else {}
        |  var23[4] = !var13;
        |  output var22.nufdKxRylg;
        |  var13 = var9.IlLgXvdtWf;
        |  return input;
        |}
        |""".stripMargin




    val future = Future {
      val program = parseUnsafe(code)
      new SymbolicExecutorFactory(false, false, Some("querycount"), 1, 5, "tree").get(program).run()
    }

    try {
      Await.ready(future, 5.seconds) // Use Await.result if you need the result of the future
    } catch {
      case _: TimeoutException => println("Test terminated due to timeout")
      case NonFatal(e) => println(s"Test failed due to an unexpected error: ${e.getMessage}")
    }


  }



  test("random factory test 4") {
    val code =
      """
        |main() {
        |  var var0,var1,var2,var3,var4,var5,var6,var7,var8,var9,var10,var11,var12,var13,var14,var15,var16,var17,var18,var19,var20,var21,var22,var23,var24,var25,var26,var27,var28;
        |  var0 = 7;
        |  var4 = 3;
        |  var8 = [7,2,7,0,6];
        |  var11 = 1;
        |  var16 = -1;
        |  var20 = 7;
        |  while (var16) {
        |    while ((var0 < var20)) {
        |      var8 = [3,0,7,0,4];
        |      var0 = (var0 + 1);
        |    }
        |    while ((var4 < var11)) {
        |      while (input) {
        |        while (4) {
        |          output var8[2];
        |        }
        |      }
        |      var4 = (var4 + 1);
        |    }
        |  }
        |  return 0;
        |}
        |""".stripMargin

    val program = parseUnsafe(code)
    new SymbolicExecutorFactory(true, false, Some("none"), 1, 5, "coverage").get(program).run()

  }


}

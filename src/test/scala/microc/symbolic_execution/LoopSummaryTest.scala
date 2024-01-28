package microc.symbolic_execution

import microc.cfg.IntraproceduralCfgFactory
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class LoopSummaryTest extends FunSuite with MicrocSupport with Examples {

  test("loop summary test") {
    val code =
      """
        |main() {
        |  var k, i, n;
        |  k = 0;
        |  i = 3;
        |  n = input;
        |  A = [1, 1, 1, 1, 1, 1 ,0 ,1 ,1 ,1 ,1 ,1 ,0 ,0, 1, 1]
        |  while (i < n) {
        |   if (A[i] == 1) {
        |     k = k + 1;
        |   }
        |   i = i + 1;
        |  }
        |  if (k > 12) {
        |   k = 1 / 0;
        |  }
        |  return k;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    null
  }


  test("nested loop summary test") {
    val code =
      """
        |main() {
        |  var i, j, m, n;
        |  i = 0;
        |  m = input;
        |  n = input;
        |  while (i < m) {
        |     j = i;
        |     while (j < n) {
        |       j = j + 1;
        |     }
        |  }
        |  return j;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    null
  }
}

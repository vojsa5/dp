package microc.cli

import microc.ast.CodeLoc
import munit.FunSuite

class ReporterTest extends FunSuite {

  test("Format error") {
    val reporter = new Reporter(
      """|f() {
         |  return 1
         |}
         |""".stripMargin,
      Some("file.uc")
    )

    val actual = reporter.formatError("parse", "missing ;", CodeLoc(2, 11))
    val expected =
      """file.uc:[2:11]: parse error: missing ;
        |    return 1
        |            ^
        |""".stripMargin

    assertEquals(actual, expected)
  }

}

package microc.parser

import microc.ast.{CodeLoc, Program, Stmt}

class LLParserTest extends AbstractParserTest {
  override def parser: Parser = new LLParser

  checkFail[Stmt](
    """|return = 1;
       |""".stripMargin,
    ParseException("expected expression, got 'return'", CodeLoc(1, 1))
  )

  checkFail[Program](
    """|f() {
       |
       |
       |
       |  = 1;
       |
       |  return 1;
       |}
       |""".stripMargin,
    ParseException("expected expression, got '='", CodeLoc(5, 3))
  )

  checkFail[Program](
    """|f(x, ) {
       |  return 1;
       |}
       |""".stripMargin,
    ParseException("expected identifier, got ')'", CodeLoc(1, 6))
  )

  checkFail[Program](
    """|f(x) {
       |  return 1+;
       |}
       |""".stripMargin,
    ParseException("expected expression, got ';'", CodeLoc(2, 12))
  )

  checkFail[Program](
    """|f(x) {
       |  var
       |  return 1;
       |}
       |""".stripMargin,
    ParseException("expected identifier, got 'return'", CodeLoc(3, 3))
  )
}

package microc.parser

import microc.ast.{CodeLoc, Expr, Program, Stmt}

class PCParserTest extends AbstractParserTest {
  override def parser: Parser = new PCParser

  checkFail[Stmt](
    """|return = 1;
       |""".stripMargin,
    ParseException("expected expression", CodeLoc(1, 1))
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
    ParseException("expected 'return', got '= 1;'", CodeLoc(5, 3))
  )

  checkFail[Expr](
    "f(x,y,)",
    ParseException("expected expression", CodeLoc(1, 7))
  )

  checkFail[Program](
    """|f() { 
       |  return 1; 
       |} 
       |g() { 
       |  return 2 
       |}""".stripMargin,
    ParseException("expected ';', got '}'", CodeLoc(6, 1))
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
    ParseException("expected expression", CodeLoc(2, 12))
  )

  checkFail[Program](
    """|f(x) {
       |  var
       |  return 1;
       |}
       |""".stripMargin,
    ParseException("expected identifier, got keyword 'return'", CodeLoc(3, 3))
  )
}

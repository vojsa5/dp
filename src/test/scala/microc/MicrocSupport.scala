package microc

import microc.ast.{AstNormalizer, Program}
import microc.parser.Parser
import microc.util.IOUtil.FilesOps
import microc.util.logger.{ConsoleLogger, Debug}
import munit.Assertions.assertEquals
import munit.Location

import java.io.File

trait MicrocSupport {
  private def parser = Parser()

  protected def parseUnsafe(code: String): Program = {
    val res = parser.parseProgram(code)
    new AstNormalizer().normalize(res)
  }

  protected def parseUnsafe(file: File): Program = {
    val res = parser.parseProgram(file.readAll())
    new AstNormalizer().normalize(res)
  }

  implicit class AnyAssert[T](actual: T) {
    def -->(expected: T)(implicit loc: Location): Unit = assertEquals(actual, expected)
  }

  protected def logger = new ConsoleLogger(System.out, Debug)
}

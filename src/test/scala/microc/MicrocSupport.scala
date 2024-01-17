package microc

import microc.ast.Program
import microc.parser.Parser
import microc.util.IOUtil.FilesOps
import microc.util.logger.{ConsoleLogger, Debug}
import munit.Assertions.assertEquals
import munit.Location

import java.io.File

trait MicrocSupport {
  private def parser = Parser()

  protected def parseUnsafe(code: String): Program = {
    parser.parseProgram(code)
  }

  protected def parseUnsafe(file: File): Program = {
    parser.parseProgram(file.readAll())
  }

  implicit class AnyAssert[T](actual: T) {
    def -->(expected: T)(implicit loc: Location): Unit = assertEquals(actual, expected)
  }

  protected def logger = new ConsoleLogger(System.out, Debug)
}

package microc.cli

import microc.ProgramException
import microc.ast.JSONAstPrinter
import microc.parser.LLParser
import microc.util.IOUtil.InputStreamOpts
import microc.util.json.JSONPrettyPrinter

import java.io.{InputStream, OutputStream}
import scala.util.Using

class ExportAction(input: InputStream, output: OutputStream, filename: Option[String], indent: Option[Int] = None)
    extends Action {

  override def run(): Int = {
    val parser = new LLParser
    val source = input.readAll()
    val reporter = new Reporter(source, filename)

    try {
      val program = parser.parseProgram(source)
      val printer = new JSONAstPrinter
      val json = printer.serialize(program)

      Using(output) { stream =>
        new JSONPrettyPrinter(indent).print(json, stream)
      }.get

      0
    } catch {
      case e: ProgramException =>
        System.err.println(e.format(reporter))
        1
    }
  }
}

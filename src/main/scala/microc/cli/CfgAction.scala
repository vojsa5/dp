package microc.cli

import microc.ProgramException
import microc.ast.AstNormalizer
import microc.cfg.{DotCfgPrinter, IntraproceduralCfgFactory}
import microc.parser.LLParser
import microc.util.IOUtil.InputStreamOpts

import java.io._

class CfgAction(program: InputStream, filename: String, normalize: Boolean) extends Action {
  override def run(): Int = {
    val parser = new LLParser
    val source = program.readAll()
    val reporter = new Reporter(source, Some(filename))

    try {
      val program = {
        val p = parser.parseProgram(source)
        if (normalize) {
          val normalizer = new AstNormalizer
          normalizer.normalize(p)
        } else {
          p
        }
      }

      val cfg = new IntraproceduralCfgFactory().fromProgram(program)
      val printer = new DotCfgPrinter(2)
      val out = new OutputStreamWriter(System.out)
      printer.print(cfg, out)
      out.flush()

      0
    } catch {
      case e: ProgramException =>
        System.err.println(e.format(reporter))
        1
    }
  }
}

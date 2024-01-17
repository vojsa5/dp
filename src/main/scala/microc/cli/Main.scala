package microc.cli

import mainargs._
import microc.ast.Program
import microc.cfg.ProgramCfg
import microc.util.CharacterSets.NL

import java.io._

object Main {
/*
  @main(doc = "Print version and exit")
  def version(): Int = {
    import buildinfo.BuildInfo
    println(s"${BuildInfo.name} ${BuildInfo.version} (${BuildInfo.gitCommit})")
    0
  }
 */

  @main(doc = "Export uc program AST as JSON")
  def export(
      @arg(doc = "Output filename")
      output: Option[String],
      @arg(doc = "Indent (number of spaces)")
      indent: Int = 2,
      @arg(positional = true)
      program: Option[String]
  ): Int = {
    val in = program.map(new FileInputStream(_)).getOrElse(System.in)
    val out = output.map(new FileOutputStream(_)).getOrElse(System.out)

    new ExportAction(in, out, program, Some(indent)).run()
  }


  @main(doc = "Create CFG from a uc program")
  def cfg(
      @arg(positional = true)
      program: String,
      @arg(doc = "Normalize program")
      norm: Flag
  ): Int = {
    val programInput = new FileInputStream(program)

    new CfgAction(programInput, program, norm.value).run()
  }


  def main(args: Array[String]): Unit = ParserForMethods(this).runEither(args.toSeq) match {
    case Left(msg) =>
      System.err.println(msg)
      System.exit(1)
    case Right(exit: Int) =>
      System.exit(exit)
    case Right(e) =>
      sys.error(s"Unknown return value: $e")
  }

}

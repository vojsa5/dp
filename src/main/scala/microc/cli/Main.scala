package microc.cli

import mainargs._
import microc.ast.Program
import microc.cfg.ProgramCfg
import microc.symbolic_execution.SearchStrategy
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

  @main(doc = "Symbolicly execute uc program")
  def symboliclyExecute(program: String,
                        @arg(name = "search-strategy", doc = "choose a seach strategy (optional string argument)")
                        searchStrategy: Option[String] = None,
                        @arg(name = "smart-merging", doc = "Enable smart merging strategy (optional string argument)")
                        smartMerging: Option[String] = None,
                        @arg(name = "smart-merging-cost", doc = "smart merging cost (optional int argument)")
                        smartMergingCost: Option[Int] = None,
                        @arg(name = "kappa", doc = "kappa for smart merging (optional int argument)")
                        kappa: Option[Int] = None,
                        @arg(name = "summarization", doc = "Enable loop summarization (optional bool argument)")
                        summarization: Option[Boolean] = None,
                        @arg(name = "subsumption", doc = "Enable path subsumption (optional bool argument)")
                        subsumption: Option[Boolean] = None,
                        @arg(name = "timeout", doc = "Timeout for the program is s (optional int argument)")
                        timeout: Option[Int] = None,
                        @arg(name = "output", doc = "Output file (optional string argument)")
                        outputFile: Option[String] = None,
                        @arg(name = "time-output", doc = "Time output file (optional string argument)")
                        timeOutputFile: Option[String] = None): Int = {
    val programInput = new FileInputStream(program)
    val output = outputFile match {
      case Some(file) => new FileOutputStream(file)
      case None => System.out
    }
    val timeOutput = timeOutputFile match {
      case Some(file) => new FileOutputStream(file)
      case None => System.out
    }
    new SymbolicExecuteAction(programInput, searchStrategy, smartMerging, smartMergingCost, kappa, summarization, subsumption, timeout, output, timeOutput).run()
  }

  @main(doc = "precomputeVariableCosts")
  def precomputeVariableCosts(program: String,
                        @arg(name = "smart-merging", doc = "Enable smart merging strategy (optional string argument)")
                        smartMerging: Option[String] = None,
                        @arg(name = "kappa", doc = "kappa for smart merging (optional int argument)")
                        kappa: Option[Int] = None,
                        @arg(name = "timeout", doc = "Timeout for the program is s (optional int argument)")
                        timeout: Option[Int] = None,
                        @arg(name = "output", doc = "Output file (optional string argument)")
                        outputFile: Option[String] = None): Int = {
    val programInput = new FileInputStream(program)
    val output = outputFile match {
      case Some(file) => new FileOutputStream(file)
      case None => System.out
    }
    new PrecomputeVariableCosts(programInput, smartMerging, kappa, timeout, output).run()
  }

  @main(doc = "Generate program")
  def generateProgram(
                       @arg(name = "file", doc = "Output file path for the generated program")
                       file: String,
                       @arg(name = "loopGenProb", doc = "Probability of generating a loop")
                       loopGenProb: Double = 1/6,
                       @arg(name = "forLoopGenProb", doc = "Probability of generating a for loop")
                       forLoopGenProb: Double = 1/6,
                       @arg(name = "maxStmtDepth", doc = "Maximum depth of statement nesting")
                       maxStmtDepth: Int = 2,
                       @arg(name = "maxTopLvlStmtsCount", doc = "Maximum number of top-level statements")
                       maxTopLvlStmtsCount: Int = 15,
                       @arg(name = "maxStmtsWithinABlock", doc = "Maximum number of statements within a block")
                       maxStmtsWithinABlock: Int = 7,
                       @arg(name = "errorGuaranteed", doc = "An error is guaranteed")
                       errorGuaranteed: Boolean = false,
                       @arg(name = "tryNotToGenerateError", doc = "The generator tries to not generate errors")
                       tryNotToGenerateRandomError: Boolean = true
                     ): Int = {
    new GenerateProgramAction(file, loopGenProb, forLoopGenProb, maxStmtDepth, maxTopLvlStmtsCount, maxStmtsWithinABlock, errorGuaranteed, tryNotToGenerateRandomError).run()
  }


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

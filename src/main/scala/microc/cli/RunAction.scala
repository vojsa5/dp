package microc.cli

import microc.ProgramException
import microc.analysis.{Declarations, SemanticAnalysis}
import microc.ast.Program
import microc.interpreter.{Interpreter, MicroCInterpreter}
import microc.parser.LLParser
import microc.util.CharacterSets.NL
import microc.util.IOUtil.InputStreamOpts
import microc.util.{ASCIIReader, ASCIIWriter}

import java.io._

class RunAction(
                 program: InputStream,
                 filename: String,
                 ascii: Boolean,
                 outputRetval: Boolean,
                 time: Boolean,
                 input: Reader,
                 args: List[Int]
               ) extends Action {
  override def run(): Int = {
    val parser = new LLParser
    val source = program.readAll()
    val reporter = new Reporter(source, Some(filename))

    try {
      val program = {
        parser.parseProgram(source)
      }

      val declarations = new SemanticAnalysis().analyze(program)
      val stdout = createOutput
      val stdin = createInput
      val interpreter = createInterpreter(program, declarations, stdin, stdout)

      val start = System.currentTimeMillis()
      val status = interpreter.run(args)
      val elapsed = System.currentTimeMillis() - start

      stdout.flush()

      if (time) {
        System.out.println(s"${NL}Elapsed: $elapsed${NL}")
      }

      val retval = if (outputRetval) {
        System.out.println(s"$status")
        0
      } else {
        status
      }

      retval
    } catch {
      case e: ProgramException =>
        System.err.println(e.format(reporter))
        1
    }
  }

  private def createOutput: Writer = {
    val out = new OutputStreamWriter(System.out)
    if (ascii) {
      new ASCIIWriter(out)
    } else {
      out
    }
  }

  private def createInput: Reader = {
    if (ascii) {
      new ASCIIReader(input)
    } else {
      input
    }
  }

  private def createInterpreter(
                                 program: Program,
                                 declarations: Declarations,
                                 stdin: Reader,
                                 stdout: Writer
                               ): Interpreter = new MicroCInterpreter(program, stdin, stdout, ascii)
}


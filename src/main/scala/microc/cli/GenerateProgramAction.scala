package microc.cli

import microc.ast.AstPrinter
import microc.symbolic_execution.ProgramGenerator

import java.io.{File, PrintWriter}

class GenerateProgramAction(file: String) extends Action {

  override def run(): Int = {
    val program = new ProgramGenerator().generateRandomProgram(false)
    val pw = new PrintWriter(new File(file))
    var content: String = ""
    program.funs.foreach(fce => content += new AstPrinter().print(fce))
    println(content)
    pw.print(content)
    pw.close()
    0
  }
}

package microc.cli

import microc.ast.AstPrinter
import microc.symbolic_execution.ProgramGenerator

import java.io.{File, PrintWriter}

class GenerateProgramAction(file: String, loopGenProb: Double, forLoopGenProb: Double, maxStmtDepth: Int, maxTopLvlStmtsCount: Int, maxStmtsWithinABlock: Int) extends Action {
  override def run(): Int = {
    val programGenerator = new ProgramGenerator(loopGenProb, forLoopGenProb, maxStmtDepth, maxTopLvlStmtsCount, maxStmtsWithinABlock)
    val program = programGenerator.generateRandomProgram(false)
    val pw = new PrintWriter(new File(file))
    val content = new AstPrinter().print(program)
    pw.print(content)
    pw.close()
    0
  }
}

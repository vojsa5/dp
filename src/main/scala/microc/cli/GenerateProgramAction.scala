package microc.cli

import microc.ast.AstPrinter
import microc.generation.ProgramGenerator

import java.io.{File, PrintWriter}

class GenerateProgramAction(file: String, loopGenProb: Double, forLoopGenProb: Double, maxBlockDepth: Int, maxTopLvlStmtsCount: Int, maxStmtsWithinABlock: Int, errorGuaranteed: Boolean, doNotGenerateDivisions: Boolean) extends Action {
  override def run(): Int = {
    if (loopGenProb + forLoopGenProb > 1.0) {
      throw new IllegalArgumentException("The probabilities of generating loop are to big ->  " + "for loop: " + forLoopGenProb + "while loop: " + loopGenProb)
    }
    if (loopGenProb < 0.0 || forLoopGenProb < 0.0 ) {
      throw new IllegalArgumentException("The probabilities of generating loop are to small ->  " + "for loop: " + forLoopGenProb + "while loop: " + loopGenProb)
    }
    val programGenerator = new ProgramGenerator(loopGenProb, forLoopGenProb, maxBlockDepth, maxTopLvlStmtsCount, maxStmtsWithinABlock, errorGuaranteed, doNotGenerateDivisions)
    val program = programGenerator.generateRandomProgram(false)
    val pw = new PrintWriter(new File(file))
    val content = new AstPrinter().print(program)
    pw.print(content)
    pw.close()
    0
  }
}

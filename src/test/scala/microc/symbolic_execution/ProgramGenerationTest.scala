package microc.symbolic_execution

import microc.ast.AstNormalizer
import microc.cfg.IntraproceduralCfgFactory
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class ProgramGenerationTest extends FunSuite with MicrocSupport with Examples {

  test("test generation") {
    val program = new AstNormalizer().normalize(ProgramGenerator.generateRandomProgram())
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    new SymbolicExecutor(cfg).run()
    null
  }


  test("test generation wit loop summaries") {
    val program = new AstNormalizer().normalize(ProgramGenerator.generateRandomProgram())
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    new LoopSummary(cfg).run()
    null
  }
}

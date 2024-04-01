package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.AstNormalizer
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.{Examples, MicrocSupport}
import munit.FunSuite
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

import scala.collection.mutable
import scala.concurrent.{Await, Future, TimeoutException}

class ProgramGenerationTest extends FunSuite with MicrocSupport with Examples {

  test("test generation") {
    val future = Future {
      val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
      val cfg = new IntraproceduralCfgFactory().fromProgram(program);
      new SymbolicExecutor(cfg).run()
    }
    try {
      Await.result(future, 20.seconds)
    }
    catch {
      case _: TimeoutException =>
      case e =>
        fail(e.toString)
    }
  }

  test("test generation 50x") {

    for (i <- 0 until 50) {
      println(i)

      val future = Future {
        val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
        val cfg = new IntraproceduralCfgFactory().fromProgram(program);
        new SymbolicExecutor(cfg, printStats = false).run()
      }

      try {
        Await.result(future, 20.seconds)
      }
      catch {
        case _: TimeoutException =>
        case e =>
          fail(e.toString)
      }

    }
  }

  test("test generation subsumption") {
    val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val ctx = new Context()
    try {
      new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx))).run()
    }
    catch {
      case e@ExecutionException(_, _, _) =>
        println(e.message)
      case e =>
        throw e
    }
    null
  }

  test("test generation subsumption 50x") {

    for (i <- 0 until 50) {
      println(i)

      val future = Future {
        val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
        val cfg = new IntraproceduralCfgFactory().fromProgram(program);
        val ctx = new Context()
        new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), printStats = false).run()
      }

      try {
        Await.result(future, 5.seconds)
      }
      catch {
        case _: TimeoutException =>
        case e =>
          fail(e.toString)
      }

    }
  }

  test("test generation with loop summaries") {
    val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val executor = new LoopSummary(cfg)
    executor.run()
    null
  }

  test("test generation loop summaries 50x") {

    for (i <- 0 until 50) {
      println(i)

      val future = Future {
        val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
        val cfg = new IntraproceduralCfgFactory().fromProgram(program);
        val executor = new LoopSummary(cfg, printStats = false).run()
      }

      try {
        Await.result(future, 5.seconds)
      }
      catch {
        case _: TimeoutException =>
        case e =>
          fail(e.toString)
      }

    }
  }

  test("test generation with smart merging") {
    val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
    val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
    for (node <- analysesResult) {
      val nodeCosts = new mutable.HashMap[String, Double]
      for (cost <- node._2) {
        nodeCosts.put(cost._1.name, cost._2)
      }
      variableCosts.put(node._1, nodeCosts)
    }
    new SymbolicExecutor(cfg, searchStrategy = new HeuristicBasedStateMerging(new BFSSearchStrategy, variableCosts, 3)).run()
    null
  }


  test("test generation with smart merging 50x") {

    for (i <- 0 until 50) {
      println(i)

      val future = Future {
        val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
        val cfg = new IntraproceduralCfgFactory().fromProgram(program);
        val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
        val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
        for (node <- analysesResult) {
          val nodeCosts = new mutable.HashMap[String, Double]
          for (cost <- node._2) {
            nodeCosts.put(cost._1.name, cost._2)
          }
          variableCosts.put(node._1, nodeCosts)
        }
        new SymbolicExecutor(cfg, searchStrategy = new HeuristicBasedStateMerging(new BFSSearchStrategy, variableCosts, 3), printStats = false).run()
      }

      try {
        Await.result(future, 5.seconds)
      }
      catch {
        case _: TimeoutException =>
        case e =>
          fail(e.toString)
      }

    }
  }


  test("test generation with klee search") {
    val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val covered = Some(mutable.HashSet[CfgNode]())
    val stateHistory = new StateHistory()
    val executor = new SymbolicExecutor(cfg, stateHistory = Some(stateHistory), searchStrategy = new KleeSearchStrategy(stateHistory, covered.get), covered = covered)
    executor.run()
  }


  test("experiments") {
    new ExperimentRunner().run()
  }
}

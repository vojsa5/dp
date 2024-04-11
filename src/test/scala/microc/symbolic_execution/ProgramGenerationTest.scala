package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.AstNormalizer
import microc.cfg.{CfgNode, IntraproceduralCfgFactory, ProgramCfg}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

import scala.concurrent.{Await, ExecutionContext, Future, TimeoutException}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.collection.mutable
import java.util.concurrent.Executors
import scala.util.{Failure, Success}


class ProgramGenerationTest extends FunSuite with MicrocSupport with Examples {

  val threadPool = Executors.newFixedThreadPool(25)

  implicit val executionContext = ExecutionContext.fromExecutor(threadPool)

  test("test generation") {
    val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    new SymbolicExecutor(cfg).run()
//    val future = Future {
//      val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
//      val cfg = new IntraproceduralCfgFactory().fromProgram(program);
//      new SymbolicExecutor(cfg).run()
//    }
//    try {
//      Await.result(future, 20.seconds)
//    }
//    catch {
//      case _: TimeoutException =>
//      case e =>
//        fail(e.toString)
//    }
  }

  test("test generation 50x") {

    for (i <- 0 until 50) {
      println(i)

      val future = Future {
        val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram(false))
        val cfg = new IntraproceduralCfgFactory().fromProgram(program);
        new SymbolicExecutor(cfg, printStats = false).run()
      }(executionContext)

      try {
        Await.result(future, 10.seconds)
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

  def tmp(cfg: ProgramCfg, variableCosts: mutable.HashMap[CfgNode, mutable.HashMap[String, Double]], errors: Array[Int], pathsExplored: Array[Array[Int]], cost: Int): Unit = {
    var executor: SymbolicExecutor = null
    val future = Future {
      executor = new SymbolicExecutor(cfg, searchStrategy = new HeuristicBasedStateMerging(new BFSSearchStrategy, variableCosts, 3), printStats = false)
      executor.run()
    }(ExecutionContext.fromExecutor(Executors.newFixedThreadPool(1)))
    try {
      Await.ready(future, 30.seconds)
      errors(cost - 1) = errors(cost - 1) + 1
      println("ERROR FOUND", executor.statistics.numPaths)
    }
    catch {
      case _: TimeoutException =>
        println("NO ERROR FOUND", executor.statistics.numPaths)
        pathsExplored(cost - 1) = pathsExplored(cost - 1).appended(executor.statistics.numPaths)
      case e =>
        fail(e.toString)
    }
    Thread.sleep(10000)
  }


  test("get smart merging best params") {
    val errors = Array(0, 0, 0, 0, 0)
    val pathsExplored: Array[Array[Int]] = Array(Array(), Array(), Array(), Array(), Array())
    for (_ <- 0 to 5) {
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
      for (cost <- 1 to 5) {
        tmp(cfg, variableCosts, errors, pathsExplored, cost)
      }
    }
    System.out.println(errors)
    System.out.println(pathsExplored)
    null
  }


  test("experiments") {
    new ExperimentRunner().run()
  }
}

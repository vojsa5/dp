package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analysis.SemanticAnalysis
import microc.ast.AstNormalizer
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}

import scala.collection.mutable
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

class ExperimentRunner {


  def run(): Unit = {
    for (_ <- 0 until 3) {
      runOneProgram()
    }
  }

  private def runOneProgram(): Unit = {
    val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var executor: SymbolicExecutor = null

    println("Experiment started")

    val ctx = new Context()
    val subsumptions: Array[Option[PathSubsumption]] = Array(None, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)))

    val tmp = new TMP()(new SemanticAnalysis().analyze(program))
    tmp.tmp2(cfg)

    for (subsumption <- subsumptions) {

      var future = Future {
        val ctx = new Context()
        val solver = new ConstraintSolver(ctx)
        executor = new SymbolicExecutor(cfg, ctx = ctx, printStats = false)
        executor.run()
      }
      //
      //    try {
      //      Await.ready(future, 10.seconds)
      //      println("Default symbolic executor: No error found. Paths explored: ", executor.statistics.numPaths)
      //    }
      //    catch {
      //      case _: TimeoutException =>
      //        println("Default symbolic executor: No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
      //      case e@ExecutionException(_, _, _) =>
      //        println("Default symbolic executor: An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
      //      case e =>
      //        throw e
      //    }
      //
      //    future = Future {
      //      val ctx = new Context()
      //      val solver = new ConstraintSolver(ctx)
      //      executor = new LoopSummary(cfg, ctx = ctx, printStats = false)
      //      executor.run()
      //    }
      //
      //    try {
      //      Await.ready(future, 10.seconds)
      //      println("Loop summarization symbolic executor: No error found. Paths explored: ", executor.statistics.numPaths)
      //    }
      //    catch {
      //      case _: TimeoutException =>
      //        println("Loop summarization symbolic executor: No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
      //      case e@ExecutionException(_, _, _) =>
      //        println("Loop summarization symbolic executor: An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
      //      case e =>
      //        throw e
      //    }
      //
      //    future = Future {
      //      val ctx = new Context()
      //      val solver = new ConstraintSolver(ctx)
      //      executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), printStats = false)
      //      executor.run()
      //    }
      //
      //    try {
      //      Await.ready(future, 10.seconds)
      //      println("Subsumption symbolic executor: No error found. Paths explored: ", executor.statistics.numPaths)
      //    }
      //    catch {
      //      case _: TimeoutException =>
      //        println("Subsumption symbolic executor: No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
      //      case e@ExecutionException(_, _, _) =>
      //        println("Subsumption symbolic executor: An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
      //      case e =>
      //        throw e
      //    }


      future = Future {
        val ctx = new Context()
        val solver = new ConstraintSolver(ctx)
        val covered = Some(mutable.HashSet[CfgNode]())
        val stateHistory = new StateHistory()
        executor =
          new SymbolicExecutor(
            cfg,
            stateHistory = Some(stateHistory),
            searchStrategy = new KleeSearchStrategy(stateHistory, covered.get),
            covered = covered,
            printStats = false
          )
          if (executor == null) {
            println("hi")
          }
        executor.run()
      }

      try {
        Await.ready(future, 10.seconds)
        println("klee search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("klee search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("klee search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }


      future = Future {
        val covered = Some(mutable.HashSet[CfgNode]())
        val stateHistory = new StateHistory()
        val executor = new SymbolicExecutor(
          cfg,
          stateHistory = Some(stateHistory),
          searchStrategy = new RandomPathSelectionStrategy(stateHistory),
          covered = covered,
          printStats = false
        )
        executor.run()
      }

      try {
        Await.ready(future, 10.seconds)
        println("random path search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("random path search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("random path search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }

      future = Future {
        val covered = Some(mutable.HashSet[CfgNode]())
        val executor = new SymbolicExecutor(
          cfg,
          searchStrategy = new CoverageSearchStrategy(covered.get),
          covered = covered,
          printStats = false
        )
        executor.run()
      }

      try {
        Await.ready(future, 10.seconds)
        println("coverage search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("coverage search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("coverage search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }


      future = Future {
        val executor = new SymbolicExecutor(
          cfg,
          searchStrategy = new BFSSearchStrategy(),
          printStats = false
        )
        executor.run()
      }

      try {
        Await.ready(future, 10.seconds)
        println("bfs search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("bfs search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("bfs search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }


      future = Future {
        val executor = new SymbolicExecutor(
          cfg,
          searchStrategy = new DFSSearchStrategy(),
          printStats = false
        )
        executor.run()
      }

      try {
        Await.ready(future, 10.seconds)
        println("dfs search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("dfs search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("dfs search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }

      future = Future {
        val executor = new SymbolicExecutor(
          cfg,
          searchStrategy = new RandomSearchStrategy(),
          printStats = false
        )
        executor.run()
      }

      try {
        Await.ready(future, 10.seconds)
        println("random search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("random search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("random search symbolic executor[subsumption used: " , subsumption.nonEmpty, "]: An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }
    }
    println("Experiment stopped")
  }
}



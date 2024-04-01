package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.{AstNormalizer, Program}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory, ProgramCfg}

import scala.collection.mutable
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

class ExperimentRunner {


  def run(): Unit = {
    for (_ <- 0 until 1) {
      runOneProgram()
    }
  }

  def getSearchStrategies(covered: Option[mutable.HashSet[CfgNode]], stateHistory: StateHistory): Array[(String, SearchStrategy)] = {
    Array(
//      ("random", new RandomSearchStrategy()),
//      ("dfs", new DFSSearchStrategy()),
//      ("bfs", new BFSSearchStrategy()),
//      ("cov", new CoverageSearchStrategy(covered.get)),
//      ("path", new RandomPathSelectionStrategy(stateHistory)),
      ("klee", new KleeSearchStrategy(stateHistory, covered.get))
    )
  }

  def getMergeStrategies(program: Program, cfg: ProgramCfg, covered: Option[mutable.HashSet[CfgNode]], stateHistory: StateHistory): Array[(String, SearchStrategy)] = {
    var res = Array[(String, SearchStrategy)]()
    for (searchStrategy <- getSearchStrategies(covered, stateHistory)) {
      res = res.appended(searchStrategy)

      val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
      val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
      for (node <- analysesResult) {
        val nodeCosts = new mutable.HashMap[String, Double]
        for (cost <- node._2) {
          nodeCosts.put(cost._1.name, cost._2)
        }
        variableCosts.put(node._1, nodeCosts)
      }
      res = res.appended("heur1 " + searchStrategy._1, new HeuristicBasedStateMerging(searchStrategy._2, variableCosts, 3))

      val tmp = new RecursionBasedAnalyses()(new SemanticAnalysis().analyze(program))
      tmp.tmp2(cfg)

      res = res.appended("heur2 " + searchStrategy._1, new HeuristicBasedStateMerging(searchStrategy._2, tmp.mapping, 3))
      res = res.appended("aggr " + searchStrategy._1, new AgressiveStateMerging(searchStrategy._2))
    }
    res
  }

  private def runOneProgram(): Unit = {
    val program = new AstNormalizer().normalize(new ProgramGenerator().generateRandomProgram())
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var executor: SymbolicExecutor = null

    println("Experiment started")
    val covered = Some(mutable.HashSet[CfgNode]())
    val stateHistory = new StateHistory()


    val tmp = new RecursionBasedAnalyses()(new SemanticAnalysis().analyze(program))
    tmp.tmp2(cfg)

    val timeout = 20.seconds

    for (mergeStrategy <- getMergeStrategies(program, cfg, covered, stateHistory)) {
      var ctx = new Context()
      executor = new SymbolicExecutor(cfg, None, ctx, mergeStrategy._2, Some(stateHistory), covered, false)
      var future = Future {
        executor.run()
      }

      try {
        Await.ready(future, timeout)
        println("subsumption: false, summarization: false, " + mergeStrategy._1 + ": No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("subsumption: false, summarization: false, " + mergeStrategy._1 + ": No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("subsumption: false, summarization: false, " + mergeStrategy._1 + ": An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }

      ctx = new Context()
      executor = new LoopSummary(cfg, None, ctx, mergeStrategy._2, Some(stateHistory), covered, false)
      future = Future {
        executor.run()
      }

      try {
        Await.ready(future, timeout)
        println("subsumption: false, summarization: true, " + mergeStrategy._1 + ": No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("subsumption: false, summarization: true, " + mergeStrategy._1 + ": No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("subsumption: false, summarization: true, " + mergeStrategy._1 + ": An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }

      ctx = new Context()
      executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, mergeStrategy._2, Some(stateHistory), covered, false)

      future = Future {
        executor.run()
      }

      try {
        Await.ready(future, timeout)
        println("subsumption: true, summarization: false, " + mergeStrategy._1 + ": No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("subsumption: true, summarization: false, " + mergeStrategy._1 + ": No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("subsumption: true, summarization: false, " + mergeStrategy._1 + ": An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }

      ctx = new Context()
      executor = new LoopSummary(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), ctx, mergeStrategy._2, Some(stateHistory), covered, false)

      future = Future {
        executor.run()
      }

      try {
        Await.ready(future, timeout)
        println("subsumption: true, summarization: true, " + mergeStrategy._1 + ": No error found. Paths explored: ", executor.statistics.numPaths)
      }
      catch {
        case _: TimeoutException =>
          println("subsumption: true, summarization: true, " + mergeStrategy._1 + ": No error found. Max time reached. Paths explored: ", executor.statistics.numPaths)
        case e@ExecutionException(_, _, _) =>
          println("subsumption: true, summarization: true, " + mergeStrategy._1 + ": An error found: ", e.message, "Paths explored: ", executor.statistics.numPaths)
        case e =>
          throw e
      }
    }
    println("Experiment stopped")
  }
}



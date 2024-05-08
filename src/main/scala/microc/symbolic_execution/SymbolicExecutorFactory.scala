package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analyses.RecursionBasedAnalyses
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.{Decl, Program}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory, ProgramCfg}
import microc.parser.Parser
import microc.symbolic_execution.optimizations.merging.{AggressiveStateMerging, DynamicStateMerging, HeuristicBasedStateMerging}
import microc.symbolic_execution.optimizations.subsumption.PathSubsumption
import microc.symbolic_execution.optimizations.summarization.LoopSummarization

import java.util
import javax.management.InvalidApplicationException
import scala.collection.immutable.HashSet
import scala.collection.mutable

class SymbolicExecutorFactory(useSummarizaiton: Boolean, useSubsumption: Boolean, mergingStrategyType: Option[String],
                              smartMergingCost: Int, kappa: Int, searchStrategyType: String) {
  def get(program: Program): SymbolicExecutor = {
    val programCfg = new IntraproceduralCfgFactory().fromProgram(program)
    val ctx = new Context()
    var pathSubsumption: Option[PathSubsumption] = None
    if (useSubsumption) {
      pathSubsumption = Some(new PathSubsumption(new ConstraintSolver(ctx)))
    }
    var executionTree: Option[ExecutionTree] = None
    var covered: Option[mutable.HashSet[CfgNode]] = None

    val searchStrategy = searchStrategyType match {
      case "bfs" =>
        new BFSSearchStrategy()
      case "dfs" =>
        new DFSSearchStrategy()
      case "random" =>
        new RandomSearchStrategy()
      case "tree" =>
        executionTree = Some(new ExecutionTree())
        new RandomPathSelectionStrategy(executionTree.get)
      case "coverage" =>
        covered = Some(new mutable.HashSet[CfgNode]())
        new CoverageSearchStrategy(covered.get)
      case "klee" =>
        executionTree = Some(new ExecutionTree())
        covered = Some(new mutable.HashSet[CfgNode]())
        new KleeSearchStrategy(executionTree.get, covered.get)
      case _ =>
        throw new InvalidApplicationException()
    }

    val possiblyMergingSearchStrategy = mergingStrategyType match {
      case None =>
        searchStrategy
      case Some("none") =>
        searchStrategy
      case Some("aggresive") =>
        new AggressiveStateMerging(searchStrategy)
      case Some("querycount") => {
        val analysesResult = new QueryCountAnalyses(programCfg)(new SemanticAnalysis().analyze(program)).analyze()
        val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
        for (node <- analysesResult) {
          val nodeCosts = new mutable.HashMap[String, Double]
          for (cost <- node._2) {
            nodeCosts.put(cost._1.name, cost._2)
          }
          variableCosts.put(node._1, nodeCosts)
        }
        new HeuristicBasedStateMerging(searchStrategy, variableCosts, smartMergingCost)
      }
      case Some("recursive") => {
        val tmp = new RecursionBasedAnalyses()(new SemanticAnalysis().analyze(program), kappa)
        tmp.tmp2(programCfg)
        new HeuristicBasedStateMerging(searchStrategy, tmp.mapping, smartMergingCost)
      }
      case Some(_) =>
        throw new InvalidApplicationException()
    }


    if (useSummarizaiton) {
      new LoopSummarization(programCfg, pathSubsumption, ctx, possiblyMergingSearchStrategy, executionTree, covered, printStats = false)
    }
    else {
      new SymbolicExecutor(programCfg, pathSubsumption, ctx, possiblyMergingSearchStrategy, executionTree, covered, printStats = false)
    }
  }
}

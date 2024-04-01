package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.{Decl, Program}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory, ProgramCfg}
import microc.parser.Parser

import javax.management.InvalidApplicationException
import scala.collection.mutable

class SymbolicExecutorFactory(useSummarizaiton: Boolean, useSubsumption: Boolean, mergingStrategyType: Option[String], searchStrategyType: String) {
  def get(program: Program): SymbolicExecutor = {
    val programCfg = new IntraproceduralCfgFactory().fromProgram(program)
    val ctx = new Context()
    var pathSubsumption: Option[PathSubsumption] = None
    if (useSubsumption) {
      pathSubsumption = Some(new PathSubsumption(new ConstraintSolver(ctx), ctx))
    }

    val searchStrategy = searchStrategyType match {
      case "bfs" =>
        new BFSSearchStrategy()
      case "dfs" =>
        new DFSSearchStrategy()
      case "random" =>
        new RandomSearchStrategy()
      case _ =>
        throw new InvalidApplicationException()
    }

    val possiblyMergingSearchStrategy = mergingStrategyType match {
      case None =>
        searchStrategy
      case Some("aggresive") =>
        new AgressiveStateMerging(searchStrategy)
      case Some("query-count") => {
        val analysesResult = new QueryCountAnalyses(programCfg)(new SemanticAnalysis().analyze(program)).analyze()
        val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
        for (node <- analysesResult) {
          val nodeCosts = new mutable.HashMap[String, Double]
          for (cost <- node._2) {
            nodeCosts.put(cost._1.name, cost._2)
          }
          variableCosts.put(node._1, nodeCosts)
        }
        new HeuristicBasedStateMerging(new BFSSearchStrategy, variableCosts, 3)
      }
      case Some("tmp") => {
        val tmp = new RecursionBasedAnalyses()(new SemanticAnalysis().analyze(program))
        tmp.tmp2(programCfg)
        new HeuristicBasedStateMerging(new BFSSearchStrategy, tmp.mapping, 3)
      }
      case Some(_) =>
        throw new InvalidApplicationException()
    }


    if (useSummarizaiton) {
      new LoopSummary(programCfg, pathSubsumption, ctx, possiblyMergingSearchStrategy)
    }
    else {
      new SymbolicExecutor(programCfg, pathSubsumption, ctx, possiblyMergingSearchStrategy)
    }
  }
}

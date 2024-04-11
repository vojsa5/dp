package microc.cli

import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.AstNormalizer
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.parser.LLParser
import microc.symbolic_execution.{BFSSearchStrategy, HeuristicBasedStateMerging, RecursionBasedAnalyses, SymbolicExecutor, SymbolicExecutorFactory}
import microc.util.IOUtil.InputStreamOpts

import java.io.{InputStream, OutputStream, Reader}
import java.nio.charset.StandardCharsets
import scala.collection.mutable
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

class SymbolicExecuteAction(
                             program: InputStream,
                             searchStrategy: Option[String],
                             smartMerging: Option[String],
                             smartMergingCost: Option[Int],
                             summarization: Option[Boolean],
                             subsumption: Option[Boolean],
                             timeout: Option[Int],
                             output: OutputStream
                           ) extends Action
 {

   override def run(): Int = {
     val parser = new LLParser
     val source = program.readAll()
     val summariationB = summarization match {
       case Some(v) => v
       case None => false
     }
     val subsumptionB = subsumption match {
       case Some(v) => v
       case None => false
     }
     val searchStrategyStr = searchStrategy match {
       case Some(v) => v
       case None => "bfs"
     }
     val timeoutI = timeout match {
       case Some(v) => v
       case None => 10
     }
     val factory = new SymbolicExecutorFactory(summariationB, subsumptionB, smartMerging, smartMergingCost, searchStrategyStr)
     val programCfg = {
       new AstNormalizer().normalize(parser.parseProgram(source))
     }
     val cfg = new IntraproceduralCfgFactory().fromProgram(programCfg);
     val executor = factory.get(programCfg)
     val future = Future {
       executor.run()
     }
     try {
       Await.result(future, timeoutI.seconds) // Adjust the timeout duration as needed
     } catch {
       case e: TimeoutException =>
         println("Execution timed out!")
       // Handle the timeout scenario, e.g., by gracefully stopping the executor or logging the timeout
     }

     output.write(executor.statistics.numPaths.toString.getBytes(StandardCharsets.UTF_8))
     println(executor.statistics.numPaths)
     0
   }


 }

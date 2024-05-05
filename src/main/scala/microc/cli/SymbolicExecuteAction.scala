package microc.cli

import microc.analyses.RecursionBasedAnalyses
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.AstNormalizer
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.parser.LLParser
import microc.symbolic_execution.optimizations.merging.HeuristicBasedStateMerging
import microc.symbolic_execution.{BFSSearchStrategy, SymbolicExecutor, SymbolicExecutorFactory}
import microc.util.IOUtil.InputStreamOpts

import java.io.{FileOutputStream, InputStream, OutputStream, Reader}
import java.nio.charset.StandardCharsets
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

class SymbolicExecuteAction(
                             program: InputStream,
                             searchStrategy: Option[String],
                             smartMerging: Option[String],
                             smartMergingCostOpt: Option[Int],
                             kappaOpt: Option[Int],
                             summarization: Option[Boolean],
                             subsumption: Option[Boolean],
                             timeout: Option[Int],
                             outputFolderPathOpt: Option[String]
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
       case None => 30
     }
     val smartMergingCost = smartMergingCostOpt match {
       case Some(value) => value
       case None => 1
     }
     val kappa = kappaOpt match {
       case Some(value) => value
       case None => 1
     }
     val factory = new SymbolicExecutorFactory(summariationB, subsumptionB, smartMerging, smartMergingCost, kappa, searchStrategyStr)
     val programCfg = {
       new AstNormalizer().normalize(parser.parseProgram(source))
     }
     val executor = factory.get(programCfg)
     val future = Future {
       executor.run()
     }
     var errorEncountered = 0
     val startTime = System.currentTimeMillis()
     try {
       Await.result(future, timeoutI.seconds)
     }
     catch {
       case e: TimeoutException =>
         println("Execution timed out!")
       case e =>
         println(e)
         errorEncountered = 1
     }
     val endTime = System.currentTimeMillis()
     val elapsedTime = endTime - startTime

     outputFolderPathOpt match {
       case Some(outputFolderPath) =>
         val coverageOutputPath = s"$outputFolderPath/coverage.txt"
         println(coverageOutputPath)
         val coverageOutput = new FileOutputStream(coverageOutputPath)
         try {
           coverageOutput.write(executor.statistics.numPaths.toString.getBytes(StandardCharsets.UTF_8))
         } finally {
           coverageOutput.close()
         }
         println(executor.statistics.numPaths)

         val timeOutputPath = s"$outputFolderPath/time.txt"
         val timeOutput = new FileOutputStream(timeOutputPath)
         try {
           timeOutput.write(elapsedTime.toString.getBytes(StandardCharsets.UTF_8))
         } finally {
           timeOutput.close()
         }
         println(elapsedTime)


         val errorOutputPath = s"$outputFolderPath/error.txt"
         val errorOutput = new FileOutputStream(errorOutputPath)
         try {
           errorOutput.write(errorEncountered.toString.getBytes(StandardCharsets.UTF_8))
         } finally {
           errorOutput.close()
         }
         println(errorEncountered)
       case None =>
     }

     0
   }


 }

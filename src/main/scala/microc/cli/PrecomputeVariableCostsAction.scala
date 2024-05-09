package microc.cli

import microc.analyses.RecursionBasedAnalyses
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.AstNormalizer
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.parser.LLParser
import microc.util.IOUtil.InputStreamOpts

import java.io.{InputStream, OutputStream}
import java.nio.charset.StandardCharsets
import scala.concurrent.ExecutionContext.Implicits.global
import scala.collection.mutable
import scala.concurrent.duration.DurationInt
import scala.concurrent.{Await, Future, TimeoutException}

class PrecomputeVariableCostsAction(
                               program: InputStream,
                               smartMerging: Option[String],
                               kappa: Option[Int],
                               timeout: Option[Int],
                               output: OutputStream
                             ) extends Action {

  override def run(): Int = {
    val programParsed = new AstNormalizer().normalize(new LLParser().parseProgram(program.readAll()))
    val programCfg = new IntraproceduralCfgFactory().fromProgram(programParsed)

    val timeoutI = timeout match {
      case Some(v) => v
      case None => 30
    }

    val future = Future {
      smartMerging match {
        case Some("recursive") =>
          val kappaI = kappa match {
            case Some(value) => value
            case None => 1
          }
          val tmp = new RecursionBasedAnalyses()(new SemanticAnalysis().analyze(programParsed), kappaI)
          tmp.compute(programCfg)
        case Some("lattice-based") =>
          val analysesResult = new QueryCountAnalyses(programCfg)(new SemanticAnalysis().analyze(programParsed)).analyze()
          val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
          for (node <- analysesResult) {
            val nodeCosts = new mutable.HashMap[String, Double]
            for (cost <- node._2) {
              nodeCosts.put(cost._1.name, cost._2)
            }
            variableCosts.put(node._1, nodeCosts)
          }
        case _ =>
          throw new IllegalArgumentException("use recursive or lattice-based as the smart-merging")
      }
    }


    val startTime = System.currentTimeMillis()
    try {
      Await.result(future, timeoutI.seconds)
    }
    catch {
      case e: TimeoutException =>
        println("Execution timed out!")
      case _: Throwable =>
    }

    val endTime = System.currentTimeMillis()
    output.write((endTime - startTime).toString.getBytes(StandardCharsets.UTF_8))

    0
  }
}

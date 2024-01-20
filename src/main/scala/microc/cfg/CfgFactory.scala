package microc.cfg

import microc.ProgramException
import microc.ast._
import microc.cli.Reporter
import microc.util.Counter
import microc.ast.AstNormalizer

import scala.collection.mutable


case class CfgConstructionException(message: String, loc: Loc) extends ProgramException(message + s" [$loc]") {
  override def format(reporter: Reporter): String = reporter.formatError("cfg", message, loc)
}


trait CfgFactory {
  var id = 0
  var preds: mutable.Set[CfgNode] = mutable.Set.empty
  val programCfg = new ProgramCfg()

  def addCell(cfgNode: CfgNode) = {
    preds.add(cfgNode)
    programCfg.add(cfgNode)
    id += 1
  }

  def addCfg(cfgNode: CfgNode) = {
    programCfg.add(cfgNode)
    for (pred <- preds) {
      cfgNode.pred.add(pred)
      pred.succ.add(cfgNode)
    }
    preds.clear()
    preds.add(cfgNode)
    id += 1
  }

  def isNormalizedVar(name: String): Boolean = {
    name.charAt(0) == '_' && name.charAt(1) == 't' && name.charAt(2).isDigit
  }

  def addCfgStmt(curr: AstNode, programCfg: ProgramCfg): CfgNode = {
    curr match {
      case stmt@WhileStmt(quard, block, _) =>
        val tmpPreds = mutable.Set.empty[CfgNode]
        val qNode = new CfgStmtNode(id, stmt)
        addCfg(qNode)
        tmpPreds.addAll(preds)
        var last: CfgNode = null
        block match {
          case NestedBlockStmt(body, _) =>
            for (stmt <- body) {
              last = addCfgStmt(stmt, programCfg)
            }
            qNode.pred.add(last)
            last.succ.add(qNode)
        }
        preds = tmpPreds
        qNode
      case stmt@IfStmt(quard, thenBranch, elseBranch, _) =>
        val tmpPreds = mutable.Set.empty[CfgNode]
        val qNode = new CfgStmtNode(id, stmt)
        addCfg(qNode)
        tmpPreds.addAll(preds)
        var last: CfgNode = null
        thenBranch match {
          case NestedBlockStmt(body, _) =>
            for (stmt <- body) {
              if (last == null) {
                last = addCfgStmt(stmt, programCfg)
                qNode.succ.add(last)
                last.pred.add(qNode)
              }
              else {
                last = addCfgStmt(stmt, programCfg)
              }
            }
            tmpPreds.add(last)
          case node =>
            addCfgStmt(node, programCfg)
        }
        last = null
        preds.clear()
        preds.add(qNode)
        elseBranch match {
          case Some(NestedBlockStmt(body, _)) =>
            for (stmt <- body) {
              if (last == null) {
                last = addCfgStmt(stmt, programCfg)
                //qNode.pred.add(last)
                //last.succ.add(qNode)
              }
              else {
                last = addCfgStmt(stmt, programCfg)
              }
            }
            tmpPreds.add(last)
          case None =>
        }
        preds = tmpPreds
        qNode
      case _ =>
        val res = new CfgStmtNode(id, curr)
        addCfg(res)
        res
    }
  }


  def fromProgram(p: Program): ProgramCfg = {
    for (f <- p.funs) {
      val fce = new CfgFunEntryNode(id, f)
      programCfg.addFce(fce)
      addCell(fce)
      if (f.block.vars.nonEmpty) {
        addCfgStmt(f.block.vars.last, programCfg)
      }
      for (s <- f.block.stmts) {
        addCfgStmt(s, programCfg)
      }
      addCfgStmt(f.block.ret, programCfg)
      addCfg(new CfgFunExitNode(id, f))
    }
    programCfg
  }
}

class IntraproceduralCfgFactory extends CfgFactory {}

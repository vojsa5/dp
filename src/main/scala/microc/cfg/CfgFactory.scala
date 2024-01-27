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
  var lastNode: Option[CfgNode] = None
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
        tmpPreds.addAll(preds)
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
    val normalized = new AstNormalizer().normalize(p)
    for (f <- normalized.funs) {
      val fce = new CfgFunEntryNode(id, f)
      programCfg.addFce(fce)
      addCell(fce)
      for (v <- f.block.vars) {
        addCfgStmt(v, programCfg)
      }
      for (s <- f.block.stmts) {
        addCfgStmt(s, programCfg)
      }
      addCfgStmt(f.block.ret, programCfg)
      addCfg(new CfgFunExitNode(id, f))
    }
    programCfg
  }

//  def simplifyExpression(expr: Expr): Expr = {
//    expr match {
//      case BinaryOp(op, left, right, loc) =>
//        BinaryOp(op, simplifyExpression(left), simplifyExpression(right), loc)
//      case CallFuncExpr(_, _, loc) =>
//        val iden = Identifier("_t" + id, loc)
//        id += 1;
//        val newNode = new CfgStmtNode(id, AssignStmt(iden, expr, loc))
//        newNode.succ.addAll(lastNode.get.succ)
//        newNode.pred.add(lastNode.get)
//        lastNode.get.succ.clear()
//        lastNode.get.succ.add(newNode)
//        lastNode = Some(newNode)
//        iden
//      case Not(expr, loc) =>
//        Not(simplifyExpression(expr), loc)
//      case Deref(pointer, loc) =>
//        Deref(simplifyExpression(pointer), loc)
//    }
//  }
//
//  def simplifyStatement(node: CfgNode): Unit = {
//    lastNode = Some(node)
//    preds = node.succ
//    node match {
//      case AssignStmt(_, right, _) =>
//        simplifyExpression(right)
//      case OutputStmt(expr, _) =>
//        simplifyExpression(expr)
//    }
//  }
//
//  def simplify(programCfg: ProgramCfg): ProgramCfg = {
//    val u = mutable.Set.empty[CfgNode]
//    for (node <- programCfg.nodes) {
//      node.ast match {
//        case AssignStmt(_, CallFuncExpr(_, _, _), _) =>
//        case _ => u.add(node)
//      }
//    }
//    programCfg
//  }
}

class IntraproceduralCfgFactory extends CfgFactory {}

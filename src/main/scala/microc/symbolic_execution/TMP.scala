package microc.symbolic_execution

import microc.analysis.Declarations
import microc.ast.{AssignStmt, Decl, FunDecl, Identifier, IfStmt, OutputStmt, ReturnStmt, VarStmt, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}

import scala.collection.mutable

class TMP(implicit declarations: Declarations, beta: Double = 0.7, kappa: Double = 1.0) {

  val mapping = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]


  def tmp2(programCfg: ProgramCfg): Unit = {
    programCfg.function.foreach(fce => tmp(fce, mutable.HashSet()))
  }

  def tmp(cfgNode: CfgNode, whiles: mutable.HashSet[WhileStmt]): mutable.HashMap[String, Double] = {
    cfgNode.ast match {
      case FunDecl(_, _, _, _) => {
        val res = mutable.HashMap[String, Double]()
        res.addAll(
          cfgNode.succ.map(node => tmp(node, whiles))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum)
            .toMap
        )
        mapping.put(cfgNode, res)
        res
      }
      case VarStmt(_, _) => {
        val res = mutable.HashMap[String, Double]()
        res.addAll(
          cfgNode.succ.map(node => tmp(node, whiles))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum)
            .toMap
        )
        mapping.put(cfgNode, res)
        res
      }
      case ReturnStmt(expr, _) => {
        val res = mutable.HashMap[String, Double]()
        for (id <- Utility.getIdentifiersThatCanCauseError(expr)) {
          res.put(id.name, res.getOrElse(id.name, 0.0) + 1.0)
        }
        mapping.put(cfgNode, res)
        res
      }
      case OutputStmt(expr, _) => {
        val res = mutable.HashMap[String, Double]()
        res.addAll(
          cfgNode.succ.map(node => tmp(node, whiles))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum)
            .toMap
        )
        for (id <- Utility.getIdentifiersThatCanCauseError(expr)) {
          res.put(id.name, res.getOrElse(id.name, 0.0) + 1.0)
        }
        mapping.put(cfgNode, res)
        res
      }
      case AssignStmt(left, right, _) => {
        val res = mutable.HashMap[String, Double]()
        res.addAll(
          cfgNode.succ.map(node => tmp(node, whiles))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum)
            .toMap
        )
        for (id <- Utility.getIdentifiersThatCanCauseError(right)) {
          res.put(id.name, res.getOrElse(id.name, 0.0) + 1.0)
        }
        left match {
          case id@Identifier(_, _) =>
            for (idToUpdate <- Utility.getAllIdentifierNames(right)) {
              res.put(idToUpdate.name, res.getOrElse(id.name, 0.0) + res.getOrElse(idToUpdate.name, 0.0))
            }
            res.remove(id.name)
          case _ =>
        }
        mapping.put(cfgNode, res)
        res
      }
      case w@WhileStmt(expr, _, _) => {
        if (whiles.contains(w)) {
          return mutable.HashMap()
        }
        val res = mutable.HashMap[String, Double]()
        for (v <- tmp(cfgNode.succ.minBy(node => node.id), whiles + w)) {
          res.put(v._1, v._2 * kappa)
        }
        for (v <- tmp(cfgNode.succ.maxBy(node => node.id), whiles + w)) {
          res.put(v._1, res.getOrElse(v._1, 0.0) + v._2)
        }
        for (id <- Utility.getAllIdentifierNames(expr)) {
          res.put(id.name, res.getOrElse(id.name, 0.0) + 1.0)
        }
        mapping.put(cfgNode, res)
        res
      }
      case IfStmt(expr, _, _, _) =>
        val res = mutable.HashMap[String, Double]()
        res.addAll(
          cfgNode.succ.map(node => tmp(node, whiles))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum * beta)
            .toMap
        )
        for (id <- Utility.getAllIdentifierNames(expr)) {
          res.put(id.name, res.getOrElse(declarations(id).name, 0.0) + 1.0)
        }
        mapping.put(cfgNode, res)
        res
    }
  }

}

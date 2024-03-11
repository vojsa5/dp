package microc.symbolic_execution

import microc.analysis.Declarations
import microc.ast.{AssignStmt, Decl, FunDecl, Identifier, IfStmt, OutputStmt, ReturnStmt, VarStmt, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}

import scala.collection.mutable

class TMP(implicit declarations: Declarations) {

  val mapping = new mutable.HashMap[CfgNode, mutable.HashMap[Decl, Double]]


  def tmp2(programCfg: ProgramCfg): Unit = {
    programCfg.function.foreach(fce => tmp(fce, mutable.HashSet()))
  }

  def tmp(cfgNode: CfgNode, whiles: mutable.HashSet[WhileStmt]): mutable.HashMap[Decl, Double] = {
    cfgNode.ast match {
      case FunDecl(_, _, _, _) => {
        val res = mutable.HashMap[Decl, Double]()
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
        val res = mutable.HashMap[Decl, Double]()
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
        val res = mutable.HashMap[Decl, Double]()
        for (name <- Utility.getIdentifiersThatCanCauseError(expr)) {
          res.put(name, res.getOrElse(name, 0.0) + 1.0)
        }
        mapping.put(cfgNode, res)
        res
      }
      case OutputStmt(expr, _) => {
        val res = mutable.HashMap[Decl, Double]()
        res.addAll(
          cfgNode.succ.map(node => tmp(node, whiles))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum)
            .toMap
        )
        for (name <- Utility.getIdentifiersThatCanCauseError(expr)) {
          res.put(name, res.getOrElse(name, 0.0) + 1.0)
        }
        mapping.put(cfgNode, res)
        res
      }
      case AssignStmt(left, right, _) => {
        val res = mutable.HashMap[Decl, Double]()
        res.addAll(
          cfgNode.succ.map(node => tmp(node, whiles))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum)
            .toMap
        )
        for (id <- Utility.getIdentifiersThatCanCauseError(right)) {
          res.put(id, res.getOrElse(id, 0.0) + 1.0)
        }
        left match {
          case id@Identifier(_, _) =>
            for (idToUpdate <- Utility.getAllIdentifierNames(right)) {
              res.put(idToUpdate, res.getOrElse(id, 0.0) + res.getOrElse(idToUpdate, 0.0))
            }
            res.remove(id)
          case _ =>
        }
        mapping.put(cfgNode, res)
        res
      }
      case w@WhileStmt(expr, _, _) => {
        if (whiles.contains(w)) {
          return mutable.HashMap()
        }
        val res = mutable.HashMap[Decl, Double]()
        res.addAll(
          cfgNode.succ.map(node => tmp(node, whiles + w))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum)
            .toMap
        )
        for (name <- Utility.getAllIdentifierNames(expr)) {
          res.put(name, res.getOrElse(name, 0.0) + 1.0)
        }
        mapping.put(cfgNode, res)
        res
      }
      case IfStmt(expr, _, _, _) =>
        val res = mutable.HashMap[Decl, Double]()
        res.addAll(
          cfgNode.succ.map(node => tmp(node, whiles))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum)
            .toMap
        )
        for (name <- Utility.getAllIdentifierNames(expr)) {
          res.put(name, res.getOrElse(declarations(name), 0.0) + 1.0)
        }
        mapping.put(cfgNode, res)
        res
    }
  }

}

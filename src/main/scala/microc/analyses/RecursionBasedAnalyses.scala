package microc.analyses

import microc.analysis.Declarations
import microc.ast.{AssignStmt, FunDecl, Identifier, IfStmt, OutputStmt, ReturnStmt, VarStmt, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}
import microc.symbolic_execution.Utility

import scala.collection.mutable

class RecursionBasedAnalyses(implicit declarations: Declarations, beta: Double = 1.0, kappa: Double = 1.0) {

  val mapping = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]


  def compute(programCfg: ProgramCfg): Unit = {
    programCfg.function.foreach(fce => computeNode(fce, mutable.HashSet()))
  }

  def computeNode(cfgNode: CfgNode, whiles: mutable.HashSet[WhileStmt]): mutable.HashMap[String, Double] = {
    cfgNode.ast match {
      case FunDecl(_, _, _, _) => {
        val res = mutable.HashMap[String, Double]()
        res.addAll(
          cfgNode.succ.map(node => computeNode(node, whiles))
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
          cfgNode.succ.map(node => computeNode(node, whiles))
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
          cfgNode.succ.map(node => computeNode(node, whiles))
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
          cfgNode.succ.map(node => computeNode(node, whiles))
            .flatMap(_.toList)
            .groupBy(_._1)
            .view
            .mapValues(_.map(_._2).sum)
            .toMap
        )
        for (id <- Utility.getIdentifiersThatCanCauseError(right)) {
          res.put(id.name, res.getOrElse(id.name, 0.0) + 1.0)
        }
        var removeLeft = true
        left match {
          case id@Identifier(name, _) =>
            for (idToUpdate <- Utility.getAllIdentifierNames(right)) {
              if (name == idToUpdate.name) {
                removeLeft = false
              }
              else {
                val newVal = res.getOrElse(id.name, 0.0) + res.getOrElse(idToUpdate.name, 0.0)
                if (newVal != 0) {
                  res.put(idToUpdate.name, newVal)
                }
              }
            }
            if (removeLeft) {
              res.remove(id.name)
            }
          case _ =>
        }
        mapping.put(cfgNode, res)
        res
      }
      case w@WhileStmt(expr, _, _) => {
        if (whiles.contains(w)) {
          if (mapping.contains(cfgNode)) {
            return mapping(cfgNode)
          }
          return mutable.HashMap[String, Double]()
        }
        val res = mutable.HashMap[String, Double]()

        val newWhiles = mutable.HashSet[WhileStmt]()
        newWhiles.addAll(whiles)
        newWhiles.add(w)
        for (id <- Utility.getAllIdentifierNames(expr)) {
          res.put(id.name, 1.0)
        }
        for (v <- computeNode(cfgNode.succ.maxBy(node => node.id), newWhiles)) {
          res.put(v._1, res.getOrElse(v._1, 0.0) + v._2)
        }
        mapping.put(cfgNode, res)
        for (v <- computeNode(cfgNode.succ.minBy(node => node.id), newWhiles)) {
          res.put(v._1, res.getOrElse(v._1, 0.0) + v._2 * kappa)
        }
        mapping.put(cfgNode, res)
        res
      }
      case IfStmt(expr, _, _, _) =>
        val res = mutable.HashMap[String, Double]()
        res.addAll(computeNode(cfgNode.succ.head, whiles))
        for (v <- computeNode(cfgNode.succ.tail.head, whiles)) {
          res.put(v._1, res.getOrElse(v._1, 0.0) + v._2)
        }
        for (id <- Utility.getAllIdentifierNames(expr)) {
          res.put(id.name, res.getOrElse(declarations(id).name, 0.0) + 1.0)
        }
        mapping.put(cfgNode, res)
        res
    }
  }

}

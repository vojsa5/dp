package microc.analysis

import microc.analyses.laticce.PowerSetLattice
import microc.ast.{Alloc, AssignStmt, AstNode, BinaryOp, CallFuncExpr, Decl, Divide, Expr, Identifier, IfStmt, Input, Not, Null, Number, OutputStmt, ReturnStmt, VarStmt, WhileStmt}
import microc.cfg.{CfgFunExitNode, CfgNode, CfgStmtNode, ProgramCfg}
import microc.symbolic_execution.Utility


import scala.collection.immutable.HashSet

/** A variable is live at a program point if there exists an execution in which its value will be read later without
 * being written to in between. For each of the CFG node the analysis provides a set of variables that are live
 * *before* the node executes.
 * @param cfg
 * @param declarations
 */
class QueryCountAnalyses(cfg: ProgramCfg)(implicit declarations: Declarations) extends DataflowAnalysis(cfg)(declarations) {
  type NodeElem = Set[(Decl, Double)]
  override def analyze(): ProgLattice#Element = {
    var decls = new HashSet[(Decl, Double)]
    for (decl <- cfg.nodes.flatMap(node => getDecls(node.ast))) {
      decls = decls + ((decl, 0))
    }
    fixPoint(new ProgLattice(Set.empty, new PowerSetLattice[(Decl, Double)](decls)), Directions.Backward)
  }


  override def mergeTheSameStates(state: Set[(Decl, Double)]): Set[(Decl, Double)] = {
    HashSet(state.groupBy(_._1).view.mapValues(_.map(_._2).sum).map(t => (t._1, if (t._2 > 10) 10 else t._2)).toSeq: _*)
  }

  override def transferFun(progLattice: ProgLattice, node: CfgNode, state: NodeElem): NodeElem = {
    var res = state
    res = node match {
      case CfgStmtNode(VarStmt(decls, _)) =>
        state.filter(decl => !decls.contains(decl))
      case CfgStmtNode(AssignStmt(id: Identifier, right, _)) =>

        val checks = res.find(_._1.name == id.name) match {
          case Some(check) => check._2
          case None => 0.0
        }
        res = res.filter(decl => decl._1.name != id.name)
        for (v <- vars(right)) {
          if (!res.exists(_._1.name == v.name)) {
            res = res + ((v, checks + (if (Utility.expressionCanCauseError(right)) 1 else 0)))
          }
        }
        res
      case CfgStmtNode(OutputStmt(expr, _)) =>
        for (v <- vars(expr)) {
          val basic = res.find(_._1.name == v.name) match {
            case Some(value) => value._2
            case None => 0.0
          }
          res = res + ((v, basic + (if (Utility.expressionCanCauseError(expr)) 1 else 0)))
        }
        res
      case CfgStmtNode(ReturnStmt(expr, _)) =>
        for (v <- vars(expr)) {
          val basic = res.find(_._1.name == v.name) match {
            case Some(value) => value._2
            case None => 0.0
          }
          res = res + ((v, basic + (if (Utility.expressionCanCauseError(expr)) 1 else 0)))
        }
        res
      case CfgStmtNode(IfStmt(expr, _, _, _)) =>
        for (v <- vars(expr)) {
          val basic = res.find(_._1.name == v.name) match {
            case Some(value) => value._2 + 1
            case None => 1.0
          }
          res = res + ((v, basic + (if (Utility.expressionCanCauseError(expr)) 2 else 0)))
        }
        res
      case CfgStmtNode(WhileStmt(expr, _, _)) =>
        for (v <- vars(expr)) {
          val basic = res.find(_._1.name == v.name) match {
            case Some(value) => value._2 + 1
            case None => 1.0
          }
          res = res + ((v, basic + (if (Utility.expressionCanCauseError(expr)) 2 else 0)))
        }
        res
      case CfgFunExitNode(_) =>
        Set.empty
      case _ =>
        state
    }
    return res
  }

}

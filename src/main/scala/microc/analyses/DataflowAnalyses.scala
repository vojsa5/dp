package microc.analysis

import microc.analyses.laticce.MapLattice
import microc.ast.{ArrayAccess, ArrayNode, AssignStmt, AstNode, BinaryOp, Decl, Expr, Identifier, IfStmt, Input, Number, OutputStmt, ReturnStmt, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}

import java.util




abstract class DataflowAnalysis(val cfg: ProgramCfg)(implicit declarations: Declarations) {

  type NodeElem
  type ProgLattice = MapLattice[CfgNode, NodeElem]

  def exps(node: Expr): Set[AstNode] = {
    node match {
      case b@BinaryOp(_, left, right, _) => exps(left) ++ exps(right) ++ Set(b)
      case _ => Set.empty
    }
  }

  def getExprs(node: AstNode): Set[AstNode] = {
    node match {
      case AssignStmt(_, right, _) =>
        exps(right)
      case OutputStmt(expr, _) =>
        exps(expr)
      case ReturnStmt(expr, _) =>
        exps(expr)
      case e: Expr =>
        exps(e)
      case _ =>
        Set.empty
    }
  }

  def vars(node: Expr): Set[Decl] = {
    node match {
      case id@Identifier(_, _) => Set(declarations(id))
      case BinaryOp(_, left, right, _) => vars(left) ++ vars(right)
      case Number(value, loc) => Set.empty
      case ArrayNode(elems, loc) => elems.flatMap(elem => vars(elem)).toSet
      case ArrayAccess(array, index, loc) => vars(array) ++ vars(index)
      case i@Input(_) => Set.empty
      case _ => Set.empty
    }
  }

  def getDecls(node: AstNode): Set[Decl] = {
    node match {
      case AssignStmt(_, right, _) =>
        vars(right)
      case OutputStmt(expr, _) =>
        vars(expr)
      case ReturnStmt(expr, _) =>
        vars(expr)
      case IfStmt(expr, _, _, _) =>
        vars(expr)
      case WhileStmt(expr, _, _) =>
        vars(expr)
      case _ =>
        Set.empty
    }
  }


  def analyze(): ProgLattice#Element = {
    ???
  }

  object Directions extends Enumeration {
    type Direction = Value
    val Forward, Backward = Value
  }

  def fixPoint(progLattice: ProgLattice): Map[CfgNode, NodeElem] = {
    var x = progLattice.bot
    var t = x
    do {
      t = x
      x = fun(progLattice, x, Directions.Forward)
    } while (x != t)
    x
  }

  def fixPoint(progLattice: ProgLattice, direction: Directions.Direction): Map[CfgNode, NodeElem] = {
    var x = progLattice.bot
    var workList = cfg.nodes.foldLeft(Set.empty[CfgNode])((p, n) => p + n)

    while (workList.nonEmpty) {
      val v = workList.head
      workList = workList.drop(1)
      val y = fun(v, progLattice, x, direction)
      if (x != y) {
        direction match {
          case Directions.Forward =>
            v.succ.foreach(n => workList = workList + n)
          case Directions.Backward =>
            v.pred.foreach(n => workList = workList + n)
        }
        x = y
      }
    }
    x

  }

  def fun(progLattice: ProgLattice, state: Map[CfgNode, NodeElem], direction: Directions.Direction): Map[CfgNode, NodeElem] = {
    cfg.nodes.toList.sortBy(node => node.id).foldLeft(Map.empty[CfgNode, NodeElem]) { (acc, node) =>
      acc + (node -> transferFun(progLattice, node, join(progLattice, node, state, direction)))
    }
  }

  def fun(cfgNode: CfgNode, progLattice: ProgLattice, state: Map[CfgNode, NodeElem], direction: Directions.Direction): Map[CfgNode, NodeElem] = {
    state + (cfgNode -> transferFun(progLattice, cfgNode, join(progLattice, cfgNode, state, direction)))
  }

  def join(progLattice: ProgLattice, node: CfgNode, state: Map[CfgNode, NodeElem], direction: Directions.Direction): NodeElem = {
    val prev: Set[NodeElem] = direction match {
      case Directions.Forward =>
        node.pred.map(w => state(w)).toSet
      case Directions.Backward =>
        node.succ.map(w => state(w)).toSet
    }
    val res = prev.foldLeft(progLattice.subLattice.bot)((acc, p) => progLattice.subLattice.lub(acc, p))
    mergeTheSameStates(res)
  }

  def transferFun(progLattice: ProgLattice, node: CfgNode, state: NodeElem): NodeElem = {???}

  def mergeTheSameStates(state: NodeElem): NodeElem = {
    state
  }
}


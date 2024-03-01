package microc.cfg

import microc.ast._

import scala.collection.mutable

abstract class CfgNode(val id: Int, var ast: AstNode) extends Ordered[CfgNode] {
  val pred: mutable.Set[CfgNode] = mutable.Set()

  val succ: mutable.Set[CfgNode] = mutable.Set()

  override def equals(obj: scala.Any): Boolean =
    obj match {
      case that: CfgNode => that.id == this.id
      case _             => false
    }

  override def hashCode(): Int = id

  override def compare(that: CfgNode): Int = this.id - that.id
}

class CfgStmtNode(id: Int, ast: AstNode) extends CfgNode(id, ast) {
  override def toString: String = s"$id: [$ast]"
}

object CfgStmtNode {
  def unapply(that: CfgNode): Option[AstNode] = that match {
    case x: CfgStmtNode => Some(x.ast)
    case _              => None
  }
}

class CfgFunEntryNode(id: Int, val fun: FunDecl) extends CfgNode(id, fun) {
  override def toString: String = s"$id: [fun entry: ${fun.name}]"
}

object CfgFunEntryNode {
  def unapply(that: CfgNode): Option[FunDecl] = that match {
    case x: CfgFunEntryNode => Some(x.fun)
    case _                  => None
  }
}

class CfgFunExitNode(id: Int, val fun: FunDecl) extends CfgNode(id, fun) {
  override def toString: String = s"$id: [fun exit: ${fun.name}]"
}

object CfgFunExitNode {
  def unapply(that: CfgNode): Option[FunDecl] = that match {
    case x: CfgFunExitNode => Some(x.fun)
    case _                 => None
  }
}

package microc.cfg

import microc.ast._

import scala.annotation.tailrec
import scala.collection.mutable

/** A control flow graph.
  *
  * This can be single statement, a sequence of statements, a complete function or a complete program.
  */
sealed class Cfg {

  protected val nodesCfg: mutable.Set[CfgNode] = mutable.Set.empty[CfgNode]

  /** Returns `true` if this is an empty CFG */
  def isEmpty: Boolean = nodesCfg.isEmpty

  /** Returns the set of nodes in the CFG. */
  def nodes: Set[CfgNode] = nodesCfg.toSet
}

class ProgramCfg extends Cfg {



  def add(node: CfgNode): Unit = {
    nodesCfg.add(node)
  }

  def addFce(node: CfgFunEntryNode): Unit = {
      functionsCfg.add(node)
  }

  def getFce(name: String): CfgFunEntryNode = {
    for (fce <- functionsCfg) {
      if (fce.fun.name == name) {
        return fce
      }
    }
    null
  }

  protected val functionsCfg: mutable.Set[CfgFunEntryNode] = mutable.Set.empty[CfgFunEntryNode]


  def function: mutable.Set[CfgFunEntryNode] = functionsCfg

  def allNodes: mutable.Set[CfgNode] = nodesCfg
}

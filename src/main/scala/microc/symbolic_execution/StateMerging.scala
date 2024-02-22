package microc.symbolic_execution

import microc.cfg.CfgNode

import scala.collection.mutable

class StateMerging {
  val states = mutable.HashMap[CfgNode, mutable.HashSet[SymbolicState]]()

  def addState(node: CfgNode, state: SymbolicState): Unit = {
    states.getOrElseUpdate(node, new mutable.HashSet[SymbolicState]()).add(state)
  }
}

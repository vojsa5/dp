package microc.symbolic_execution.optimizations.merging

import microc.cfg.CfgNode
import microc.symbolic_execution.{SearchStrategy, SymbolicState}

import scala.collection.mutable

trait StateMerging extends SearchStrategy {
  val states = mutable.HashMap[(CfgNode, Int), mutable.HashSet[SymbolicState]]()

  var statesToRemove = mutable.Set[SymbolicState]()
}

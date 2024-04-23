package microc.symbolic_execution.optimizations.merging

import microc.cfg.CfgNode
import microc.symbolic_execution.{StateHistory, SymbolicState}

import scala.collection.mutable

class DynamicStateMerging(
                           strategy: StateMerging,
                           stateHistory: StateHistory,
                           variableSolvingCosts: mutable.HashMap[CfgNode, mutable.HashMap[String, Double]],
                           limitCost: Double,
                           depth: Int
                         ) extends StateMerging {

  override def addState(state: SymbolicState): Unit = {
    strategy.addState(state)
  }

  override def getState(): SymbolicState = {
    for (cluster <- strategy.states) {
      for (alreadyExisting <- cluster._2) {
        for (alreadyExisting2 <- cluster._2) {
          if (alreadyExisting != alreadyExisting2) {
            if (stateHistory.stateSimilarToPredecessor(alreadyExisting, alreadyExisting2, depth, limitCost, variableSolvingCosts)) {
              return alreadyExisting
            }
          }
        }
      }
    }
    strategy.getState()
  }

  override def statesCount(): Int = strategy.statesCount()
}

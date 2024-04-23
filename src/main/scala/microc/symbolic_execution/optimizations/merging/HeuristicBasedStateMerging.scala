package microc.symbolic_execution.optimizations.merging

import microc.cfg.CfgNode
import microc.symbolic_execution.{SearchStrategy, SymbolicState}

import scala.collection.mutable

class HeuristicBasedStateMerging(strategy: SearchStrategy, variableSolvingCosts: mutable.HashMap[CfgNode, mutable.HashMap[String, Double]], limitCost: Double) extends StateMerging {
  override def addState(state: SymbolicState): Unit = {
    val newState = states.get((state.programLocation, state.symbolicStore.framesCnt())) match {
      case Some(alreadyExisting) => {
        for (existingState <- alreadyExisting) {
          if (state.isSimilarTo(existingState, limitCost, variableSolvingCosts(state.programLocation))) {
            statesToRemove.add(existingState)
            val merged = existingState.mergeStates(state)
            strategy.updateStateHistory(state, merged)
            states((state.programLocation, state.symbolicStore.framesCnt())).remove(existingState)
            states.getOrElseUpdate((state.programLocation, state.symbolicStore.framesCnt()), new mutable.HashSet[SymbolicState]()).add(merged)
            strategy.addState(merged)
            return
          }
        }
        state
      }
      case None =>
        state
    }
    states.getOrElseUpdate((state.programLocation, state.symbolicStore.framesCnt()), new mutable.HashSet[SymbolicState]()).add(newState)
    strategy.addState(newState)
  }

  override def getState(): SymbolicState = {
    val res = strategy.getState()
    if (statesToRemove.contains(res)) {
      statesToRemove.remove(res)
      return getState()
    }
    val statesCluster = states((res.programLocation, res.symbolicStore.framesCnt()))
    statesCluster.remove(res)
    if (statesCluster.isEmpty) {
      states.remove((res.programLocation, res.symbolicStore.framesCnt()))
    }
    res
  }

  override def statesCount(): Int = strategy.statesCount() - statesToRemove.size
}

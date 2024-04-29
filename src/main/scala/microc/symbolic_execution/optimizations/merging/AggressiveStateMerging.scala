package microc.symbolic_execution.optimizations.merging

import microc.symbolic_execution.{SearchStrategy, SymbolicState}

import scala.collection.mutable

class AggressiveStateMerging(strategy: SearchStrategy) extends StateMerging {

  override def addState(state: SymbolicState): Unit = {
    //println("ADD STATE(MERGING): ", states.map(state => state._1._1.id), statesCount(), state.nextStatement.id)
    val newState = states.get((state.programLocation, state.symbolicStore.framesCnt())) match {
      case Some(alreadyExisting) => {
        statesToRemove.add(alreadyExisting.last)
        val merged = alreadyExisting.last.mergeStates(state)
        strategy.updateExecutionTree(state, merged)
        merged
      }
      case None => state
    }
    states.remove((state.programLocation, state.symbolicStore.framesCnt()))
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

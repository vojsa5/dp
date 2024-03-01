package microc.symbolic_execution

import microc.cfg.CfgNode

import scala.collection.mutable



trait StateMerging extends SearchStrategy {
  val states = mutable.HashMap[(CfgNode, Int), mutable.HashSet[SymbolicState]]()

  var statesToRemove = mutable.Set[SymbolicState]()
}


class AgressiveStateMerging(strategy: SearchStrategy) extends StateMerging {

  override def addState(state: SymbolicState): Unit = {
    val newState = states.get((state.nextStatement, state.symbolicStore.framesCnt())) match {
      case Some(alreadyExisting) => {
        statesToRemove.add(alreadyExisting.last)
        val merged = alreadyExisting.last.mergeStates(state)
        new MergedSymbolicState(merged.nextStatement, merged.pathCondition, merged.symbolicStore, merged.callStack, (alreadyExisting.last, state))
      }
      case None => state
    }
    states.clear()
    states.getOrElseUpdate((state.nextStatement, state.symbolicStore.framesCnt()), new mutable.HashSet[SymbolicState]()).add(newState)
    strategy.addState(newState)
  }

  override def getState(): SymbolicState = {
    val res = strategy.getState()
    if (statesToRemove.contains(res)) {
      statesToRemove.remove(res)
      return getState()
    }
    res
  }

  override def statesCount(): Int = strategy.statesCount() - statesToRemove.size
}

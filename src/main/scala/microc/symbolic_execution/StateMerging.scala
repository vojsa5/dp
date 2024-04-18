package microc.symbolic_execution

import microc.ast.Decl
import microc.cfg.CfgNode

import scala.collection.mutable



trait StateMerging extends SearchStrategy {
  val states = mutable.HashMap[(CfgNode, Int), mutable.HashSet[SymbolicState]]()

  var statesToRemove = mutable.Set[SymbolicState]()
}


class HeuristicBasedStateMerging(strategy: SearchStrategy, variableSolvingCosts: mutable.HashMap[CfgNode, mutable.HashMap[String, Double]], limitCost: Double) extends StateMerging {
  override def addState(state: SymbolicState): Unit = {
    val newState = states.get((state.nextStatement, state.symbolicStore.framesCnt())) match {
      case Some(alreadyExisting) => {
        for (existingState <- alreadyExisting) {
          if (state.isSimilarTo(existingState, limitCost, variableSolvingCosts(state.nextStatement))) {
            statesToRemove.add(existingState)
            val merged = existingState.mergeStates(state)
            strategy.updateStateHistory(state, merged)
            states((state.nextStatement, state.symbolicStore.framesCnt())).remove(existingState)
            states.getOrElseUpdate((state.nextStatement, state.symbolicStore.framesCnt()), new mutable.HashSet[SymbolicState]()).add(merged)
            strategy.addState(merged)
            return
          }
        }
        state
      }
      case None =>
        state
    }
    states.getOrElseUpdate((state.nextStatement, state.symbolicStore.framesCnt()), new mutable.HashSet[SymbolicState]()).add(newState)
    strategy.addState(newState)
  }

  override def getState(): SymbolicState = {
    val res = strategy.getState()
    if (statesToRemove.contains(res)) {
      statesToRemove.remove(res)
      return getState()
    }
    val statesCluster = states((res.nextStatement, res.symbolicStore.framesCnt()))
    statesCluster.remove(res)
    if (statesCluster.isEmpty) {
      states.remove((res.nextStatement, res.symbolicStore.framesCnt()))
    }
    res
  }

  override def statesCount(): Int = strategy.statesCount() - statesToRemove.size
}

class AgressiveStateMerging(strategy: SearchStrategy) extends StateMerging {

  override def addState(state: SymbolicState): Unit = {
    //println("ADD STATE(MERGING): ", states.map(state => state._1._1.id), statesCount(), state.nextStatement.id)
    val newState = states.get((state.nextStatement, state.symbolicStore.framesCnt())) match {
      case Some(alreadyExisting) => {
        statesToRemove.add(alreadyExisting.last)
        val merged = alreadyExisting.last.mergeStates(state)
        strategy.updateStateHistory(state, merged)
        merged
      }
      case None => state
    }
    states.remove((state.nextStatement, state.symbolicStore.framesCnt()))
    states.getOrElseUpdate((state.nextStatement, state.symbolicStore.framesCnt()), new mutable.HashSet[SymbolicState]()).add(newState)
    strategy.addState(newState)
  }

  override def getState(): SymbolicState = {
    val res = strategy.getState()
    if (statesToRemove.contains(res)) {
      statesToRemove.remove(res)
      return getState()
    }
    val statesCluster = states((res.nextStatement, res.symbolicStore.framesCnt()))
    statesCluster.remove(res)
    if (statesCluster.isEmpty) {
      states.remove((res.nextStatement, res.symbolicStore.framesCnt()))
    }
    res
  }

  override def statesCount(): Int = strategy.statesCount() - statesToRemove.size
}


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



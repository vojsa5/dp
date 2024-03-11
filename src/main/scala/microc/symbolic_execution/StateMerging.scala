package microc.symbolic_execution

import microc.ast.Decl
import microc.cfg.CfgNode

import scala.collection.mutable
import scala.util.control.Breaks.break



trait StateMerging extends SearchStrategy {
  val states = mutable.HashMap[(CfgNode, Int), mutable.HashSet[SymbolicState]]()

  var statesToRemove = mutable.Set[SymbolicState]()
}


class HeuristicBasedStateMerging(strategy: SearchStrategy, variableSolvingCosts: mutable.HashMap[CfgNode, mutable.HashMap[Decl, Double]], limitCost: Double) extends StateMerging {
  override def addState(state: SymbolicState): Unit = {
    val i = state.symbolicStore.framesCnt()
    val newState = states.get((state.nextStatement, state.symbolicStore.framesCnt())) match {
      case Some(alreadyExisting) => {
        var cost = 0.0
        var lastState = state
        for (existingState <- alreadyExisting) {
          val variablesThatDiffers = existingState.symbolicStore.getDifferentVariables(existingState.symbolicStore)
          for (variable <- variablesThatDiffers) {
            val asf = variableSolvingCosts.get(existingState.nextStatement).getOrElse(variable, 0.0)
            //cost += variableSolvingCosts.get(state.nextStatement).getOrElse(variable, 0.0)
            null
          }
          if (cost <= limitCost) {
            statesToRemove.add(alreadyExisting.last)
            val merged = alreadyExisting.last.mergeStates(existingState)

            val i = states((state.nextStatement, state.symbolicStore.framesCnt()))
            states((state.nextStatement, state.symbolicStore.framesCnt())).remove(existingState)
            lastState = new MergedSymbolicState(merged.nextStatement, merged.pathCondition, merged.symbolicStore, merged.callStack, (state, existingState))
            states.getOrElseUpdate((state.nextStatement, state.symbolicStore.framesCnt()), new mutable.HashSet[SymbolicState]()).add(lastState)
            strategy.addState(lastState)
            return
          }
        }
        lastState
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
    val newState = states.get((state.nextStatement, state.symbolicStore.framesCnt())) match {
      case Some(alreadyExisting) => {
        statesToRemove.add(alreadyExisting.last)
        val merged = alreadyExisting.last.mergeStates(state)
        new MergedSymbolicState(merged.nextStatement, merged.pathCondition, merged.symbolicStore, merged.callStack, (alreadyExisting.last, state))
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

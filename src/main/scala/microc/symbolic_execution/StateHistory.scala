package microc.symbolic_execution

import microc.cfg.CfgNode

import scala.collection.mutable
import scala.util.Random


class StateHistory {
  val children = mutable.HashMap[SymbolicState, mutable.HashSet[SymbolicState]]()
  var unfinishedPaths = mutable.HashMap[SymbolicState, mutable.HashSet[SymbolicState]]()
  val preds = mutable.HashMap[SymbolicState, SymbolicState]()
  val random = new Random()
  var initial: SymbolicState = null
  var count = 0
  var initialRunned = false
  var stopRemovingUnfinishedPaths = false

  private def getChildrenOfNodes(symbolicState: SymbolicState): SymbolicState = {
    stopRemovingUnfinishedPaths = false
    unfinishedPaths.get(symbolicState) match {
      case None =>
        symbolicState
      case Some(states) =>
        val inner = states.toList(random.nextInt(states.size))
        val res = getChildrenOfNodes(inner)
        if (!stopRemovingUnfinishedPaths && unfinishedPaths.contains(symbolicState)) {
          unfinishedPaths(symbolicState).remove(inner)
          if (unfinishedPaths(symbolicState).isEmpty) {
            unfinishedPaths.remove(symbolicState)
          }
          else {
            stopRemovingUnfinishedPaths = true
          }
        }
        res
    }
  }

  def statesCount(): Int = count + (if (!initialRunned) 1 else 0)

  def getParent(state: SymbolicState): SymbolicState = {
    preds(state)
  }


  def getState(): SymbolicState = {
    count -= 1
    val res = getChildrenOfNodes(initial)
    if (res == initial) {
      initialRunned = false
    }
    res
  }

  private def updateSubstateCounts(symbolicState: SymbolicState): Unit = {
    preds.get(symbolicState) match {
      case Some(parent) =>
        val s = unfinishedPaths.getOrElse(parent, mutable.HashSet[SymbolicState]())
        s.add(symbolicState)
        unfinishedPaths.put(parent, s)
        updateSubstateCounts(parent)
      case None =>
    }
  }

  def addState(parentState: SymbolicState, newState: SymbolicState): Unit = {
    count += 1;
    addNode(parentState, newState)
    updateSubstateCounts(newState)
  }

  def addNode(parentState: SymbolicState, newState: SymbolicState): Unit = {
    val newChildren = children.getOrElse(parentState, mutable.HashSet())
    newChildren.add(newState)
    children.put(parentState, newChildren)
    preds.put(newState, parentState)
  }

  def removeStateInner(state: SymbolicState): Unit = {
    preds.get(state) match {
      case Some(parent) =>
        unfinishedPaths(parent).remove(state)
        if (unfinishedPaths(parent).isEmpty) {
          unfinishedPaths.remove(parent)
          removeStateInner(parent)
        }
      case None =>
    }
  }

  def removeState(state: SymbolicState): Unit = {
    count -= 1
    removeStateInner(state)
  }

  def stateSimilarToPredecessor(
                                 symbolicState1: SymbolicState,
                                 symbolicState2: SymbolicState,
                                 depth: Int,
                                 limitCost: Double,
                                 variableSolvingCosts: mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
                               ): Boolean = {
    if (symbolicState1.programLocation.id == symbolicState2.programLocation.id && symbolicState1.symbolicStore.framesCnt() == symbolicState2.symbolicStore.framesCnt()) {
      return symbolicState1.isSimilarTo(symbolicState2, limitCost, variableSolvingCosts(symbolicState1.programLocation))
    }
    if (depth == 0) {
      return false
    }
    preds.get(symbolicState2) match {
      case Some(pred) =>
        stateSimilarToPredecessor(symbolicState1, pred, depth - 1, limitCost, variableSolvingCosts)
      case None =>
        false
    }
  }

}

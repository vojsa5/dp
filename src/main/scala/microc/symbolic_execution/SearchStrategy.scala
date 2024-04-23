package microc.symbolic_execution

import microc.cfg.CfgNode

import java.util
import scala.collection.immutable.Queue
import scala.collection.mutable
import scala.util.Random

class RandomAccessSet[T] {//TODO look at this
  private val elements = mutable.ArrayBuffer[T]()
  private val indexMap = mutable.HashMap[T, Int]()
  private val random = new Random()

  def add(element: T): Unit = {
    if (!indexMap.contains(element)) {
      indexMap(element) = elements.length
      elements += element
    }
  }

  def popRandom(): Option[T] = {
    if (elements.isEmpty) {
      None
    } else {
      val randomIndex = random.nextInt(elements.length)
      val element = elements(randomIndex)
      removeElementAt(randomIndex)
      Some(element)
    }
  }

  private def removeElementAt(index: Int): Unit = {
    val lastElement = elements.last
    elements(index) = lastElement
    indexMap(lastElement) = index
    elements.remove(elements.length - 1)
    indexMap.remove(lastElement)
  }

  def isEmpty: Boolean = elements.isEmpty

  def size: Int = elements.length
}


trait SearchStrategy {

  def addState(symbolicState: SymbolicState): Unit

  def getState(): SymbolicState

  def statesCount(): Int

  def updateStateHistory(oldState: SymbolicState, newState: SymbolicState): Unit = {}
}


class BFSSearchStrategy extends SearchStrategy {

  var queue = Queue[SymbolicState]()

  override def addState(symbolicState: SymbolicState): Unit = {
    queue = queue.enqueue(symbolicState)
  }

  override def getState(): SymbolicState = {
    val (element, newQueue) = queue.dequeue
    queue = newQueue
    element
  }

  override def statesCount(): Int = this.queue.size
}


class DFSSearchStrategy extends SearchStrategy {

  var front = new util.LinkedList[SymbolicState]

  override def addState(symbolicState: SymbolicState): Unit = {
    front.add(symbolicState)
  }

  override def getState(): SymbolicState = {
    front.pop()
  }

  override def statesCount(): Int = this.front.size()
}


class RandomSearchStrategy extends SearchStrategy {

  var set = new RandomAccessSet[SymbolicState]

  override def addState(symbolicState: SymbolicState): Unit = {
    set.add(symbolicState)
  }

  override def getState(): SymbolicState = {
    set.popRandom().get
  }

  override def statesCount(): Int = set.size
}


class RandomPathSelectionStrategy(stateHistory: StateHistory) extends SearchStrategy {

  override def addState(symbolicState: SymbolicState): Unit = {}

  override def getState(): SymbolicState = {
    stateHistory.getState()
  }

  override def statesCount(): Int =
    stateHistory.statesCount()
}


class CoverageSearchStrategy(covered: mutable.HashSet[CfgNode]) extends SearchStrategy {

  var set = new mutable.HashSet[SymbolicState]

  private def nextUncoveredDistanceInner(cfgNode: CfgNode): Int = {
    if (!covered.contains(cfgNode)) {
      0
    }
    else {
      val nodesWithBiggerId = cfgNode.succ.filter(s => s.id >= cfgNode.id)
      if (nodesWithBiggerId.isEmpty) {
        return Int.MaxValue
      }
      cfgNode.succ.filter(s => s.id >= cfgNode.id).map(s => nextUncoveredDistanceInner(s)).min + 1
    }
  }

  private def nextUncoveredDistance(symbolicState: SymbolicState): Int =
    nextUncoveredDistanceInner(symbolicState.programLocation)

  override def addState(symbolicState: SymbolicState): Unit =
    set.add(symbolicState)

  override def getState(): SymbolicState = {
    val res = set.maxBy(nextUncoveredDistance)
    set.remove(res)
    res
  }

  override def statesCount(): Int =
    set.size
}


class KleeSearchStrategy(stateHistory: StateHistory, covered: mutable.HashSet[CfgNode]) extends SearchStrategy {
  val coverageSearchStrategy = new CoverageSearchStrategy(covered)
  val randomPathSearchStrategy = new RandomPathSelectionStrategy(stateHistory)

  var isCoverageStage = false

  override def addState(symbolicState: SymbolicState): Unit = {
    coverageSearchStrategy.addState(symbolicState)
  }

  override def getState(): SymbolicState = {
    val res = if (isCoverageStage) {
      isCoverageStage = false
      val res = coverageSearchStrategy.getState()
      stateHistory.removeState(res)
      res
    }
    else {
      isCoverageStage = true
      val res = randomPathSearchStrategy.getState()
      coverageSearchStrategy.set.remove(res)
      res
    }
    res
  }

  override def statesCount(): Int = {
    randomPathSearchStrategy.statesCount()
  }

  override def updateStateHistory(oldState: SymbolicState, newState: SymbolicState): Unit = {
    stateHistory.addState(stateHistory.getParent(oldState), newState)
    stateHistory.removeState(oldState)
  }
}

package microc.symbolic_execution

import microc.cfg.CfgNode

import java.util
import scala.collection.immutable.Queue
import scala.collection.mutable
import scala.util.Random

/**
 * A set-like data structure that supports poping random elements properly.
 *
 * @tparam T The type of elements stored in the set.
 */

class RandomAccessSet[T] {
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


/**
 * Defines a common interface for search strategies used in symbolic execution.
 * Search strategies dictate how states are selected for exploration.
 */


trait SearchStrategy {

  def addState(symbolicState: SymbolicState): Unit

  def getState(): SymbolicState

  def statesCount(): Int

  def updateExecutionTree(oldState: SymbolicState, newState: SymbolicState): Unit = {}
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


class TreeBasedStrategy(stateHistory: ExecutionTree) extends SearchStrategy {

  override def addState(symbolicState: SymbolicState): Unit = {}

  override def getState(): SymbolicState = {
    stateHistory.getState()
  }

  override def statesCount(): Int = {
    stateHistory.statesCount()
  }
}


class CoverageSearchStrategy(covered: mutable.HashSet[CfgNode]) extends SearchStrategy {

  var set = new mutable.HashSet[SymbolicState]

  private def nextUncoveredDistanceInner(cfgNode: CfgNode, limit: Int): Int = {
    if (!covered.contains(cfgNode) || limit < 0) {
      1
    }
    else {
      val nodesWithBiggerId = cfgNode.succ.filter(s => s.id >= cfgNode.id)
      if (nodesWithBiggerId.isEmpty) {
        return Int.MaxValue
      }
      cfgNode.succ.filter(s => s.id >= cfgNode.id).map(s => nextUncoveredDistanceInner(s, limit - 1)).min + 1
    }
  }

  private def nextUncoveredDistance(symbolicState: SymbolicState): Int =
    nextUncoveredDistanceInner(symbolicState.programLocation, 50)

  override def addState(symbolicState: SymbolicState): Unit =
    set.add(symbolicState)

  override def getState(): SymbolicState = {
    val weights = set.map(s => 1.0 / nextUncoveredDistance(s)).toSeq
    val totalWeight = weights.sum

    val normalizedWeights = weights.map(w => w / totalWeight)

    val cumulativeWeights = normalizedWeights.scanLeft(0.0)(_ + _).tail

    val randomValue = Random.nextDouble()
    val index = cumulativeWeights.indexWhere(cw => randomValue < cw)
    val res = set.toSeq(index)
    set.remove(res)
    res
  }

  override def statesCount(): Int =
    set.size
}


class KleeSearchStrategy(stateHistory: ExecutionTree, covered: mutable.HashSet[CfgNode]) extends SearchStrategy {
  val coverageSearchStrategy = new CoverageSearchStrategy(covered)
  val randomPathSearchStrategy = new TreeBasedStrategy(stateHistory)

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

  override def updateExecutionTree(oldState: SymbolicState, newState: SymbolicState): Unit = {
    stateHistory.addState(stateHistory.getParent(oldState), newState)
    stateHistory.removeState(oldState)
  }
}

package microc.symbolic_execution

import java.util
import scala.collection.immutable.Queue
import scala.collection.mutable
import scala.util.Random

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


trait SearchStreategy {

  def addState(symbolicState: SymbolicState): Unit

  def getState(): SymbolicState

  def statesCount(): Int

}


class BFSSearchStrategy extends SearchStreategy {

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


class DFSSearchStrategy extends SearchStreategy {

  var front = new util.LinkedList[SymbolicState]

  override def addState(symbolicState: SymbolicState): Unit = {
    front.add(symbolicState)
  }

  override def getState(): SymbolicState = {
    front.pop()
  }

  override def statesCount(): Int = this.front.size()
}


class RandomSearchStrategy extends SearchStreategy {

  var set = new RandomAccessSet[SymbolicState]

  override def addState(symbolicState: SymbolicState): Unit = {
    set.add(symbolicState)
  }

  override def getState(): SymbolicState = {
    set.popRandom().get
  }

  override def statesCount(): Int = set.size
}

package microc.util

class UnionFind[T] {

  var data: Map[T, T] = Map.empty

  /** Returns the union-find graph.
   *
   * @return
   * the graph
   */
  def graph: Map[T, T] = {
    data
  }

  /** Adds a new node `x` that initially is its own parent.
   *
   * @param x
   * a node
   */
  def makeSet(x: T): Unit = {
    data = data.updated(x, x)
  }

  /** Finds the canonical representative of `x` by traversing the path to the root, performing path compression on the
   * way—i.e. the parent of each node on the traversed path is set to the canonical representative.
   *
   * @param x
   * the node
   * @return
   * the canonical representation of the node `x`
   */
  def find(x: T): T = {
    var y: T = data(x)
    if (y != data(y))
      y = find(y)
    y
  }

  /** Makes y parent of x.
   *
   * @param x
   * a node
   * @param y
   * a node
   */
  def union(x: T, y: T): Unit = {
    val a = find(x)
    val b = find(y)
    if (a != b) {
      data = data.updated(a, b)
    }
  }


  def contains(x: T): Boolean = {
    data.get(x) match {
      case Some(_) => true
      case None => false
    }
  }

}


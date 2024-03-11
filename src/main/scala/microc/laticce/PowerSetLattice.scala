package microc.lattice

class PowerSetLattice[A](elements: Set[A]) extends Lattice[Set[A]] {
  override def top: Set[A] = {
    elements
  }

  override def bot: Set[A] = {
    Set.empty
  }

  override def lub(x: Set[A], y: Set[A]): Set[A] = {
    x.union(y)
  }
}

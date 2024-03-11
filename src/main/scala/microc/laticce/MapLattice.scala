package microc.lattice

/** A map lattice from a set of type `A` to sub-lattice of type `Lattice[B]`, ordered point-wise.
 *
 * @param subLattice
 *   the lattice the elements of type `A` maps to
 * @tparam A
 *   type of the set to be mapped to the lattice
 * @tparam B
 *   type of the elements in the sub-lattice
 */
class MapLattice[A, B](val domain: Set[A] , val subLattice: Lattice[B]) extends Lattice[Map[A, B]] {
  type SubLattice = Lattice[B]

  override val top: Map[A, B] = {
    Map().withDefaultValue(subLattice.top)
  }

  override val bot: Map[A, B] = {
    Map().withDefaultValue(subLattice.bot)
  }

  override def lub(x: Map[A, B], y: Map[A, B]): Map[A, B] = {
    x.keys.foldLeft(y)((acc, entry) => acc + (entry -> subLattice.lub(x(entry), y(entry))))
  }

  override def toString: String = super.toString
}


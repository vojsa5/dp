package microc.analyses.laticce

/** A complete lattice of elements of type 'A'.
 *
 * Implementation note: It would have been better to use type parameters instead as it would allow us to properly
 * encapsulate the `FlatLattice`. However, until https://youtrack.jetbrains.com/issue/SCL-20111 is fixed, such
 * implementation will result in IDEA complaining in `join`, and `transferFun` implementation in data flow analyses.
 *
 * @tparam A
 *   the type of elements in the lattice
 */
trait Lattice[A] {
  type Element = A

  /** Returns the ⊤ element */
  def top: A

  /** Returns the ⊥ element */
  def bot: A

  /** Returns the least upper bound ⨆{x,y} (`x` ⊔ `y`) */
  def lub(x: A, y: A): A
}


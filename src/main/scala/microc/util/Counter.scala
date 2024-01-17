package microc.util

class Counter[A](init: Int, f: Int => A) {
  private var counter = init
  def apply(): A = {
    val n = counter
    counter += 1
    f(n)
  }
}

object Counter {
  def apply(): Counter[Int] = new Counter[Int](0, identity)
  def apply[A](f: Int => A): Counter[A] = new Counter(0, f)
}

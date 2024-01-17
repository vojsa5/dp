package microc.util.fmt

import java.io.{StringWriter, Writer}
import scala.language.implicitConversions

trait Fmt[-A] {
  def apply(value: A): String = {
    val sw = new StringWriter()
    apply(value, sw)
    sw.toString
  }

  def apply(value: A, writer: Writer): Unit
}

object Fmt {
  def apply[A](value: A)(implicit fmt: Fmt[A]): String = fmt(value)
}

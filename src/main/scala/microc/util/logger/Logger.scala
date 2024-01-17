package microc.util.logger

import microc.util.CharacterSets.NL
import microc.util.fmt.Fmt

import java.io.{OutputStream, OutputStreamWriter, Writer}

sealed trait LogLevel extends Ordered[LogLevel] {
  def severity: Int
  override def compare(that: LogLevel): Int = this.severity - that.severity
}

case object Debug extends LogLevel {
  override def severity: Int = 1
}

case object Info extends LogLevel {
  override def severity: Int = 2
}

case object Error extends LogLevel {
  override def severity: Int = 3
}

trait Logger {
  def debug[A](obj: A)(implicit fmt: Fmt[A]): Unit = log(Debug, fmt(obj))
  def debug(msg: String): Unit = log(Debug, msg)
  def log(level: LogLevel, msg: String): Unit
}

class ConsoleLogger(out: Writer, minLevel: LogLevel) extends Logger {
  def this(out: OutputStream, maxLevel: LogLevel) =
    this(new OutputStreamWriter(out), maxLevel)

  override def log(level: LogLevel, msg: String): Unit =
    if (level >= minLevel) {
      out.write(msg + NL)
      out.flush()
    }
}

class IndentLogger(parent: Logger, indent: Int) extends Logger {
  var indentLevel: Int = 0
  override def log(level: LogLevel, msg: String): Unit = parent.log(level, " ".repeat(indentLevel * indent) + msg)
  def incLevel(): Unit = indentLevel += 1
  def decLevel(): Unit = indentLevel -= 1
}

object NoopLogger extends Logger {
  override def log(level: LogLevel, msg: String): Unit = {}
}

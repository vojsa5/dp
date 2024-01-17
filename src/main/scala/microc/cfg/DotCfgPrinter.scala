package microc.cfg

import microc.ast.AstPrinter
import microc.util.Collections._
import microc.util.IndentWriter
import microc.util.fmt.Fmt

import java.io.{StringWriter, Writer}

object DotCfgPrinter {
  private val Printer = new AstPrinter()
}

class DotCfgPrinter(indent: Int) {

  import DotCfgPrinter._

  def print(cfg: Cfg): String = {
    val sb: StringWriter = new StringWriter()
    print(cfg, sb)
    sb.toString
  }

  def print(cfg: Cfg, out: Writer): Unit = {
    visit(cfg, new IndentWriter(out, Some(indent)), None)
  }

  def print[A](cfg: Cfg, out: Writer, auxData: CfgNode => A)(implicit fmt: Fmt[A]): Unit = {
    visit(cfg, new IndentWriter(out, Some(indent)), Some(node => fmt(auxData(node))))
  }

  protected def visit(cfg: Cfg, writer: IndentWriter, auxData: Option[CfgNode => String]): Unit = {
    writer << "digraph CFG {"
    writer.indent {
      cfg.nodes.toList.sorted.foreachSep(n => visit(n, writer, auxData), writer.nl().nl())
    }
    writer << "}"
  }

  protected def id(node: CfgNode): String = "n_" + node.id

  protected def visit(node: CfgNode, writer: IndentWriter, auxData: Option[CfgNode => String]): Unit = {
    val labelPrefix = node match {
      case node: CfgFunEntryNode => s"Fun ${node.fun.name} entry"
      case node: CfgFunExitNode  => s"Fun ${node.fun.name} exit"
      case node: CfgStmtNode     => Printer.print(node.ast)
    }

    writer << id(node)
    writer << s"[label=\"$labelPrefix"
    auxData.foreach { f =>
      writer << "\\n"
      writer << f(node)
    }
    writer << s"\"]"

    if (node.succ.nonEmpty) {
      writer.nl()
    }

    node.succ.foreachSep(s => writer << id(node) + " -> " + id(s), writer.nl())
  }
}

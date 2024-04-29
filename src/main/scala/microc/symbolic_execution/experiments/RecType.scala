package microc.symbolic_execution.experiments

import scala.collection.mutable

case class RecType(fields: mutable.HashMap[String, VarType]) extends VarType {

  override def toString(): String = "rec -> " + fields.map(field => "( " + field._1 + " " + field._2.toString + " )")

  override def getInner(field: String): VarType = fields(field)
}

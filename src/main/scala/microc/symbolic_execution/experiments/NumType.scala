package microc.symbolic_execution.experiments

case class NumType() extends VarType {
  override def toString: String = "number"

  override def getInner(field: String): VarType = throw new UnsupportedOperationException()
}

package microc.symbolic_execution.experiments

case class PtrType(inner: VarType) extends VarType {
  override def toString: String = "pointer -> " + inner.toString

  override def getInner(field: String): VarType = inner
}

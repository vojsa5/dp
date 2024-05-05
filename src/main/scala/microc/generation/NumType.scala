package microc.generation

case class NumType() extends VarType {
  override def toString: String = "number"

  override def getInner(field: String): VarType = throw new UnsupportedOperationException()
}

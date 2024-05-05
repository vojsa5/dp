package microc.generation

case class ArrayType(innerType: VarType) extends VarType {
  override def toString: String = "array -> " + innerType.toString

  override def getInner(field: String): VarType = innerType
}

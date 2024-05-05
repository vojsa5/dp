package microc.generation

abstract class VarType {
  def toString(): String

  def getInner(field: String): VarType
}

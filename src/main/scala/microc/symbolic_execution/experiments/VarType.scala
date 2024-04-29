package microc.symbolic_execution.experiments

abstract class VarType {
  def toString(): String

  def getInner(field: String): VarType
}

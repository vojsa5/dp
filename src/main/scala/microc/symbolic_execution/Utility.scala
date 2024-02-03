package microc.symbolic_execution

object Utility {
  def varIsFromOriginalProgram(name: String): Boolean = {
    !(name.length > 2 && name(0) == '_' && name(1) == 't')
  }
}

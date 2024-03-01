package microc.symbolic_execution

import scala.util.Random

object Utility {
  def varIsFromOriginalProgram(name: String): Boolean = {
    !(name.length > 2 && name(0) == '_' && name(1) == 't')
  }

  def generateRandomString(): String = {
    (1 to 10).map(_ => "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"(new Random().nextInt(52))).mkString
  }
}

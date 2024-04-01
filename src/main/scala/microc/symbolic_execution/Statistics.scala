package microc.symbolic_execution

import sys.process._

class Statistics {
  var numPaths = 0
  var stoppedWithSubsumption = 0
  var summarizableLoops = 0

  def printStats(): Unit = {
    "clear".!;
    System.out.println(numPaths)
    System.out.println(stoppedWithSubsumption)
    System.out.println(summarizableLoops)
  }
}

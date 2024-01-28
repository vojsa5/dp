package microc.symbolic_execution

import microc.ast.{AssignStmt, StmtInNestedBlock, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}
import microc.symbolic_execution.Value.Symbolic

import java.util

class LoopSummary(program: ProgramCfg) extends SymbolicExecutor(program) {

  val fcs = new util.HashMap[String, Symbolic]()

  def executeBackbones(): Unit = {

  }

  def executeBackbone(): Unit = {

  }

  def computeSummary(loop: CfgNode): Unit = {
    val symbolicState = new SymbolicState(loop, PathCondition.initial())
    step(symbolicState)
  }

  override def stepOnLoop(symbolicState: SymbolicState, loop: WhileStmt): Unit = {
    val nextState = symbolicState.getIfFalseState()
    step(nextState)
    symbolicState.returnValue = nextState.returnValue
  }

}

package microc.symbolic_execution

import microc.ast.{Expr, IdentifierDecl}
import microc.cfg.CfgNode

class SymbolicStateNotAssiciatedWithAPath(symbolicState: SymbolicState) extends
  SymbolicState(symbolicState.programLocation, symbolicState.pathCondition, symbolicState.symbolicStore, symbolicState.callStack) {

  override def associatedPathsCount(): Int = 0

}

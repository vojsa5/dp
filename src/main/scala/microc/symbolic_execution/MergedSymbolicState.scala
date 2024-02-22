package microc.symbolic_execution

import microc.cfg.CfgNode

class MergedSymbolicState(nextStatement: CfgNode, pathCondition: PathCondition, symbolicStore: SymbolicStore, callStack: List[CfgNode] = List.empty, subStates: (SymbolicState, SymbolicState)) extends SymbolicState(nextStatement, pathCondition, symbolicStore, callStack) {

}

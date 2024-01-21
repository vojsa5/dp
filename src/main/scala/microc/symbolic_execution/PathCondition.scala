package microc.symbolic_execution

import microc.ast.Expr

class PathCondition(val prev: Option[PathCondition], val expr: Expr) {

}

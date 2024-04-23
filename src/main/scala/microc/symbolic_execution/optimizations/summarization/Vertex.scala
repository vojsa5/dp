package microc.symbolic_execution.optimizations.summarization

import microc.ast.Expr
import microc.symbolic_execution.Value.SymbolicVal
import microc.symbolic_execution.optimizations.Path

case class Vertex(path: Path, condition: Expr, change: List[(Expr, Expr => (Expr => Expr))], iterationsVal: SymbolicVal)

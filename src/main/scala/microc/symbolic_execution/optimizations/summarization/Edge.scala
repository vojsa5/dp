package microc.symbolic_execution.optimizations.summarization

import microc.ast.Expr
import microc.symbolic_execution.SymbolicState

import scala.collection.mutable

case class Edge(destination: Vertex, condition: Expr, change: mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr])

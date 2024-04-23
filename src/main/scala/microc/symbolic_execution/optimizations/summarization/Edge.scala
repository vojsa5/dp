package microc.symbolic_execution.optimizations.summarization

import microc.ast.Expr

import scala.collection.mutable

case class Edge(destination: Vertex, condition: Expr, change: mutable.HashMap[Expr, Expr => Expr])

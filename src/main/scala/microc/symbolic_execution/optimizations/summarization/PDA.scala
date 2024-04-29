package microc.symbolic_execution.optimizations.summarization

import com.microsoft.z3.Status
import microc.ast.{AndAnd, ArrayAccess, BinaryOp, BinaryOperator, CodeLoc, Deref, Expr, FieldAccess, Identifier, IdentifierDecl, Not, Number, VarRef}
import microc.symbolic_execution.Value._
import microc.symbolic_execution.optimizations._
import microc.symbolic_execution.{ConstraintSolver, SymbolicState, Utility}

import scala.collection.mutable

case class PDA(loopSummary: LoopSummarization, vertices: List[Vertex], variables: List[IdentifierDecl],
               solver: ConstraintSolver, precond: Expr, symbolicState: SymbolicState, mapping: mutable.HashMap[Val, Expr]) {

  val edges = new mutable.HashMap[Path, mutable.HashSet[Edge]]()
  val exitStates = new mutable.HashSet[Path]()
  val entryStates = new mutable.HashSet[Vertex]()


  def initialize(): Unit = {
    for (vertex <- vertices) {
      var newState = symbolicState.deepCopy()
      for (change <- vertex.change) {
        change._1 match {
          case Identifier(name, _) =>
            if (!Utility.varIsFromOriginalProgram(name) && !newState.containsVar(name)) {
              newState.updateVar(name, Utility.removeUnnecessarySymbolicExpr(
                SymbolicExpr(change._2.apply(Number(1, CodeLoc(0, 0))).apply(Number(1, CodeLoc(0, 0))), CodeLoc(0, 0)))
              )
            }
          case d@Deref(pointer, loc) =>
            newState.updateMemoryLocation(newState.getMemoryLoc(d), Utility.removeUnnecessarySymbolicExpr(
              SymbolicExpr(change._2.apply(Number(1, CodeLoc(0, 0))).apply(newState.getValAtMemoryLoc(d).asInstanceOf[Symbolic]), CodeLoc(0, 0)))
            )
          case a@ArrayAccess(_, _, _) =>
            newState.updateMemoryLocation(newState.getMemoryLoc(a), Utility.removeUnnecessarySymbolicExpr(
              SymbolicExpr(change._2.apply(Number(1, CodeLoc(0, 0))).apply(newState.getValAtMemoryLoc(a).asInstanceOf[Symbolic]), CodeLoc(0, 0)))
            )
          case f@FieldAccess(_, _, _) =>
            newState.updateMemoryLocation(newState.getMemoryLoc(f), Utility.removeUnnecessarySymbolicExpr(
              SymbolicExpr(change._2.apply(Number(1, CodeLoc(0, 0))).apply(newState.getValAtMemoryLoc(f).asInstanceOf[Symbolic]), CodeLoc(0, 0)))
            )
        }
      }
      solver.solveConstraint(solver.createConstraint(BinaryOp(AndAnd, vertex.condition, newState.pathCondition, CodeLoc(0, 0)), newState, true)) match {
        case Status.SATISFIABLE =>
          entryStates.add(vertex)
        case _ =>
      }
    }


    for (vertex1 <- vertices) {
      edges.put(vertex1.path, new mutable.HashSet())
      for (vertex2 <- vertices) {
        if (vertex1 != vertex2) {
          var newState = symbolicState.deepCopy()
          val edge = loopSummary.computePathRelationship(vertex1, vertex2, variables, mapping)
          if (edge.nonEmpty) {
            edges(vertex1.path).add(edge.get)
          }
        }
      }
    }
    for (edge <- edges.keys) {
      if (edges(edge).isEmpty) {
        exitStates.add(edge)
      }
    }
  }


  def summarizeType1Loop2(symbolicState: SymbolicState): Option[mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])]] = {
    var res: mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])] = mutable.HashSet()
    for (path <- entryStates) {
      val constraint = solver.createConstraint(BinaryOp(AndAnd, path.condition, symbolicState.pathCondition, CodeLoc(0, 0)), symbolicState, true)
      solver.solveConstraint(constraint) match {
        case Status.SATISFIABLE =>
          val trace = Traces()
          val summarizable = trace.summarizeTrace(
            this,
            symbolicState,
            path,
            Number(1, CodeLoc(0, 0)),
            new mutable.HashMap[Expr, Expr => Expr](),
            new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])]()
          )
          if (!summarizable) {
            return None
          }
          res.addAll(trace.res)
        case _ =>
          null
      }
    }
    Some(res)
  }

  def checkForConnectedCycles(): Boolean = {
    var cycles = Array[mutable.HashSet[Vertex]]()

    def dfs(v: Vertex, visited: mutable.HashSet[Vertex], recStack: List[Vertex]): Boolean = {
      if (!visited.contains(v)) {
        visited.add(v)
        val newStack: List[Vertex] = recStack.appended(v)

        for (neighbor <- edges.getOrElse(v.path, mutable.HashSet())) {
          if (!visited.contains(neighbor.destination) && dfs(neighbor.destination, visited, newStack)) {
            var startOfTheCycleFound = false
            val cycle = mutable.HashSet[Vertex]()
            for (v <- recStack) {
              if (!startOfTheCycleFound) {
                if (v == neighbor.destination) {
                  startOfTheCycleFound = true
                  cycle.add(v)
                }
              }
              else {
                cycle.add(v)
              }
            }
            cycles = cycles.appended(cycle)
            return true
          } else if (recStack.contains(neighbor.destination)) {
            var startOfTheCycleFound = false
            val cycle = mutable.HashSet[Vertex]()
            for (v <- recStack) {
              if (!startOfTheCycleFound) {
                if (v == neighbor.destination) {
                  startOfTheCycleFound = true
                  cycle.add(v)
                }
              }
              else {
                cycle.add(v)
              }
            }
            cycles = cycles.appended(cycle)
            return true
          }
        }
      }
      false
    }

    entryStates.foreach { vertex => dfs(vertex, mutable.HashSet[Vertex](), List()) }
    val seen = mutable.Set[Vertex]()
    for (cycle <- cycles) {
      for (v <- cycle) {
        if (seen.contains(v)) {
          return true
        }
        seen.add(v)
      }
    }
    false
  }


  def applyIterationsCount(expr: Expr, iterations: SymbolicVal, count: Expr): Expr = {
    expr match {
      case Not(expr, loc) =>
        Not(applyIterationsCount(expr, iterations, count), loc)
      case BinaryOp(operator, left, right, loc) =>
        BinaryOp(operator, applyIterationsCount(left, iterations, count), applyIterationsCount(right, iterations, count), loc)
      case id@Identifier(_, _) => id
      case n@Number(_, _) => n
      case v@SymbolicVal(_) =>
        if (v.name == iterations.name) {
          count
        }
        else {
          v
        }
      case SymbolicExpr(expr, _) => applyIterationsCount(expr, iterations, count)
      case p@PointerVal(_) => p
      case r@VarRef(id, _) => applyIterationsCount(id, iterations, count)
      case a@ArrVal(_) => a
    }
  }


  def combineFunctions(operation: BinaryOperator, oldFunction: Expr => Expr, newFunction: Expr => Expr): Expr => Expr = {
    expr => BinaryOp(operation, oldFunction.apply(expr), newFunction.apply(expr), CodeLoc(0, 0))
  }

}

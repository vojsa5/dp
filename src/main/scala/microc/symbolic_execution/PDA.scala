package microc.symbolic_execution

import com.microsoft.z3.Status
import microc.ast.{AndAnd, ArrayAccess, BinaryOp, BinaryOperator, CodeLoc, Expr, FieldAccess, GreaterEqual, Identifier, IdentifierDecl, Not, Number, OrOr, Plus, Program, VarRef, WhileStmt}
import microc.symbolic_execution.Value.{ArrVal, PointerVal, Symbolic, SymbolicExpr, SymbolicVal, Val}

import java.util
import scala.collection.mutable



case class Edge(destination: Vertex, condition: Expr, change: mutable.HashMap[Expr, Expr => Expr])
case class Vertex(path: Path, condition: Expr, change: List[(Expr, Expr => (Expr => Expr))], iterationsVal: SymbolicVal)


case class PDA(loopSummary: LoopSummary, vertices: List[Vertex], variables: List[IdentifierDecl],
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
              newState.addedVar(name, Utility.removeUnnecessarySymbolicExpr(
                SymbolicExpr(change._2.apply(Number(1, CodeLoc(0, 0))).apply(Number(1, CodeLoc(0, 0))), CodeLoc(0, 0)))
              )
            }
          case a@ArrayAccess(_, _, _) =>
            newState.setMemoryLocation(newState.getMemoryLoc(a), Utility.removeUnnecessarySymbolicExpr(
              SymbolicExpr(change._2.apply(Number(1, CodeLoc(0, 0))).apply(Number(1, CodeLoc(0, 0))), CodeLoc(0, 0)))
            )
          case f@FieldAccess(_, _, _) =>
            newState.setMemoryLocation(newState.getMemoryLoc(f), Utility.removeUnnecessarySymbolicExpr(
              SymbolicExpr(change._2.apply(Number(1, CodeLoc(0, 0))).apply(Number(1, CodeLoc(0, 0))), CodeLoc(0, 0)))
            )
        }
      }
      solver.solveConstraint(solver.createConstraintWithState(BinaryOp(AndAnd, vertex.condition, newState.pathCondition, CodeLoc(0, 0)), newState, true)) match {
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


  def summarizeType1Loop(symbolicState: SymbolicState, precond: Expr): (Expr, mutable.HashMap[Expr, mutable.HashSet[Expr => Expr]]) = {
    var res: (Expr, mutable.HashMap[Expr, mutable.HashSet[Expr => Expr]]) = (Number(1, CodeLoc(0, 0)), new mutable.HashMap[Expr, mutable.HashSet[Expr => Expr]]())
    for (path <- entryStates) {
      val trace = Trace()
      trace.summarizeTrace(
        this,
        symbolicState,
        path,
        BinaryOp(AndAnd, path.condition, precond, CodeLoc(0, 0)),
        new mutable.HashMap[Expr, Expr => Expr](),
        new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])]()
      )//TODO add precond
      for (changes <- trace.resChanges) {
        res._2.put(changes._1, changes._2)
      }
      res = (BinaryOp(AndAnd, trace.resCondition, res._1, CodeLoc(0, 0)), res._2)
    }
    res
  }


  def summarizeType1Loop2(symbolicState: SymbolicState): Option[mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])]] = {
    var res: mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])] = mutable.HashSet()
    for (path <- entryStates) {
      val constraint = solver.createConstraintWithState(BinaryOp(AndAnd, path.condition, symbolicState.pathCondition, CodeLoc(0, 0)), symbolicState, true)
      solver.solveConstraint(constraint) match {
        case Status.SATISFIABLE =>
          val trace = Trace()
          val summarizable = trace.summarizeTrace(
            this,
            symbolicState,
            path,
            //applyIterationsCount(solver.applyTheState(path.condition, symbolicState), path.iterationsVal, Number(0, CodeLoc(0, 0))),//initially 0 iterations performed
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
        Not(applyIterationsCount(expr, iterations,count), loc)
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


//  def combineFunctions(expr: Expr, expr2: Expr): Expr = {
//    expr => BinaryOp(Plus, expr, expr2, CodeLoc(0, 0))
//  }
}



case class Trace() {

  var resCondition: Expr = Number(1, CodeLoc(0, 0))
  var resChanges = new mutable.HashMap[Expr, mutable.HashSet[Expr => Expr]]()
  var res = new mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])]()


  def summarizeTrace2(
                       pda: PDA,
                       symbolicState: SymbolicState,
                       currPath: Vertex,
                       traceCondition: Expr,
                       updated_variables: mutable.HashMap[Expr, Expr => Expr],
                       rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])]
                     ): Boolean = {
    summarizeTrace(pda, symbolicState, currPath, traceCondition, updated_variables, rec)
  }


  def summarizeTrace(
                      pda: PDA,
                      symbolicState: SymbolicState,
                      currPath: Vertex,
                      traceCondition: Expr,
                      updated_variables: mutable.HashMap[Expr, Expr => Expr],
                      rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])]
                    ): Boolean = {
    if (rec.contains(currPath)) {
      constructCycleState(pda, rec, currPath, traceCondition, updated_variables, symbolicState) match {
        case Some(res) =>
          for (edge <- pda.edges(currPath.path)) {
            if (!rec.contains(edge.destination)) {
              summarizeTrace(pda, symbolicState, edge.destination, res._1, res._2, rec)
            }
          }
        case None =>
          return false
      }
    }
    else if (pda.exitStates.contains(currPath.path)) {
      if (rec.isEmpty) {
        res.add(BinaryOp(AndAnd, Utility.applyTheState(Not(currPath.condition, CodeLoc(0, 0)), symbolicState, true), traceCondition, CodeLoc(0, 0)), updated_variables)
      }
      else {
        res.add(traceCondition, updated_variables)
      }
    }
    else {
      for (edge <- pda.edges(currPath.path)) {
        val newState = symbolicState.deepCopy()
        val condition = Utility.simplifyArithExpr(BinaryOp(AndAnd, traceCondition, Utility.applyTheState(edge.condition, symbolicState, true), edge.condition.loc))
        pda.solver.solveConstraint(pda.solver.createConstraintWithState(condition, symbolicState, true)) match {
          case Status.SATISFIABLE =>
            val ncond = condition
            val nrec = new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])]()
            for (i <- rec) {
              nrec.put(i._1, i._2)
            }
            val newUpdatedVariables = mutable.HashMap[Expr, Expr => Expr]()
            for (update <- updated_variables) {
              newUpdatedVariables.put(update._1, update._2)
            }
            for (update <- edge.change) {
              if (newUpdatedVariables.contains(update._1)) {
                newUpdatedVariables.put(update._1, pda.combineFunctions(Plus, update._2, newUpdatedVariables(update._1)))
              }
              else {
                newUpdatedVariables.put(update._1, update._2)
                newState.setMemoryLocation(symbolicState.getMemoryLoc(update._1), Utility.removeUnnecessarySymbolicExpr(
                  SymbolicExpr(update._2.apply(symbolicState.getValAtMemoryLoc(update._1, true).asInstanceOf[Symbolic]), CodeLoc(0, 0)))
                )
              }
            }
            nrec.put(currPath, (ncond, edge.change))
            summarizeTrace(pda, newState, edge.destination, ncond, newUpdatedVariables, nrec)
          case _ =>
        }
      }
    }
    return true
  }

  def constructCycleState(pda: PDA, rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])],
                          currPath: Vertex, traceCondition: Expr, updated_variables: mutable.HashMap[Expr, Expr => Expr],
                          symbolicState: SymbolicState):
  Option[(Expr, mutable.HashMap[Expr, Expr => Expr])] = {
    val newUpdatedVariables = mutable.HashMap[Expr, Expr => Expr]()
    val newUpdatedVariables2 = mutable.HashMap[Expr, Expr => Expr]()
    val newState = symbolicState.deepCopy()
    for (update <- updated_variables) {
      newUpdatedVariables2.put(update._1, update._2)
    }
    val iterations = SymbolicVal(CodeLoc(0, 0))
    var initialConstraint: Expr = BinaryOp(GreaterEqual, iterations, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0))

    // get the cycle vertices
    val cycleRec = mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])]()
    var foundBeginningOfTheCycle = false
    for (r <- rec) {
      if (r._1 == currPath) {
        foundBeginningOfTheCycle = true
      }
      if (foundBeginningOfTheCycle) {
        cycleRec.put(r._1, r._2)
      }
    }

    // collect the cycle as a node
    var i = 0
    var lastNode = cycleRec.last
    val cycleRecWithNext = cycleRec.zip(cycleRec.drop(1) + cycleRec.head)
    for (r <- cycleRecWithNext) {
      for (update <- r._1._2._2) {
        val name = Utility.getName(update._1)
        if (newUpdatedVariables.contains(update._1) && Utility.varIsFromOriginalProgram(name)) {
          val prev = newUpdatedVariables(update._1)
          pda.loopSummary.computePeriod(lastNode._1, r._1._1, r._2._1) match {
            case Some(period) =>
              newUpdatedVariables.put(update._1, variable =>
                BinaryOp(
                  OrOr,
                  pda.applyIterationsCount(update._2.apply(variable), r._1._1.iterationsVal, Number(period, CodeLoc(0, 0))),
                  prev.apply(variable), CodeLoc(0, 0)
                )
              )
            case None =>
              return None
          }
        }
        else {
          newUpdatedVariables.put(update._1, update._2)
        }
      }
      i = i + 1
      lastNode = r._1
    }

    // apply the cycle
    for (update <- newUpdatedVariables) {
      if (newUpdatedVariables2.contains(update._1)) {
        newUpdatedVariables2.put(update._1, pda.combineFunctions(Plus, update._2, newUpdatedVariables2(update._1)))
      }
      else {
        newUpdatedVariables2.put(update._1, update._2)
        newState.setMemoryLocation(symbolicState.getMemoryLoc(update._1), Utility.removeUnnecessarySymbolicExpr(
          SymbolicExpr(update._2.apply(symbolicState.getValAtMemoryLoc(update._1, true).asInstanceOf[Symbolic]), CodeLoc(0, 0)))
        )
      }
    }


    Some((BinaryOp(AndAnd, traceCondition, initialConstraint, CodeLoc(0, 0)), newUpdatedVariables2))
  }

}

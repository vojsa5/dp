package microc.symbolic_execution

import com.microsoft.z3.Status
import microc.ast.{AndAnd, ArrayAccess, BinaryOp, BinaryOperator, CodeLoc, Expr, FieldAccess, GreaterEqual, Identifier, IdentifierDecl, Not, Number, OrOr, Plus, Program, VarRef, WhileStmt}
import microc.symbolic_execution.Value.{ArrVal, PointerVal, Symbolic, SymbolicExpr, SymbolicVal, Val}

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


  def summarizeType1Loop2(symbolicState: SymbolicState): mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])] = {
    var res: mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])] = mutable.HashSet()
    for (path <- entryStates) {
      val constraint = solver.createConstraintWithState(BinaryOp(AndAnd, path.condition, symbolicState.pathCondition, CodeLoc(0, 0)), symbolicState, true)
      println(constraint)
      solver.solveConstraint(constraint) match {
        case Status.SATISFIABLE =>
          val trace = Trace()
          trace.summarizeTrace2(
            this,
            symbolicState,
            path,
            //applyIterationsCount(solver.applyTheState(path.condition, symbolicState), path.iterationsVal, Number(0, CodeLoc(0, 0))),//initially 0 iterations performed
            Number(1, CodeLoc(0, 0)),
            new mutable.HashMap[Expr, Expr => Expr](),
            new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])]()
          )
          res.addAll(trace.res)
        case _ =>
          null
      }
    }
    res
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
  var cycleTrace: Option[Trace] = None
  var cycleTrace2: Option[(Expr, mutable.HashMap[Expr, Expr => Expr])] = None


  def summarizeTrace2(
                       pda: PDA,
                       symbolicState: SymbolicState,
                       currPath: Vertex,
                       traceCondition: Expr,
                       updated_variables: mutable.HashMap[Expr, Expr => Expr],
                       rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])]
                     ): Unit = {
    summarizeTrace(pda, symbolicState, currPath, traceCondition, updated_variables, rec)
    if (cycleTrace2.nonEmpty) {
      val newRes = new mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])]()
      for (changes <- res) {
        val changesWithCycles = new mutable.HashMap[Expr, Expr => Expr]
        for (change <- changes._2) {
          val changes2 = cycleTrace2.get._2
          if (changes2.contains(change._1)) {
            changesWithCycles.put(change._1, variable => change._2.apply(changes2(change._1).apply(variable)))
          }
          else {
            changesWithCycles.put(change._1, change._2)
          }
        }
        for (cycleChange <- cycleTrace2.get._2) {
          if (!changes._2.contains(cycleChange._1)) {
            changesWithCycles.put(cycleChange._1, cycleChange._2)
          }
        }
        newRes.add((BinaryOp(AndAnd, changes._1, cycleTrace2.get._1, CodeLoc(0, 0)), changesWithCycles))
      }
      res.addAll(newRes)
    }
  }


  def summarizeTrace(
                      pda: PDA,
                      symbolicState: SymbolicState,
                      currPath: Vertex,
                      traceCondition: Expr,
                      updated_variables: mutable.HashMap[Expr, Expr => Expr],
                      rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])]
                    ): Unit = {
    if (rec.contains(currPath)) {
      cycleTrace = Some(Trace())
      //constructCycleState(pda, symbolicState, rec, updated_variables, traceCondition)
      constructCycleState2(pda, rec, currPath)
      null
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
      var res: (Expr, mutable.HashMap[String, Expr => Expr]) = (Number(1, CodeLoc(0, 0)), new mutable.HashMap[String, Expr => Expr]())
      for (edge <- pda.edges(currPath.path)) {
        var newState = symbolicState.deepCopy()
        val c = BinaryOp(AndAnd, traceCondition, Utility.applyTheState(edge.condition, symbolicState, true), edge.condition.loc)
        val f = Utility.applyTheState(edge.condition, symbolicState, true)
        val condition = Utility.simplifyArithExpr(BinaryOp(AndAnd, traceCondition, Utility.applyTheState(edge.condition, symbolicState, true), edge.condition.loc))
        pda.solver.solveConstraint(pda.solver.createConstraintWithState(condition, symbolicState, true)) match {
          case Status.SATISFIABLE =>
            val ncond = condition//pda.solver.applyTheState(pda.solver.applyTheStateWithChangesAsFunctions(condition, symbolicState, edge.change), symbolicState)
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
                newUpdatedVariables.put(update._1, pda.combineFunctions(Plus, update._2, newUpdatedVariables(update._1)))//TODO check if correct
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
  }

  def constructCycleState2(pda: PDA, rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[Expr, Expr => Expr])], currPath: Vertex): Unit = {
    val newUpdatedVariables = mutable.HashMap[Expr, Expr => Expr]()
    val newUpdatedVariables2 = mutable.HashMap[Expr, Expr => Expr]()

    val iterations = SymbolicVal(CodeLoc(0, 0))
    var initialConstraint: Expr = BinaryOp(GreaterEqual, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0))

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

    for (r <- cycleRec) {
      initialConstraint = BinaryOp(AndAnd, initialConstraint, r._2._1, initialConstraint.loc)
      for (update <- r._2._2) {
        val name = Utility.getName(update._1)
        if (newUpdatedVariables.contains(update._1) && Utility.varIsFromOriginalProgram(name)) {
          val prev = newUpdatedVariables(update._1)
          newUpdatedVariables.put(update._1, variable => BinaryOp(OrOr, update._2.apply(variable), prev.apply(variable), CodeLoc(0, 0)))
        }
        else {
          newUpdatedVariables.put(update._1, update._2)
        }
      }
    }


    for (update <- newUpdatedVariables) {
      val tmp: Expr => Expr = variable => {
        val expr = update._2.apply(variable)
        if (LoopSummary.getSymbolicValsFromExpr(expr, pda.symbolicState).nonEmpty) {
          pda.applyIterationsCount(expr, LoopSummary.getSymbolicValsFromExpr(expr, pda.symbolicState).head, iterations)
        }
        else {
          expr
        }
      }
      newUpdatedVariables2.put(update._1, tmp)
    }

    cycleTrace2 = Some(initialConstraint, newUpdatedVariables2)

  }
}

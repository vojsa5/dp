package microc.symbolic_execution

import com.microsoft.z3.Status
import microc.ast.{AndAnd, BinaryOp, BinaryOperator, CodeLoc, Expr, Identifier, IdentifierDecl, Not, Number, OrOr, Plus}
import microc.symbolic_execution.Value.{SymbolicExpr, SymbolicVal}

import scala.collection.mutable



case class Edge(destination: Vertex, condition: Expr, change: mutable.HashMap[String, Expr => Expr])
case class Vertex(path: Path, condition: Expr, change: mutable.HashMap[String, Expr => (Expr => Expr)], iterationsVal: SymbolicVal)



case class PDA(loopSummary: LoopSummary, vertices: List[Vertex], variables: List[IdentifierDecl], solver: ConstraintSolver, precond: Expr, symbolicState: SymbolicState) {

  val edges = new mutable.HashMap[Path, mutable.HashSet[Edge]]()
  val exitStates = new mutable.HashSet[Path]()
  val entryStates = new mutable.HashSet[Vertex]()


  def initialize(): Unit = {
    for (vertex <- vertices) {
      solver.solveConstraint(solver.createConstraintWithState(BinaryOp(AndAnd, vertex.condition, precond, CodeLoc(0, 0)), symbolicState)) match {
        case Status.SATISFIABLE =>
          entryStates.add(vertex)
        case _ =>
      }
    }


    for (vertex1 <- vertices) {
      edges.put(vertex1.path, new mutable.HashSet())
      for (vertex2 <- vertices) {
        if (vertex1 != vertex2) {
          val edge = loopSummary.computePathRelationship(vertex1, vertex2, variables)
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


  def summarizeType1Loop(symbolicState: SymbolicState, precond: Expr): (Expr, mutable.HashMap[String, mutable.HashSet[Expr => Expr]]) = {
    var res: (Expr, mutable.HashMap[String, mutable.HashSet[Expr => Expr]]) = (Number(1, CodeLoc(0, 0)), new mutable.HashMap[String, mutable.HashSet[Expr => Expr]]())
    for (path <- entryStates) {
      val trace = Trace()
      trace.summarizeTrace(
        this,
        symbolicState,
        path,
        BinaryOp(AndAnd, path.condition, precond, CodeLoc(0, 0)),
        new mutable.HashMap[String, Expr => Expr](),
        new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]()
      )//TODO add precond
      for (changes <- trace.resChanges) {
        res._2.put(changes._1, changes._2)
      }
      res = (BinaryOp(AndAnd, trace.resCondition, res._1, CodeLoc(0, 0)), res._2)
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
  var resChanges = new mutable.HashMap[String, mutable.HashSet[Expr => Expr]]()
  var cycleTrace: Option[Trace] = None

  def summarizeTrace2(pda: PDA, symbolicState: SymbolicState, currPath: Vertex, traceCondition: Expr, updated_variables: mutable.HashMap[String, Expr => Expr], rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]): Unit = {

    summarizeTrace(pda, symbolicState, currPath, traceCondition, updated_variables, rec)
  }

  def summarizeTrace(pda: PDA, symbolicState: SymbolicState, currPath: Vertex, traceCondition: Expr, updated_variables: mutable.HashMap[String, Expr => Expr], rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]): Unit = {
    if (rec.contains(currPath)) {
      cycleTrace = Some(Trace())
      constructCycleState(pda, symbolicState, rec, updated_variables, traceCondition)
      null
    }
    else if (pda.exitStates.contains(currPath.path)) {
      resCondition = BinaryOp(AndAnd, resCondition, traceCondition, CodeLoc(0, 0))
      for (update <- updated_variables) {
        if (!resChanges.contains(update._1)) {
          resChanges.put(update._1, new mutable.HashSet())
        }
        resChanges(update._1).add(update._2)
      }
    }
    else {
      var res: (Expr, mutable.HashMap[String, Expr => Expr]) = (Number(1, CodeLoc(0, 0)), new mutable.HashMap[String, Expr => Expr]())
      for (edge <- pda.edges(currPath.path)) {
        val condition = LoopSummary.simplifyArithExpr(BinaryOp(AndAnd, traceCondition, pda.solver.applyTheState(edge.condition, symbolicState), edge.condition.loc))
        pda.solver.solveConstraint(pda.solver.createConstraintWithState(condition, symbolicState)) match {
          case Status.SATISFIABLE =>
            val ncond = pda.solver.applyTheState2(condition, symbolicState, edge.change)
            val nrec = new mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]()
            for (i <- rec) {
              nrec.put(i._1, i._2)
            }
            val newUpdatedVariables = mutable.HashMap[String, Expr => Expr]()
            for (update <- updated_variables) {
              newUpdatedVariables.put(update._1, update._2)
            }
            for (update <- edge.change) {
              if (newUpdatedVariables.contains(update._1)) {
                newUpdatedVariables.put(update._1, pda.combineFunctions(Plus, update._2, newUpdatedVariables(update._1)))
              }
              else {
                newUpdatedVariables.put(update._1, update._2)
              }
            }
            nrec.put(currPath, (ncond, edge.change))
            summarizeTrace(pda, symbolicState, edge.destination, ncond, newUpdatedVariables, nrec)
        }
      }
    }
  }

  def constructCycleState(pda: PDA, symbolicState: SymbolicState, rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])], updated_variables: mutable.HashMap[String, Expr => Expr], traceCondition: Expr) = {
    val interestingVars = new mutable.HashMap[String, Expr]()
    for (v <- pda.variables) {
      val expr: Expr = symbolicState.getSymbolicVal(v.name, v.loc) match {
        case v@SymbolicVal(_) => v
        case SymbolicExpr(expr, _) => expr
        case _ => throw new Exception("IMPLEMENT")
      }
      interestingVars.put(v.name, expr)
    }
    val period = rec.size - 1
    var condition: Expr = Number(1, CodeLoc(0, 0))
    val mergedChanges = new mutable.HashMap[String, Expr => Expr => Expr]()
    val cycleVertexIterations = SymbolicVal(CodeLoc(0, 0))
    for (r <- rec) {
      val vertex = r._1
      r._2._2.map {
        case (name, change) =>
          val iterationsCount = symbolicState.getSymbolicVal(name, CodeLoc(0, 0)) match {//TODO use for the condition
            case SymbolicExpr(expr, _) =>
              pda.applyIterationsCount(change.apply(expr), r._1.path.iterations, Number(1, CodeLoc(0, 0)))
            case v@SymbolicVal(_) =>
              pda.applyIterationsCount(change.apply(v), r._1.path.iterations, Number(1, CodeLoc(0, 0)))
            case _ =>
              throw new Exception("IMPLEMENT")
          }
          interestingVars.put(name, iterationsCount)

          if (mergedChanges.contains(name) && Utility.varIsFromOriginalProgram(name)) {//TODO should I ban non original vars here?
            val tmp = mergedChanges(name).apply(cycleVertexIterations)
            val tmp2 = vertex.change(name).apply(cycleVertexIterations)
            mergedChanges += name -> ((new_iterations) => (x) =>
              BinaryOp(
                Plus,
                pda.applyIterationsCount(tmp.apply(x), cycleVertexIterations, new_iterations),
                pda.applyIterationsCount(tmp2.apply(x), cycleVertexIterations, new_iterations),
                CodeLoc(0, 0)
              )
              )
          }
          else {
            mergedChanges += name -> ((new_iterations) => (x) => pda.applyIterationsCount(vertex.change(name).apply(cycleVertexIterations).apply(x), cycleVertexIterations, new_iterations)) //TODO there should be a merge here
          }
      }
      condition = BinaryOp(AndAnd, condition, r._2._1, CodeLoc(0, 0))
    }
    condition = LoopSummary.simplifyArithExpr(condition)
    val res = Vertex(new Path(List(), condition), condition, mergedChanges, SymbolicVal(CodeLoc(0, 0)))
    val cycleStates = new mutable.Queue[Vertex]()
    for (r <- rec) {
      cycleStates.append(r._1)
    }
    cycleStates.append(cycleStates.front)
    replaceCycle(pda, res, cycleStates, traceCondition, updated_variables, rec)
  }

  def replaceCycle(pda: PDA, newCycleVertex: Vertex, cycle: mutable.Queue[Vertex], traceCondition: Expr, mergedChanges: mutable.HashMap[String, Expr => Expr], rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]): Unit = {
    var cycleVertices = List[Vertex]()
    cycleVertices = cycleVertices.appended(newCycleVertex)
    cycleVertices = cycleVertices.appended(cycle(0))


    var lastV: Option[Vertex] = None
    var firstCondition: Option[Expr] = None
    var lastCondition: Option[Expr] = None
    val newChanges = new mutable.HashMap[String, Expr => Expr]()



    for (v <- cycle) {
      if (lastV.nonEmpty) {
        pda.edges(lastV.get.path).foreach(e => {
          if (e.destination == v) {
//            for (change <- e.change) {
//              if (newChanges.contains(change._1)) {
//                newChanges.put(change._1, pda.combineFunctions(change._2, newChanges(change._1)))
//              }
//              else {
//                newChanges.put(change._1, change._2)
//              }
//            }
            if (firstCondition.isEmpty) {
              firstCondition = Some(e.condition)
            }
          }
        })
      }
      lastV = Some(v)
      if (cycle(cycle.length - 2) == v) {//last before the first (repeated) one
        pda.edges(lastV.get.path).foreach(e =>
          if (e.destination == cycle(0)) {
            lastCondition = Some(e.condition)
          })
      }
    }
    val iterations = SymbolicVal(CodeLoc(0, 0))
    val firstEdge = Edge(newCycleVertex, firstCondition.get, mutable.HashMap())
    val lastEdge = Edge(cycle(cycle.length - 1), lastCondition.get, mergedChanges)
//    pda.edges(cycle(0).path).add(firstEdge)
//    pda.edges.put(newCycleVertex.path, new mutable.HashSet[Edge]())
//    pda.edges(newCycleVertex.path).add(lastEdge)
    val newPDA = PDA(pda.loopSummary, cycleVertices, pda.variables, pda.solver, pda.precond, pda.symbolicState)
    newPDA.edges.put(cycle(0).path, new mutable.HashSet[Edge]())
    newPDA.edges(cycle(0).path).add(firstEdge)
    newPDA.edges.put(newCycleVertex.path, new mutable.HashSet[Edge]())
    newPDA.edges(newCycleVertex.path).add(lastEdge)
    newPDA.exitStates.add(cycle(0).path)
    newPDA.entryStates.add(cycle(0))

    val x2 = mergedChanges("x").apply(Number(0, CodeLoc(0, 0)))

    mergedChanges.foreach(
      change => {
        newChanges += change._1 -> (x => {
          var res = change._2.apply(x)
          val symVals = LoopSummary.getSymbolicValsFromExpr(res)
          for (symVal <- symVals) {
            res = pda.applyIterationsCount(res, symVal, iterations)
          }
          res
        })
      }
    )

    val x = newChanges("x").apply(Number(0, CodeLoc(0, 0)))

    cycleTrace.get.summarizeTrace(newPDA, pda.symbolicState, cycle(0), traceCondition, newChanges, mutable.LinkedHashMap[Vertex, (Expr, mutable.HashMap[String, Expr => Expr])]())

    null
  }
}

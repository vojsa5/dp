package microc.symbolic_execution.optimizations.summarization

import com.microsoft.z3.Status
import microc.ast.{AndAnd, BinaryOp, CodeLoc, Expr, GreaterEqual, Not, Number, OrOr, Plus}
import microc.symbolic_execution.Value.{Symbolic, SymbolicExpr, SymbolicVal}
import microc.symbolic_execution.{SymbolicState, Utility}

import scala.collection.mutable

case class Traces() {

  var res = new mutable.HashSet[(Expr, mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr], mutable.HashSet[Expr])]()



  def summarizeTrace(
                      pda: PDA,
                      symbolicState: SymbolicState,
                      currPath: Vertex,
                      traceCondition: Expr,
                      updated_variables: mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr],
                      rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr])],
                      incrementedVars: mutable.HashSet[Expr]
                    ): Boolean = {
    if (rec.contains(currPath)) {
      constructCycleState(pda, rec, currPath, traceCondition, updated_variables, symbolicState) match {
        case Some(res) =>
          for (edge <- pda.edges(currPath.path)) {
            if (!rec.contains(edge.destination)) {
              summarizeTrace(pda, symbolicState, edge.destination, res._1, res._2, rec, incrementedVars)
            }
          }
        case None =>
          return false
      }
    }
    else if (pda.exitStates.contains(currPath.path)) {
      if (rec.isEmpty) {
        res.add(BinaryOp(AndAnd, Utility.applyTheState(Utility.applyPointers(Not(currPath.condition, CodeLoc(0, 0)), symbolicState), symbolicState, true), traceCondition, CodeLoc(0, 0)), updated_variables, incrementedVars)
      }
      else {
        res.add(traceCondition, updated_variables, incrementedVars)
      }
    }
    else {
      for (edge <- pda.edges(currPath.path)) {
        val newState = symbolicState.deepCopy()
        val condition = Utility.simplifyArithExpr(BinaryOp(AndAnd, traceCondition, Utility.applyTheState(Utility.applyPointers(edge.condition, symbolicState), symbolicState, true), edge.condition.loc))
        pda.solver.solveConstraint(pda.solver.createConstraint(condition, symbolicState, true)) match {
          case Status.SATISFIABLE =>
            val ncond = condition
            val nrec = new mutable.LinkedHashMap[Vertex, (Expr, mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr])]()
            for (i <- rec) {
              nrec.put(i._1, i._2)
            }
            val newUpdatedVariables = mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr]()
            for (update <- updated_variables) {
              newUpdatedVariables.put(update._1, update._2)
            }
            for (update <- edge.change) {
              if (newUpdatedVariables.contains(update._1)) {
                newUpdatedVariables.put(update._1, pda.combineFunctions(Plus, update._2, newUpdatedVariables(update._1)))
              }
              else {
                newUpdatedVariables.put(update._1, update._2)
                newState.updateMemoryLocation(symbolicState.getMemoryLoc(update._1), Utility.removeUnnecessarySymbolicExpr(
                  SymbolicExpr(update._2.apply(symbolicState.getValAtMemoryLoc(update._1, true).asInstanceOf[Symbolic]).apply(newState), CodeLoc(0, 0)))
                )
              }
            }
            nrec.put(currPath, (ncond, edge.change))
            if (!summarizeTrace(pda, newState, edge.destination, ncond, newUpdatedVariables, nrec, incrementedVars)) {
              return false
            }
          case _ =>
        }
      }
    }
    true
  }

  def constructCycleState(pda: PDA, rec: mutable.LinkedHashMap[Vertex, (Expr, mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr])],
                          currPath: Vertex, traceCondition: Expr, updated_variables: mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr],
                          symbolicState: SymbolicState):
  Option[(Expr, mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr])] = {
    val newUpdatedVariables = mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr]()
    val newUpdatedVariables2 = mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr]()
    val newState = symbolicState.deepCopy()
    for (update <- updated_variables) {
      newUpdatedVariables2.put(update._1, update._2)
    }
    val iterations = SymbolicVal(CodeLoc(0, 0))
    var initialConstraint: Expr = BinaryOp(GreaterEqual, iterations, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0))

    // get the cycle vertices
    val cycleRec = mutable.LinkedHashMap[Vertex, (Expr, mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr])]()
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
//        if (newUpdatedVariables.contains(update._1) && Utility.varIsFromOriginalProgram(name)) {
//          val prev = newUpdatedVariables(update._1)
//          pda.loopSummary.computePeriod(lastNode._1, r._1._1, r._2._1) match {
//            case Some(period) =>
//              newUpdatedVariables.put(update._1, variable => s =>
//                BinaryOp(
//                  OrOr,
//                  pda.applyIterationsCount(update._2.apply(variable).apply(s), r._1._1.iterationsVal, Number(period, CodeLoc(0, 0))),
//                  prev.apply(variable).apply(s), CodeLoc(0, 0)
//                )
//              )
//            case None =>
//              return None
//          }
//        }
//        else {
//          newUpdatedVariables.put(update._1, update._2)
//        }
        if (Utility.varIsFromOriginalProgram(name)) {
          pda.loopSummary.computePeriod(lastNode._1, r._1._1, r._2._1) match {
            case Some(period) =>
              newUpdatedVariables.put(update._1, variable => s =>
                pda.applyIterationsCount(update._2.apply(variable).apply(s), r._1._1.iterationsVal, Number(period, CodeLoc(0, 0)))
              )
            case None =>
              return None
          }
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
        newState.updateMemoryLocation(symbolicState.getMemoryLoc(update._1), Utility.removeUnnecessarySymbolicExpr(
          SymbolicExpr(update._2.apply(symbolicState.getValAtMemoryLoc(update._1, true).asInstanceOf[Symbolic]).apply(newState), CodeLoc(0, 0)))
        )
      }
    }


    Some((BinaryOp(AndAnd, traceCondition, initialConstraint, CodeLoc(0, 0)), newUpdatedVariables2))
  }

}

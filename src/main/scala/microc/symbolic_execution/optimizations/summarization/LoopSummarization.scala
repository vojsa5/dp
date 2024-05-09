package microc.symbolic_execution.optimizations.summarization

import com.microsoft.z3.{Context, IntNum, Status}
import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, AstPrinter, BinaryOp, CodeLoc, Deref, Expr, FieldAccess, GreaterEqual, GreaterThan, Identifier, IdentifierDecl, IfStmt, Input, Minus, NestedBlockStmt, Not, Number, Plus, Record, Stmt, Times, VarRef, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}
import microc.symbolic_execution.Value._
import microc.symbolic_execution._
import microc.symbolic_execution.optimizations.subsumption.PathSubsumption
import microc.symbolic_execution.optimizations.{summarization, _}

import scala.collection.mutable

object LoopSummarization {

  /**
   * Recursively collects all possible paths through a loop's body starting from a given CFG node.
   *
   * @param stmt current node of the loop.
   * @param loopId Identifier for the loop, used to prevent infinite recursion.
   * @param symbolicState The current state of symbolic execution at the loop's entry.
   * @param executor Instance of SymbolicExecutor used to update the general symbolic states.
   * @return A set of symbolic states representing execution of all paths.
   */

  def getAllPaths(stmt: CfgNode, loopId: Double, symbolicState: SymbolicState, executor: SymbolicExecutor): mutable.HashSet[SymbolicState] = {
    var paths = List[Path]()
    paths = paths.appended(new Path(List[Stmt](), Number(1, CodeLoc(0, 0)), List.empty, mutable.HashSet[Expr]()))
    var curr = stmt
    while (curr.id > loopId) {
      curr.ast match {
        case IfStmt(_, _, _, _) =>
          val trueBranch = Utility.getTrueBranch(curr)
          val elseBranch = Utility.getFalseBranch(curr)
          val trueState = symbolicState.deepCopy()
          val falseState = symbolicState.deepCopy()
          val res = getAllPaths(trueBranch, loopId, trueState, executor).addAll(getAllPaths(elseBranch, loopId, falseState, executor))
          return res
        case w@WhileStmt(_, _, _) =>
          if (curr.succ.contains(curr)) {
            return getAllPaths(curr.succ.filter(node => node.id != curr.id).head, curr.id, symbolicState, executor)
          }
          val res = mutable.HashSet[SymbolicState]()
          val thenStmt = curr.ast.asInstanceOf[WhileStmt].block.asInstanceOf[NestedBlockStmt].body.head
          for (state <- getAllPaths(curr.succ.filter(node => node.ast == thenStmt).head, curr.id, symbolicState, executor)) {
            res.addAll(getAllPaths(curr.succ.filter(node => node.ast != thenStmt).head, loopId, state, executor))
          }
          return res
        case otherStmt@AssignStmt(left, _, _) =>
          if (Utility.varIsFromOriginalProgram(Utility.getName(left))) {
            executor.stepOnAssign(otherStmt, symbolicState, true)
          }
          curr = curr.succ.head
        case _ =>
          curr = curr.succ.head
      }
    }
    val res = mutable.HashSet[SymbolicState]()
    res.add(symbolicState)
    res
  }

  def getSymbolicValsFromExpr(expr: Expr, symbolicState: SymbolicState): List[SymbolicVal] = {
    expr match {
      case Not(expr, loc) => getSymbolicValsFromExpr(expr, symbolicState)
      case BinaryOp(operator, left, right, loc) => getSymbolicValsFromExpr(left, symbolicState).appendedAll(getSymbolicValsFromExpr(right, symbolicState))
      case id@Identifier(_, _) => List.empty
      case n@Number(_, _) => List.empty
      case v@SymbolicVal(_) => List(v)
      case SymbolicExpr(expr, _) => getSymbolicValsFromExpr(expr, symbolicState)
      case VarRef(id, _) => getSymbolicValsFromExpr(id, symbolicState)
      case PointerVal(_) => List.empty
      case Alloc(expr, loc) => getSymbolicValsFromExpr(expr, symbolicState)
      case ArrayNode(elems, loc) =>
        elems.flatMap(elem => getSymbolicValsFromExpr(elem, symbolicState))
      case ArrVal(elems) =>
        elems.flatMap(elem => getSymbolicValsFromExpr(symbolicState.getValOnMemoryLocation(elem).get.asInstanceOf[Symbolic], symbolicState)).toList
      case RecVal(fields) =>
        fields.flatMap(field => getSymbolicValsFromExpr(symbolicState.getValOnMemoryLocation(field._2).get.asInstanceOf[Symbolic], symbolicState)).toList
    }
  }

  def getSymbolicRepressentation(v: Val, name: String, originalSymbolicState: SymbolicState,
                                 symbolicState: SymbolicState,
                                 mapping: mutable.HashMap[Val, Expr]): Val = {
    val res = v match {
      case ArrVal(elems) =>
        ArrVal(elems.map(elem => {
          getSymbolicRepressentation(originalSymbolicState.getValOnMemoryLocation(elem).get, name, originalSymbolicState, symbolicState, mapping)
          //in the recursive call the element is added to the last place
          PointerVal(symbolicState.symbolicStore.storage.size - 1)
        }))
      case RecVal(fields) =>
        RecVal(fields.map(field => {
          getSymbolicRepressentation(originalSymbolicState.getValOnMemoryLocation(field._2).get, name, originalSymbolicState, symbolicState, mapping)
          (field._1, PointerVal(symbolicState.symbolicStore.storage.size - 1))
        }))
      case p@PointerVal(_) =>
        getSymbolicRepressentation(originalSymbolicState.getValOnMemoryLocation(p).get, name, originalSymbolicState, symbolicState, mapping)
        PointerVal(symbolicState.symbolicStore.storage.size - 1)
      case _ =>
        if (mapping.contains(v)) {
          mapping(v).asInstanceOf[SymbolicVal]
        }
        else {
          SymbolicVal(CodeLoc(0, 0))
        }
    }
    symbolicState.updateVar(name, res)
    res
  }

  def fillMapping(idDecl: Expr, tmpSymVal: Val, mapping: mutable.HashMap[Val, Expr], state: SymbolicState): Unit = {
    mapping.put(tmpSymVal, idDecl)
    tmpSymVal match {
      case ArrVal(elems) =>
        var i = 0
        for (elem <- elems) {
          fillMapping(ArrayAccess(idDecl, Number(i, CodeLoc(0, 0)), CodeLoc(0, 0)), state.getValOnMemoryLocation(elem).get, mapping, state)
          i = i + 1
        }
      case RecVal(fields) => {
        for (field <- fields) {
          fillMapping(FieldAccess(idDecl, field._1, CodeLoc(0, 0)), state.getValOnMemoryLocation(field._2).get, mapping, state)
        }
      }
      case PointerVal(addr) =>
        fillMapping(Deref(idDecl, CodeLoc(0, 0)), state.getValOnMemoryLocation(PointerVal(addr)).get, mapping, state)
      case _ =>
    }
  }

  def createSymbolicStateWithAllValuesSymbolic(oldState: SymbolicState, mapping: mutable.HashMap[Val, Expr]): SymbolicState = {
    var newState = new SymbolicState(oldState.programLocation, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (v <- oldState.symbolicStore.lastFrameVars()) {
      val tmpSymVal = getSymbolicRepressentation(oldState.getValueOfVar(v, CodeLoc(0, 0), true), v, oldState, newState, mapping)
      fillMapping(Identifier(v, CodeLoc(0, 0)), tmpSymVal, mapping, newState)
    }
    newState
  }
}

class SummarizationResult(
                           val summary: mutable.HashSet[(Expr, mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr], mutable.HashSet[Expr])],
                           val state: SymbolicState,
                           val updatedVars: mutable.HashSet[Expr],
                           val incrementedVars: mutable.HashSet[Expr],
                           val locationsWithUnpredictability: mutable.HashSet[String]
                         )


class LoopSummarization(program: ProgramCfg,
                        subsumption: Option[PathSubsumption] = None,
                        ctx: Context = new Context(),
                        searchStrategy: SearchStrategy = new BFSSearchStrategy,
                        stateHistory: Option[ExecutionTree] = None,
                        covered: Option[mutable.HashSet[CfgNode]] = None,
                        printStats: Boolean = false
                 ) extends SymbolicExecutor(program, subsumption, ctx, searchStrategy, stateHistory, covered, printStats = printStats) {

  val loopPDAs = mutable.HashMap[CfgNode, (PDA, mutable.HashSet[Expr], mutable.HashSet[Expr], mutable.HashSet[String], mutable.HashMap[Val, Expr])]()

  val unsummarizableLoops = mutable.HashSet[CfgNode]()

  val printer = new AstPrinter()

  override def stepOnLoop(symbolicState: SymbolicState): Unit = {
    val mapping: mutable.HashMap[Val, Expr] = new mutable.HashMap[Val, Expr]()
    val summarizationRes = summarizeLoop(symbolicState, mapping)
    if (summarizationRes.nonEmpty) {
      val summary = summarizationRes.get.summary
      statistics.summarizableLoops += 1
      for (trace <- summary) {
        var tmpState = symbolicState.deepCopy()
        tmpState = tmpState.addLoopTrace(trace)

        for (change <- trace._2) {
          tmpState.applyChange(change._1, trace._2(change._1), mapping)
        }
        step(tmpState)
        symbolicState.returnValue = tmpState.returnValue
      }
    }
    else {
      super.stepOnLoop(symbolicState)
    }
  }

  val pathToVertex: mutable.LinkedHashMap[Path, List[(Expr, Expr => Expr => SymbolicState => Expr)]] = mutable.LinkedHashMap[Path, List[(Expr, Expr => Expr => SymbolicState => Expr)]]()
  val pathToState: mutable.HashMap[Path, SymbolicState] = mutable.HashMap[Path, SymbolicState]()
  var generalState: SymbolicState = null

  def getAllConditionsInALoop(cfg: ProgramCfg, loop: CfgNode): mutable.HashSet[Expr] = {
    val res = mutable.HashSet[Expr]()
    val minId = loop.id.toInt
    val maxId = loop.succ.maxBy(node => node.id).id.toInt
    for (i <- minId until maxId) {
      cfg.nodes.find(node => node.id == i).get.ast match {
        case WhileStmt(guard, _, _) =>
          res.add(guard)
        case IfStmt(guard, _, _, _) =>
          res.add(guard)
        case _ =>
      }
    }
    res
  }


  def summarizeLoop(symbolicState: SymbolicState, mapping: mutable.HashMap[Val, Expr]): Option[SummarizationResult] = {
    summarizeLoopInner(symbolicState.programLocation, symbolicState, None, mapping)
  }

  def getMemoryCellsFromConditions(exprs: mutable.HashSet[Expr]): mutable.HashSet[String] = {
    val res = mutable.HashSet[String]()
    for (expr <- exprs) {
      for (e <- Utility.getMemoryCellsFromAnExpr(expr)) {
        if (!res.contains(printer.print(e))) {
          res.add(printer.print(e))
        }
      }
    }
    res
  }

  private def summarizeLoopInner(loop: CfgNode, symbolicState: SymbolicState,
                                 newStateOpt: Option[SymbolicState], mapping: mutable.HashMap[Val, Expr]): Option[SummarizationResult] = {
    if (unsummarizableLoops.contains(loop)) {
      return None
    }
    val (pda, updatedVars, incrementedVars, locationsWithUnpredictability) = if (!loopPDAs.contains(loop)) {
      val updatedVars = mutable.HashSet[Expr]()
      val incrementedVars = mutable.HashSet[Expr]()
      val locationsWithUnpredictability = mutable.HashSet[String]()
      val allConditions: mutable.HashSet[Expr] = getAllConditionsInALoop(program, loop)
      val conditionMemoryCells: mutable.HashSet[String] = getMemoryCellsFromConditions(allConditions)
      val updatedBy: mutable.HashMap[String, mutable.HashSet[String]] = mutable.HashMap()
      var vertices: List[Vertex] = List()

      val innerMapping: mutable.HashMap[Val, Expr] = mutable.HashMap[Val, Expr]()

      val newState = newStateOpt match {
        case Some(s) => s
        case None =>
          LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping)
      }
      for (m <- mapping) {
        innerMapping.put(m._1, m._2)
      }
      val pathsOpt = getAllPathsInALoop(loop, symbolicState.deepCopy(), newState.deepCopy(), conditionMemoryCells,
        updatedBy, updatedVars, incrementedVars, locationsWithUnpredictability, innerMapping)
      if (pathsOpt.isEmpty) {
        unsummarizableLoops.add(loop)
        return None
      }
      val paths = pathsOpt.get
      for (path <- paths) {
        vertices = vertices.appended(summarization.Vertex(path, path.condition, pathToVertex(path), path.iterations))
      }
      val pda = PDA(this, vertices, solver, Number(1, CodeLoc(0, 0)), newState, mapping)
      pda.initialize()
      if (pda.checkForConnectedCycles()) {
        return None
      }
      loopPDAs.put(loop, (pda, updatedVars, incrementedVars, locationsWithUnpredictability, mapping))
      (pda, updatedVars, incrementedVars, locationsWithUnpredictability)
    }
    else {
      val pda = loopPDAs(loop)
      for (v <- pda._5) {
        mapping.put(v._1, v._2)
      }
      (pda._1, pda._2, pda._3, pda._4)
    }
    pda.summarizeType1Loop2(symbolicState) match {
      case Some(summary) =>
        Some(new SummarizationResult(summary, pda.symbolicState, updatedVars, incrementedVars, locationsWithUnpredictability))
      case None =>
        None
    }
  }


  def getAllLoopBodyPaths(stmt: CfgNode, loopId: Double, originalSymbolicState: SymbolicState, symbolicState: SymbolicState,
                          incrementedMemoryLocations: mutable.HashMap[PointerVal, Expr => Expr => SymbolicState => Expr],
                          updatedVars: mutable.HashSet[Expr], incrementedVars: mutable.HashSet[Expr],
                          conditionMemoryCells: mutable.HashSet[String], updatedBy: mutable.HashMap[String, mutable.HashSet[String]],
                          locationsWithUnpredictability: mutable.HashSet[String],
                          mapping: mutable.HashMap[Val, Expr], idMapping: mutable.HashMap[Identifier, Expr]): Option[List[Path]] = {
    var paths = List[Path]()
    paths = paths.appended(new Path(List[Stmt](), Number(1, CodeLoc(0, 0)), List.empty, mutable.HashSet[Expr]()))
    var curr = stmt
    while (curr.id > loopId) {
      curr.ast match {
        case IfStmt(guard, thenBranch, _, _) =>
          paths = paths.flatMap(
            path => {
              val trueBranch = Utility.getTrueBranch(curr)
              val elseBranch = Utility.getFalseBranch(curr)
              val trueState = symbolicState.deepCopy()
              val newUpdatedVars = new mutable.HashSet[Expr]
              newUpdatedVars.addAll(updatedVars)
              val newIncrementedVars = new mutable.HashSet[Expr]
              newIncrementedVars.addAll(incrementedVars)
              val newIncrementedVars2 = new mutable.HashSet[Expr]
              newIncrementedVars2.addAll(incrementedVars)
              var pathsOpt = getAllLoopBodyPaths(trueBranch, loopId, originalSymbolicState, trueState,
                incrementedMemoryLocations, newUpdatedVars, newIncrementedVars, conditionMemoryCells, updatedBy,
                locationsWithUnpredictability.clone(), mapping, idMapping)
              if (pathsOpt.isEmpty) {
                return None
              }
              paths = pathsOpt.get
                .map(pathContinuation => pathContinuation.addedCondition(Utility.applyToVarsFromStartingProgram(guard, idMapping)))
                .map(pathContinuation => path.appendedAsPath(pathContinuation))

              val falseState = symbolicState.deepCopy()
              val newUpdatedVars2 = new mutable.HashSet[Expr]
              newUpdatedVars2.addAll(updatedVars)

              pathsOpt = getAllLoopBodyPaths(elseBranch, loopId, originalSymbolicState, falseState,
                incrementedMemoryLocations, newUpdatedVars2, newIncrementedVars2, conditionMemoryCells, updatedBy,
                locationsWithUnpredictability.clone(), mapping, idMapping)
              updatedVars.addAll(newUpdatedVars)
              updatedVars.addAll(newUpdatedVars2)
              incrementedVars.addAll(newIncrementedVars)
              incrementedVars.addAll(newIncrementedVars2)
              if (pathsOpt.isEmpty) {
                return None
              }

              paths = paths.appendedAll(
                pathsOpt.get
                  .map(pathContinuation => pathContinuation.addedCondition(Utility.applyToVarsFromStartingProgram(Not(guard, guard.loc), idMapping)))
                  .map(pathContinuation => path.appendedAsPath(pathContinuation)))
              paths
            }
          )
          return Some(paths)
        case w@WhileStmt(_, _, _) =>
          val summaryOpt = summarizeLoopInner(curr, symbolicState.deepCopy(), Some(symbolicState), mapping)
          if (summaryOpt.isEmpty) {
            return None
          }
          val summary = summaryOpt.get
          val innerIncrementedVars = summary.incrementedVars
          incrementedVars.addAll(innerIncrementedVars)
          for (trace <- summary.summary) {
            symbolicState.addLoopTrace(trace)
            paths = paths.map(path => path.addedCondition(trace._1))
            for (update <- trace._2) {
              val name = Utility.getName(update._1)
              if (incrementedVars.contains(update._1)) {
                locationsWithUnpredictability.add(name)
              }
              if (summary.locationsWithUnpredictability.contains(name)) {
                locationsWithUnpredictability.add(name)
              }
              if (Utility.varIsFromOriginalProgram(name)) {
                  paths = paths.map(path => {
                    updatedVars.add(update._1)
                    if (innerIncrementedVars.contains(update._1)) {
                      path.updatedChanges(update._1,
                        iterations => x => s =>
                          Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, update._2.apply(x).apply(s), CodeLoc(0, 0)), CodeLoc(0, 0)))
                      )
                    }
                    else {
                      path.updatedChanges(update._1,
                        iterations => update._2
                      )
                    }
                  }
                )
                if (symbolicState.containsVar(name)) {
                  symbolicState.applyChange(update._1, update._2, mapping)
                }
              }
            }
          }
          curr = Utility.getFalseBranch(curr)
        case otherStmt@AssignStmt(left, right, _) =>
          left match {
            case id@Identifier(name, _) if !Utility.varIsFromOriginalProgram(name) =>
              idMapping.put(id, right)
            case _ =>
          }
          val changeOpt = computeVariableChange(otherStmt, symbolicState, incrementedMemoryLocations, updatedVars,
            incrementedVars, conditionMemoryCells, updatedBy, locationsWithUnpredictability, mapping)
          if (changeOpt.nonEmpty) {
            (left, right) match {
              case (_, BinaryOp(_, _, _, _)) =>
              case (id@Identifier(_, _), id2@Identifier(_, _)) =>
                val s = symbolicState.getValAtMemoryLoc(id2)
                if (mapping.contains(s)) {
                  mapping.put(s, left)
                }
              case _ =>
            }
            if (curr.succ.head.id > loopId) {
              stepOnAssign(otherStmt, symbolicState, true)
              stepOnAssign(otherStmt, originalSymbolicState, true)
            }
            val change = changeOpt.get
            change._1 match {
              case v@Identifier(name, loc) =>
                paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(v, change._2))
              case d@Deref(pointer, loc) =>
                paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(d, change._2))
              case a@ArrayAccess(array, index, _) =>
                paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(a, change._2))
              case f@FieldAccess(record, field, loc) =>
                paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(f, change._2))
            }
          }
          else {
            return None
          }
          curr = curr.succ.head
        case _ =>
          curr = curr.succ.head
      }
    }
    if (paths.size == 1) {
      paths.head.incrementedVariables = incrementedVars
    }
    for (path <- paths) {
      if (!pathToState.contains(path)) {
        pathToState.put(path, symbolicState)
      }
    }
    Some(paths)
  }


  private def sameSymbolicVal(state: SymbolicState, ptr1: PointerVal, ptr2: PointerVal): Boolean = state.getValOnMemoryLocation(ptr1) == state.getValOnMemoryLocation(ptr2)



/**
 * Computes the changes to a variable as a function
 *
 * @param stmt The statement to be analyzed.
 * @param symbolicState general state.
 * @param incrementedMemoryLocations A mapping from memory locations to functions that describe how their values are incremented.
 * @param updatedVariables A set of variables that are updated within the loop.
 * @param incrementedVariables A set of variables that are incremented within the loop.
 * @param conditionMemoryCells A set of memory locations present in the condition.
 * @param updatedBy A mapping of memory locations to the variables that update them, used to track dependencies.
 * @param locationsWithUnpredictability A set of memory locations known to introduce unpredictability into the execution, affecting determinism.
 * @param mapping A mapping between symbolic values in the general symbolic state and the values from the original variables
 * @return An Option containing a tuple of a left side of the assign statement and the update function.
 */



  def computeVariableChange(stmt: Stmt, symbolicState: SymbolicState,
                            incrementedMemoryLocations: mutable.HashMap[PointerVal, (Expr) => ((Expr) => SymbolicState => Expr)],
                            updatedVariables: mutable.HashSet[Expr], incrementedVariables: mutable.HashSet[Expr],
                            conditionMemoryCells: mutable.HashSet[String],
                            updatedBy: mutable.HashMap[String, mutable.HashSet[String]],
                            locationsWithUnpredictability: mutable.HashSet[String],
                            mapping: mutable.HashMap[Val, Expr]
                            ): Option[(Expr, Expr => Expr => SymbolicState => Expr)] = {
    stmt match {
      case AssignStmt(ArrayAccess(_, Identifier(_, _), _), _, _) =>
        None
      case AssignStmt(left, right, _) =>
        if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer) && conditionMemoryCells.contains(printer.print(left))) {
          return None
        }
        val leftSideMemoryLocation = symbolicState.getMemoryLoc(left)
        if (incrementedVariables.exists(v => v.equals(left))) {
          return None
        }
        val name = Utility.getName(left)
        locationsWithUnpredictability.remove(printer.print(left))
        if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer)) {
          locationsWithUnpredictability.add(printer.print(left))
        }
        for (loc <- Utility.getMemoryLocationsFromExpr(right, printer)) {
          if (printer.print(left) != loc) {
            val v = updatedBy.getOrElse(printer.print(left), mutable.HashSet())
            v.add(loc)
            updatedBy.put(printer.print(left), v)
          }
        }
        if (conditionMemoryCells.contains(printer.print(left))) {
          if (!Utility.isNotUpdatedByUnpredictableLoc(printer.print(left), locationsWithUnpredictability, updatedBy, mutable.HashSet[String]())){
            return None
          }
        }
        Utility.simplifyArithExpr(right) match {
          case BinaryOp(_, SymbolicVal(_), _, _) =>
            None
          case BinaryOp(_, _, SymbolicVal(_), _) =>
            None
          case BinaryOp(Plus, Identifier(name2, loc1), n@Number(_, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer)) {
              return None
            }
            val changeFunction: Expr => Expr => SymbolicState => Expr = (iterations => (x => s =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            updatedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Minus, Identifier(name2, loc1), Number(value, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer)) {
              return None
            }
            val changeFunction: Expr => Expr => SymbolicState => Expr = (iterations => (x => s =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            updatedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) &&
              incrementedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name3).get) =>
            None
          case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) &&
              incrementedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name3).get) =>
            None
          case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name3).get, leftSideMemoryLocation) &&
              incrementedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name2).get) =>
            None
          case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name3).get, leftSideMemoryLocation) &&
              incrementedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name2).get) =>
            None
          case BinaryOp(Plus, resId@Identifier(name2, loc1), id@Identifier(_, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer)) {
              return None
            }
            val v = symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic]
            val changeFunction: Expr => Expr => SymbolicState => Expr = (iterations => (x => s =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, v, loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            updatedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Minus, resId@Identifier(name2, loc1), id@Identifier(_, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer)) {
              return None
            }
            val v = symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic]
            val changeFunction: Expr => Expr => SymbolicState => Expr = (iterations => (x => s =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, BinaryOp(Minus, Number(0, CodeLoc(0, 0)), v, loc2), loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            updatedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Plus, n@Number(_, loc2), Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer)) {
              return None
            }
            val changeFunction: Expr => Expr => SymbolicState => Expr = (iterations => (x => s =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            updatedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Minus, Number(value, loc2), Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer)) {
              return None
            }
            val changeFunction: Expr => Expr => SymbolicState => Expr = (iterations => (x => s =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            updatedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Plus, id@Identifier(_, loc2), resId@Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer)) {
              return None
            }
            val v = symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic]
            val changeFunction: Expr => Expr => SymbolicState => Expr = (iterations => (x => s =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, v, loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            updatedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Minus, id@Identifier(_, loc2), resId@Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer)) {
              return None
            }
            val v = symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic]
            val changeFunction: Expr => Expr => SymbolicState => Expr = (iterations => (x => s =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, BinaryOp(Minus, Number(0, CodeLoc(0, 0)), v, loc2), loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            updatedVariables.add(left)
            Some(left, changeFunction)
          case expr: BinaryOp if !Utility.varIsFromOriginalProgram(name) =>
            updatedVariables.add(left)
            Some(left, (iterations => (x => s => Utility.simplifyArithExpr(expr))))
          case n@Not(expr, loc) =>
            updatedVariables.add(left)
            Some(left, (iterations => (x => s => n)))
          case arr@ArrayNode(elems, loc) =>
            updatedVariables.add(left)
            Some(left, (iterations => (x => s => loadArray(arr, s))))
          case r@Record(fields, loc) =>
            updatedVariables.add(left)
            Some(left,  (iterations => (x => s => loadRecord(r, s, false))))
          case arr@ArrayAccess(ArrayNode(elems, loc1), Number(value, loc2), loc3) =>
            val elem = elems(value)
            updatedVariables.add(left)
            Some(left, (iterations => (x => s => elem)))
          case f@FieldAccess(Record(fields, loc1), field, loc3) =>
            val elem = fields.find(rf => rf.name == field).get.expr
            updatedVariables.add(left)
            Some(left, (iterations => (x => s => elem)))
          case n@Number(_, _) =>
            updatedVariables.add(left)
            Some(left, (iterations => (x => s => n)))
          case a@Alloc(expr, _) =>
            updatedVariables.add(left)
            Some(left, (iterations => (x => s => a)))
          case r@VarRef(id, loc) =>
            updatedVariables.add(left)
            Some(left, (iterations => (x => s => r)))
          case in@Input(loc) =>
            locationsWithUnpredictability.add(printer.print(left))
            Some(left, (iterations => (x => s => SymbolicVal(CodeLoc(0, 0)))))
          case id@Identifier(_, _) if left.equals(id) =>
            updatedVariables.add(left)
            Some(left, iterations => x => s => x)
          case id@Identifier(name, loc) =>
            val location = symbolicState.getSymbolicValOpt(name).get
            updatedVariables.add(left)
            if (!incrementedMemoryLocations.contains(location)) {
              Some(left, (iterations => (x => state => state.getValAtMemoryLoc(id).asInstanceOf[Symbolic])))
            }
            else {
              incrementedVariables.add(left)
              Some(left, incrementedMemoryLocations(location))
            }
          case a@ArrayAccess(_, n: Number, _) =>
            val location = symbolicState.getMemoryLoc(a)
            updatedVariables.add(left)
            if (!incrementedMemoryLocations.contains(location)) {

              Some(left, (iterations => (x => state => {
                val res = state.getValAtMemoryLoc(a).asInstanceOf[Symbolic]
                res
                }
                )
                ))
            }
            else {
              incrementedVariables.add(left)
              Some(left, incrementedMemoryLocations(location))
            }
          case f@FieldAccess(_, _, _) =>
            val location = symbolicState.getMemoryLoc(f)
            updatedVariables.add(left)
            if (!incrementedMemoryLocations.contains(location)) {
              Some(left, (iterations => (x => state => state.getValAtMemoryLoc(f).asInstanceOf[Symbolic])))
            }
            else {
              incrementedVariables.add(left)
              Some(left, incrementedMemoryLocations(location))
            }
          case d@Deref(pointer, loc) =>
            val location = symbolicState.getMemoryLoc(d)
            updatedVariables.add(left)
            if (!incrementedMemoryLocations.contains(location)) {
              Some(left, (iterations => (x => state => state.getValAtMemoryLoc(d).asInstanceOf[Symbolic])))
            }
            else {
              incrementedVariables.add(left)
              Some(left, incrementedMemoryLocations(location))
            }
          case _ =>
            None
        }
      case _ => None
    }
  }

/**
 * Computes all executable paths through a loop's body given a specific control flow graph (CFG) node. This function
 * explores all branches and conditions within the loop, recursively analyzing sub-paths to account for all possible
 * execution scenarios.
 *
 * @param stmt The CFG node representing the start of the loop.
 * @param originalSymbolicState the state we had before reaching the loop.
 * @param symbolicState general state.
 * @param conditionMemoryCells A set of memory locations that affect the loop's execution conditions.
 * @param updatedBy A mapping of memory locations to the variables that update them, used to track dependencies.
 * @param updatedVars A set of variables that are updated within the loop.
 * @param incrementedVars A set of variables that are incremented within the loop.
 * @param locationsWithUnpredictability A set of locations known to introduce unpredictability.
 * @param mapping A mapping between symbolic values in the general symbolic state and the values from the original variables
 * @return An Option containing a list of all paths if the paths can be successfully computed, None if any part of the path
 *         computation fails, typically due to an inability to resolve complex conditions or due to contradictory states.
 */


  def getAllPathsInALoop(stmt: CfgNode, originalSymbolicState: SymbolicState, symbolicState: SymbolicState, conditionMemoryCells: mutable.HashSet[String],
                         updatedBy: mutable.HashMap[String, mutable.HashSet[String]], updatedVars: mutable.HashSet[Expr], incrementedVars: mutable.HashSet[Expr],
                         locationsWithUnpredictability: mutable.HashSet[String], mapping: mutable.HashMap[Val, Expr]): Option[List[Path]] = {
    var paths = List[Path]()
    val incrementedMemoryLocations = mutable.HashMap[PointerVal, Expr => Expr => SymbolicState => Expr]()
    val idMapping = mutable.HashMap[Identifier, Expr]()
    val pathsOpt = getAllLoopBodyPaths(Utility.getTrueBranch(stmt), stmt.id, originalSymbolicState, symbolicState.deepCopy(), incrementedMemoryLocations,
      updatedVars, incrementedVars, conditionMemoryCells, updatedBy, locationsWithUnpredictability, mapping, idMapping)
    if (pathsOpt.isEmpty) {
      return None
    }
    val g = Utility.applyToVarsFromStartingProgram(stmt.ast.asInstanceOf[WhileStmt].guard, idMapping)
    paths = paths.appendedAll(pathsOpt.get
      .map(path => path.addedCondition(g))
      .map(path => path.simplifiedCondition())
    )
    var falsePath = new Path(List.empty, Number(1, stmt.ast.loc), List.empty, mutable.HashSet[Expr]())
    falsePath = falsePath.addedCondition(Not(g, stmt.ast.loc))
    stmt.pred.minBy(node => node.id).ast match {
      case a@AssignStmt(Identifier(name, loc), expr, _) =>
        falsePath = falsePath.appendedStatement(a)
      case _ =>
    }
    paths = paths.appended(falsePath)
    pathToState.put(falsePath, symbolicState)

    for (path <- paths) {
      pathToVertex.put(path, path.changes)
    }
    generalState = symbolicState
    Some(paths)
  }

/**
 * Determine whether there is an edge between two vertices in PDA
 * @param vertex1 The source vertex
 * @param vertex2 The target vertex
 * @param mapping A mapping between symbolic values in the general symbolic state and the values from the original variables
 * @return An Option containing an Edge if it exists.
 */

  def computePathRelationship(vertex1: Vertex, vertex2: Vertex,
                              mapping: mutable.HashMap[Val, Expr]): Option[Edge] = {
    val ctx = new Context()
    val solver = new ConstraintSolver(ctx)

    val changes = pathToVertex(vertex1.path)
    val iterations = vertex1.path.iterations

    val symbolicState = generalState.deepCopy()
    val symbolicState2 = generalState.deepCopy()

    changes.foreach(change => {
      val valLocation = symbolicState.getMemoryLoc(change._1)
      val tmp = change._2.apply(BinaryOp(Minus, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
        .apply(
          {
            symbolicState.symbolicStore.storage.getVal(valLocation) match {
              case None =>
                symbolicState.getMemoryLoc(change._1)
              case _ =>
            }
            symbolicState.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]
          })
        .apply(symbolicState)
      val newVal = tmp match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState.updateMemoryLocation(valLocation, newVal)
    })
    val path1Constraint = Utility.applyTheState(Utility.applyPointers(vertex1.condition, symbolicState), symbolicState)
    val resChanges = new mutable.LinkedHashMap[Expr, Expr => SymbolicState => Expr]()
    for (change <- changes) {
      resChanges.put(change._1, change._2.apply(iterations))
    }
    changes.foreach(change => {
      val valLocation = symbolicState2.getMemoryLoc(change._1)
      val newVal = change._2.apply(iterations).apply(symbolicState2.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]).apply(symbolicState2) match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState2.symbolicStore.storage.addVal(valLocation, newVal)
    })
    val ctxSolver = ctx.mkSolver()
    val path2Constraint = Utility.applyTheState(Utility.applyPointers(vertex2.condition, symbolicState2), symbolicState2)
    val pathsConstraints =
      Utility.simplifyArithExpr(
        BinaryOp(
          AndAnd,
          BinaryOp(AndAnd, path1Constraint, path2Constraint, CodeLoc(0, 0)),
          BinaryOp(GreaterThan, iterations, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)),
          CodeLoc(0, 0)
        )
      )
    val constraint = solver.createConstraint(pathsConstraints, symbolicState)
    ctxSolver.add(ConstraintSolver.getCondition(ctx, constraint))
    ctxSolver.check() match {
      case Status.SATISFIABLE =>
        Some(summarization.Edge(vertex2, applyMapping(pathsConstraints, mapping), resChanges))
      case _ =>
        None
    }
  }

/**
 * Computes the period of a vertex in a loop
 * of a loop by analyzing the constraints of successive iterations and checking if they can be satisfied
 * repeatedly for some integer period.
 *
 * @param vertex1 predecessor of the vertex to compute the priod for.
 * @param vertex2 vertex to compute the priod for.
 * @param vertex3 successor of the vertex to compute the priod for.
 * @return An Option containing the integer period if a consistent repeating pattern is found, None otherwise.
 */

def computePeriod(vertex1: Vertex, vertex2: Vertex, vertex3: Vertex): Option[Int] = {
    val symbolicState = generalState.deepCopy()
    val symbolicState2 = generalState.deepCopy()


    val changes = pathToVertex(vertex1.path)
    val changes2 = pathToVertex(vertex2.path)
    val iterations = vertex1.path.iterations

    changes.foreach(change => {
      val valLocation = symbolicState.getMemoryLoc(change._1)
      val tmp = change._2.apply(BinaryOp(Minus, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
        .apply(symbolicState.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]).apply(symbolicState)
      val newVal = tmp match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState.updateMemoryLocation(valLocation, newVal)
    })
    val ctxSolver = ctx.mkSolver()
    val path1Constraint = Utility.applyTheState(vertex1.condition, symbolicState)
    ctxSolver.add(ConstraintSolver.getCondition(ctx, solver.createConstraint(path1Constraint, symbolicState)))
    val resChanges = new mutable.HashMap[Expr, Expr => SymbolicState => Expr]()
    for (change <- changes) {
      resChanges.put(change._1, change._2.apply(iterations))
    }
    changes.foreach(change => {
      val valLocation = symbolicState2.getMemoryLoc(change._1)
      val newVal = change._2.apply(iterations).apply(symbolicState2.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]).apply(symbolicState2) match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState2.symbolicStore.storage.addVal(valLocation, newVal)
    })
    val path2Constraint = Utility.applyTheState(vertex2.condition, symbolicState2)
    ctxSolver.add(ConstraintSolver.getCondition(ctx, solver.createConstraint(path2Constraint, symbolicState2)))
    val period = SymbolicVal(CodeLoc(0, 0))
    val symbolicState3 = symbolicState2.deepCopy()

    changes2.foreach(change => {
      val valLocation = symbolicState2.getMemoryLoc(change._1)
      val newVal = change._2.apply(BinaryOp(Minus, period, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
        .apply(symbolicState2.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]).apply(symbolicState2) match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState2.symbolicStore.storage.addVal(valLocation, newVal)
    })
    val path3Constraint = Utility.applyTheState(vertex2.condition, symbolicState2)
    ctxSolver.add(ConstraintSolver.getCondition(ctx, solver.createConstraint(path3Constraint, symbolicState2)))
    changes2.foreach(change => {
      val valLocation = symbolicState3.getMemoryLoc(change._1)
      val newVal = change._2.apply(period)
        .apply(symbolicState3.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]).apply(symbolicState3) match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState3.symbolicStore.storage.addVal(valLocation, newVal)
    })
    val path4Constraint = Utility.applyTheState(vertex3.condition, symbolicState3)
    ctxSolver.add(ConstraintSolver.getCondition(ctx, solver.createConstraint(path4Constraint, symbolicState3)))
    ctxSolver.add(ConstraintSolver.getCondition(ctx, solver.createConstraint(BinaryOp(
      AndAnd,
      BinaryOp(GreaterThan, iterations, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)),
      BinaryOp(GreaterEqual, period, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)),
      CodeLoc(0, 0)
    ), symbolicState)))
    ctxSolver.check() match {
      case Status.SATISFIABLE =>
        var model = ctxSolver.getModel
        val periodConst = ctx.mkIntConst(period.name)
        val firstResult = model.eval(periodConst, true)

        val notFirstResult = ctx.mkNot(ctx.mkEq(periodConst, firstResult))
        ctxSolver.push()
        ctxSolver.add(notFirstResult)
        ctxSolver.check() match {
          case Status.UNSATISFIABLE =>
            firstResult match {
              case num: IntNum =>
                Some(num.getInt)
              case _ =>
                None
            }
          case _ =>
            None
        }
      case _ =>
        None
    }
  }




  def applyMapping(expr: Expr, mapping: mutable.HashMap[Val, Expr]): Expr = {
    expr match {
      case Not(expr, loc) =>
        Not(applyMapping(expr, mapping), loc)
      case BinaryOp(operator, left, right, loc) => BinaryOp(operator, applyMapping(left, mapping), applyMapping(right, mapping), loc)
      case i@Identifier(name, loc) => i
      case n@Number(_, _) => n
      case v@SymbolicVal(_)
        if mapping.contains(v) => mapping(v)
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyMapping(expr, mapping)
      case p@PointerVal(_) => p
      case ArrayAccess(array, index, loc) => ArrayAccess(applyMapping(array, mapping), applyMapping(index, mapping), loc)
      case a@ArrayNode(_, _) => a
      case FieldAccess(record, field, loc) => FieldAccess(applyMapping(record, mapping), field, loc)
      case r@Record(_, _) => r
      case Deref(pointer, loc) => Deref(applyMapping(pointer, mapping), loc)
    }
  }





}

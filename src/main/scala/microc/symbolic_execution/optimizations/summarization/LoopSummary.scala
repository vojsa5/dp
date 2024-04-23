package microc.symbolic_execution.optimizations.summarization

import com.microsoft.z3.{Context, IntNum, Status}
import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, AstPrinter, BinaryOp, CodeLoc, Expr, FieldAccess, GreaterEqual, GreaterThan, Identifier, IdentifierDecl, IfStmt, Input, Minus, NestedBlockStmt, Not, Number, Plus, Record, Stmt, Times, VarRef, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}
import microc.symbolic_execution.Value._
import microc.symbolic_execution._
import microc.symbolic_execution.optimizations.subsumption.PathSubsumption
import microc.symbolic_execution.optimizations.{summarization, _}

import scala.collection.mutable

object LoopSummary {

  def getAllPaths(stmt: CfgNode, loopId: Double, symbolicState: SymbolicState, executor: SymbolicExecutor): mutable.HashSet[SymbolicState] = {
    var tmpState = symbolicState.deepCopy()
    var paths = List[Path]()
    paths = paths.appended(new Path(List[Stmt](), Number(1, CodeLoc(0, 0)), List.empty))
    var curr = stmt
    while (curr.id > loopId) {
      curr.ast match {
        case IfStmt(guard, thenBranch, _, _) =>
          val trueBranch = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) curr.succ.maxBy(node => node.id) else curr.succ.minBy(node => node.id)
          val elseBranch = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) curr.succ.minBy(node => node.id) else curr.succ.maxBy(node => node.id)
          val trueState = symbolicState.deepCopy()
          val falseState = symbolicState.deepCopy()
          val res = getAllPaths(trueBranch, loopId, trueState, executor).addAll(getAllPaths(elseBranch, loopId, falseState, executor))
          return res
        case w@WhileStmt(_, _, _) =>
          val res = mutable.HashSet[SymbolicState]()
          for (state <- getAllPaths(curr.succ.filter(node => node.id == curr.id + 1).head, curr.id, symbolicState, executor)) {
            res.addAll(getAllPaths(curr.succ.filter(node => node.id != curr.id + 1).head, loopId, state, executor))
          }
          return res
        case otherStmt@AssignStmt(left, right, _) =>
          if (Utility.varIsFromOriginalProgram(Utility.getName(left))) {
            executor.stepOnAssign(otherStmt, symbolicState)
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

  def createSymbolicStateWithAllValuesSymbolic(oldState: SymbolicState, mapping: mutable.HashMap[Val, Expr]): SymbolicState = {
    var newState = new SymbolicState(oldState.programLocation, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    val tmpState = oldState.deepCopy()//TODO is this necessary?
    for (v <- oldState.variableDecls) {
      val tmpSymVal = getSymbolicRepressentation(tmpState.getValueOfVar(v.name, v.loc, true), v.name, oldState, newState, mapping)
      mapping.put(tmpSymVal, Identifier(v.name, v.loc))
    }
    newState
  }
}

class SummarizationResult(
                           val summary: mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])],
                           val state: SymbolicState,
                           val updatedVars: mutable.HashSet[Expr]
                         )


class LoopSummary(program: ProgramCfg,
                  subsumption: Option[PathSubsumption] = None,
                  ctx: Context = new Context(),
                  searchStrategy: SearchStrategy = new BFSSearchStrategy,
                  stateHistory: Option[StateHistory] = None,
                  covered: Option[mutable.HashSet[CfgNode]] = None,
                  printStats: Boolean = true
                 ) extends SymbolicExecutor(program, subsumption, ctx, searchStrategy, printStats = printStats) {

  val unsummarizableLoops = mutable.HashSet[WhileStmt]()

  val loopPDAs = mutable.HashMap[CfgNode, PDA]()

  val printer = new AstPrinter()

  override def stepOnLoop(symbolicState: SymbolicState): Unit = {
    if (unsummarizableLoops.contains(symbolicState.programLocation.ast.asInstanceOf[WhileStmt])) {
      return super.stepOnLoop(symbolicState)
    }

    val mapping: mutable.HashMap[Val, Expr] = new mutable.HashMap[Val, Expr]()
    val summarizationRes = summarizeLoop(symbolicState, mapping)
    if (summarizationRes.nonEmpty) {
      val summary = summarizationRes.get.summary
      statistics.summarizableLoops += 1
      for (trace <- summary) {
        var tmpState = symbolicState.deepCopy()
        tmpState = tmpState.addedLoopTrace(trace)

        for (change <- trace._2) {
          val name = Utility.getName(change._1)
          if (Utility.varIsFromOriginalProgram(name)) {
            if (tmpState.containsVar(name)) {
              tmpState.applyChange(change._1, trace._2(change._1), mapping)
            }
          }
        }
        //searchStrategy.addState(tmpState)
        step(tmpState)
        symbolicState.returnValue = tmpState.returnValue
      }
    }
    else {
      unsummarizableLoops.add(symbolicState.programLocation.ast.asInstanceOf[WhileStmt])
      super.stepOnLoop(symbolicState)
    }
  }


//TODO remove
  val pathToVertex: mutable.HashMap[Path, List[(Expr, Expr => Expr => Expr)]] = mutable.HashMap[Path, List[(Expr, Expr => Expr => Expr)]]()
  val pathToState: mutable.HashMap[Path, SymbolicState] = mutable.HashMap[Path, SymbolicState]()
  var s: SymbolicState = null

  def getAllConditionsInALoop(cfg: ProgramCfg, loop: CfgNode, symbolicState: SymbolicState): mutable.HashSet[Expr] = {
    val res = mutable.HashSet[Expr]()
    val minId = loop.id.toInt
    val maxId = loop.succ.maxBy(node => node.id).id.toInt
    for (i <- minId until maxId) {
      cfg.nodes.find(node => node.id == i).get.ast match {
        case WhileStmt(guard, _, _) =>
          var expr = guard
          var j = i
          while (Utility.containsVariableNotStartingInAProgram(expr)) {
            j = j - 1
            cfg.nodes.find(node => node.id == j).get.ast match {
              case AssignStmt(left, right, _) =>
                expr = Utility.replaceExpr(expr, left, right)
              case _ =>
                throw new Exception("IMPLEMENT")
            }
          }
          res.add(expr)
        case IfStmt(guard, _, _, _) =>
          var expr = guard
          var j = i
          while (Utility.containsVariableNotStartingInAProgram(expr)) {
            j = j - 1
            cfg.nodes.find(node => node.id == j).get.ast match {
              case AssignStmt(left, right, _) =>
                expr = Utility.replaceExpr(expr, left, right)
              case _ =>
                throw new Exception("IMPLEMENT")
            }
          }
          res.add(expr)
        case _ =>
      }
    }
    res
  }

  def checkConditionInduction(cfg: ProgramCfg, loop: CfgNode, symbolicState: SymbolicState): Boolean = {
    getAllConditionsInALoop(cfg, loop, symbolicState.deepCopy())
    false
  }


  def summarizeLoop(symbolicState: SymbolicState, mapping: mutable.HashMap[Val, Expr]): Option[SummarizationResult] = {
    summarizeLoopInner(symbolicState.programLocation, symbolicState, LoopSummary.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping), mapping)
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
                                 newState: SymbolicState, mapping: mutable.HashMap[Val, Expr]): Option[SummarizationResult] = {

    val allConditions: mutable.HashSet[Expr] = getAllConditionsInALoop(program, symbolicState.programLocation, symbolicState.deepCopy())
    val conditionMemoryCells: mutable.HashSet[String] = getMemoryCellsFromConditions(allConditions)
    var vertices: List[Vertex] = List()


    val updatedVars = mutable.HashSet[Expr]()
    val innerMapping: mutable.HashMap[Val, Expr] = mutable.HashMap[Val, Expr]()

    val innerState = newState.deepCopy()
    for (m <- mapping) {
//      m._1 match {
//        case a: ArrVal =>
//          innerMapping.put(innerState.getValAtMemoryLoc(m._2), innerMapping(m._1))
//        case r: RecVal =>
//        case other =>
          innerMapping.put(m._1, m._2)
//      }
    }
    val pathsOpt = getAllPathsInALoop(loop, symbolicState.deepCopy(), innerState, conditionMemoryCells, updatedVars, innerMapping)
    if (pathsOpt.isEmpty) {
      return None
    }
    val paths = pathsOpt.get
    for (path <- paths) {
      vertices = vertices.appended(summarization.Vertex(path, path.condition, pathToVertex(path), path.iterations))
    }
    val pda = PDA(this, vertices, symbolicState.variableDecls, solver, Number(1, CodeLoc(0, 0)), newState, mapping)
    pda.initialize()
    if (pda.checkForConnectedCycles()) {
      return None
    }
    pda.summarizeType1Loop2(symbolicState) match {
      case Some(summary) =>
        Some(new SummarizationResult(summary, newState, updatedVars))
      case None =>
        None
    }
  }


  def computeVariableChange(stmts: List[Stmt], symbolicState: SymbolicState): mutable.HashMap[String, (Expr) => ((Expr) => Expr)] = {
    val variableChange = mutable.HashMap[String, Expr => (Expr => Expr)]()
    for (stmt <- stmts) {
      stmt match {
        case AssignStmt(Identifier(name, loc), expr, _) =>
          expr match {
            case BinaryOp(Plus, Identifier(name2, loc1), n@Number(_, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
            case BinaryOp(Minus, Identifier(name2, loc1), Number(value, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
            case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(_, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc1)))))
            case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(_, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Not(symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc2), loc1)))))
            case BinaryOp(Plus, n@Number(_, loc2), Identifier(name2, loc1),  _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
            case BinaryOp(Minus, Number(value, loc2), Identifier(name2, loc1), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
            case BinaryOp(Plus, id@Identifier(_, loc2), Identifier(name2, loc1), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc1)))))
            case BinaryOp(Minus, id@Identifier(_, loc2), Identifier(name2, loc1), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Not(symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc2), loc1)))))

            case expr if !Utility.varIsFromOriginalProgram(name) =>
              variableChange += (name -> (iterations => (x => Utility.simplifyArithExpr(expr))))
            case _ =>

          }
        case _ =>
      }
    }
    variableChange
  }


  def getAllLoopBodyPaths(stmt: CfgNode, loopId: Double, originalSymbolicState: SymbolicState, symbolicState: SymbolicState,
                          incrementedMemoryLocations: mutable.HashMap[PointerVal, Expr => Expr => Expr], updatedVars: mutable.HashSet[Expr],
                          conditionMemoryCells: mutable.HashSet[String], locationsWithUnpredictability: mutable.HashSet[String],
                          mapping: mutable.HashMap[Val, Expr]): Option[List[Path]] = {
    var tmpState = symbolicState.deepCopy()
    var paths = List[Path]()
    paths = paths.appended(new Path(List[Stmt](), Number(1, CodeLoc(0, 0)), List.empty))
    var curr = stmt
    while (curr.id > loopId) {
      curr.ast match {
        case IfStmt(guard, thenBranch, _, _) =>
          paths = paths.flatMap(
            path => {
              val trueBranch = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) curr.succ.maxBy(node => node.id) else curr.succ.minBy(node => node.id)
              val elseBranch = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) curr.succ.minBy(node => node.id) else curr.succ.maxBy(node => node.id)
              val trueState = symbolicState.deepCopy()
              var pathsOpt = getAllLoopBodyPaths(trueBranch, loopId, originalSymbolicState, trueState,
                incrementedMemoryLocations, updatedVars, conditionMemoryCells, locationsWithUnpredictability.clone(), mapping)
              if (pathsOpt.isEmpty) {
                return None
              }
              paths = pathsOpt.get
                .map(pathContinuation => pathContinuation.addedCondition(guard))
                .map(pathContinuation => path.appendedAsPath(pathContinuation))

              val falseState = symbolicState.deepCopy()
              pathsOpt = getAllLoopBodyPaths(elseBranch, loopId, originalSymbolicState, falseState,
                incrementedMemoryLocations, updatedVars, conditionMemoryCells, locationsWithUnpredictability.clone(), mapping)
              if (pathsOpt.isEmpty) {
                return None
              }

              paths = paths.appendedAll(
                pathsOpt.get
                  .map(pathContinuation => pathContinuation.addedCondition(Not(guard, guard.loc)))
                  .map(pathContinuation => path.appendedAsPath(pathContinuation)))
              paths
            }
          )
          return Some(paths)
        case w@WhileStmt(_, _, _) =>
          val summaryOpt = summarizeLoopInner(curr, originalSymbolicState, symbolicState, mapping)
          if (summaryOpt.isEmpty) {
            return None
          }
          val summary = summaryOpt.get
          val innerUpdatedVars = summary.updatedVars
          updatedVars.addAll(innerUpdatedVars)
          for (trace <- summary.summary) {
            symbolicState.addedLoopTrace(trace)
            paths = paths.map(path => path.addedCondition(trace._1))
            for (update <- trace._2) {
              val name = Utility.getName(update._1)
              if (Utility.varIsFromOriginalProgram(name)) {
                paths = paths.map(path =>
                  if (innerUpdatedVars.contains(update._1)) {
                    path.updatedChanges(update._1,
                      iterations => x => Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, update._2.apply(x), CodeLoc(0, 0)), CodeLoc(0, 0)))
                    )
                  }
                  else {
                    path.updatedChanges(update._1,
                      iterations => x => Utility.simplifyArithExpr(update._2.apply(x))
                    )
                  }
                )
                if (symbolicState.containsVar(name)) {
                  symbolicState.applyChange(update._1, update._2, mapping)
                }
              }
            }
          }
          curr = curr.succ.filter(node => node.id != curr.id + 1).head
        case otherStmt@AssignStmt(left, right, _) =>
          val changeOpt = computeVariableChange2(otherStmt, symbolicState, incrementedMemoryLocations,
            updatedVars, conditionMemoryCells, locationsWithUnpredictability, mapping)
          if (changeOpt.nonEmpty) {
            (left, right) match {
              case (_, BinaryOp(_, _, _, _)) =>
              case (id@Identifier(_, _), id2@Identifier(_, _)) =>
                val s = symbolicState.getValAtMemoryLoc(id2)
                if (mapping.contains(s)) {
                  //TODO look at this
                  val v = mapping(s)
                  mapping.put(s, left)
                }
              case _ =>
            }
            if (curr.succ.head.id > loopId) {
              stepOnAssign(otherStmt, symbolicState)
              stepOnAssign(otherStmt, originalSymbolicState)
            }
            val change = changeOpt.get
            change._1 match {
              case v@Identifier(name, loc) =>
                paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(v, change._2))
              case a@ArrayAccess(array, index, _) =>
                paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(a, change._2))
              case f@FieldAccess(record, field, loc) =>
                paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(f, change._2))
              case _ =>
                throw new Exception("IMPLEMENT")
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
    for (path <- paths) {
      if (!pathToState.contains(path)) {
        pathToState.put(path, symbolicState)
      }
    }
    Some(paths)
  }


  private def sameSymbolicVal(state: SymbolicState, ptr1: PointerVal, ptr2: PointerVal): Boolean = state.getValOnMemoryLocation(ptr1) == state.getValOnMemoryLocation(ptr2)


  def computeVariableChange2(stmt: Stmt, symbolicState: SymbolicState,
                             incrementedMemoryLocations: mutable.HashMap[PointerVal, (Expr) => ((Expr) => Expr)],
                             incrementedVariables: mutable.HashSet[Expr],
                             conditionMemoryCells: mutable.HashSet[String],
                             locationsWithUnpredictability: mutable.HashSet[String],
                             mapping: mutable.HashMap[Val, Expr]
                            ): Option[(Expr, (Expr) => ((Expr) => Expr))] = {
    stmt match {
      case AssignStmt(left, right, _) =>
        if (Utility.exprContainsAMemoryLocation(right, locationsWithUnpredictability, printer) && conditionMemoryCells.contains(printer.print(left))) {
          return None
        }
        val name = Utility.getName(left)
        locationsWithUnpredictability.remove(printer.print(left))
        val leftSideMemoryLocation = symbolicState.getMemoryLoc(left)
        Utility.simplifyArithExpr(right) match {
          case BinaryOp(_, SymbolicVal(_), _, _) =>
            None
          case BinaryOp(_, _, SymbolicVal(_), _) =>
            None
          case BinaryOp(Plus, Identifier(name2, loc1), n@Number(_, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            val changeFunction: Expr => Expr => Expr = (iterations => (x =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Minus, Identifier(name2, loc1), Number(value, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            val changeFunction: Expr => Expr => Expr = (iterations => (x =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
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
            val v = symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic]
            val changeFunction: Expr => Expr => Expr = (iterations => (x =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, v, loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Minus, resId@Identifier(name2, loc1), id@Identifier(_, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            val v = symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic]
            val changeFunction: Expr => Expr => Expr = (iterations => (x =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, BinaryOp(Minus, Number(0, CodeLoc(0, 0)), v, loc2), loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Plus, n@Number(_, loc2), Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            val changeFunction: Expr => Expr => Expr = (iterations => (x =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Minus, Number(value, loc2), Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            val changeFunction: Expr => Expr => Expr = (iterations => (x =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Plus, id@Identifier(_, loc2), resId@Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            val v = symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic]
            val changeFunction: Expr => Expr => Expr = (iterations => (x =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, v, loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            Some(left, changeFunction)
          case BinaryOp(Minus, id@Identifier(_, loc2), resId@Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, leftSideMemoryLocation) =>
            val v = symbolicState.getValueOfVar(id.name, id.loc).asInstanceOf[Symbolic]
            val changeFunction: Expr => Expr => Expr = (iterations => (x =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, BinaryOp(Minus, Number(0, CodeLoc(0, 0)), v, loc2), loc2), loc1))))
            incrementedMemoryLocations.put(leftSideMemoryLocation, changeFunction)
            incrementedVariables.add(left)
            Some(left, changeFunction)
          case expr: BinaryOp if !Utility.varIsFromOriginalProgram(name) =>
            Some(left, (iterations => (x => Utility.simplifyArithExpr(expr))))
          case n@Not(expr, loc) =>
            Some(left, (iterations => (x => n)))
          case arr@ArrayNode(elems, loc) =>
            val v = loadArray(arr, symbolicState)
            Some(left, (iterations => (x => v)))
          case arr@ArrayAccess(ArrayNode(elems, loc1), Number(value, loc2), loc3) =>
            val elem = elems(value)
            Some(left, (iterations => (x => elem)))
          case f@FieldAccess(Record(fields, loc1), field, loc3) =>
            val elem = fields.find(rf => rf.name == field).get.expr
            Some(left, (iterations => (x => elem)))
          case n@Number(_, _) =>
            Some(left, (iterations => (x => n)))
          case a@Alloc(expr, _) =>
            Some(left, (iterations => (x => a)))
          case r@VarRef(id, loc) =>
            Some(left, (iterations => (x => r)))
          case in@Input(loc) =>
            locationsWithUnpredictability.add(printer.print(left))
            Some(left, (iterations => (x => SymbolicVal(CodeLoc(0, 0)))))
          case Identifier(name, loc) =>
            val location = symbolicState.getSymbolicValOpt(name).get
//            symbolicState.getVal(location) match {
//              case Some(s@SymbolicVal(_)) =>
//                mapping.put(s, left)
//              case _ =>
//            }
            if (!incrementedMemoryLocations.contains(location)) {
              Some(left, (iterations => (x => x)))
            }
            else {
              Some(left, incrementedMemoryLocations(location))
            }
          case a@ArrayAccess(_, _, _) =>
            val location = symbolicState.getMemoryLoc(a)
//            symbolicState.getVal(location) match {
//              case Some(s@SymbolicVal(_)) =>
//                mapping.put(s, left)
//              case _ =>
//            }
            if (!incrementedMemoryLocations.contains(location)) {
              Some(left, (iterations => (x => x)))
            }
            else {
              Some(left, incrementedMemoryLocations(location))
            }
          case f@FieldAccess(_, _, _) =>
            val location = symbolicState.getMemoryLoc(f)
//            symbolicState.getVal(location) match {
//              case Some(s@SymbolicVal(_)) =>
//                mapping.put(s, left)
//              case _ =>
//            }
            if (!incrementedMemoryLocations.contains(location)) {
              Some(left, (iterations => (x => x)))
            }
            else {
              Some(left, incrementedMemoryLocations(location))
            }
          case _ =>
            None
        }
      case _ => None
    }
  }



  def getAllPathsInALoop(stmt: CfgNode, originalSymbolicState: SymbolicState, symbolicState: SymbolicState, conditionMemoryCells: mutable.HashSet[String],
                         updatedVars: mutable.HashSet[Expr], mapping: mutable.HashMap[Val, Expr]): Option[List[Path]] = {
    var paths = List[Path]()
    var falsePath = new Path(List.empty, Number(1, stmt.ast.loc), List.empty)
    falsePath = falsePath.addedCondition(Not(stmt.ast.asInstanceOf[WhileStmt].guard, stmt.ast.loc))
    stmt.pred.minBy(node => node.id).ast match {
      case a@AssignStmt(Identifier(name, loc), expr, _) =>
        falsePath = falsePath.appendedStatement(a)
      case _ =>
    }
    paths = paths.appended(falsePath)
    pathToState.put(falsePath, symbolicState)
    s = symbolicState
    val incrementedMemoryLocations = mutable.HashMap[PointerVal, Expr => Expr => Expr]()
    val locationsWithUnpredictability = mutable.HashSet[String]()
    val pathsOpt = getAllLoopBodyPaths(stmt.succ.minBy(node => node.id), stmt.id, originalSymbolicState, symbolicState.deepCopy(), incrementedMemoryLocations,
      updatedVars, conditionMemoryCells, locationsWithUnpredictability, mapping)
    if (pathsOpt.isEmpty) {
      return None
    }
    paths = paths.appendedAll(pathsOpt.get
      .map(path => path.addedCondition(stmt.ast.asInstanceOf[WhileStmt].guard))
      .map(path => path.simplifiedCondition())
    )
    for (path <- paths) {
      pathToVertex.put(path, path.changes)
    }
    Some(paths)
  }


  def getUpdatedVars(loop: WhileStmt): mutable.HashSet[String] = {
    val res = mutable.HashSet[String]()
    for (stmt <- loop.block.asInstanceOf[NestedBlockStmt].body) {
      stmt match {
        case AssignStmt(left: Identifier, _, _) if Utility.varIsFromOriginalProgram(left.name) => res.add(left.name)
        case _ =>
      }
    }
    res
  }


  def computePathRelationship(vertex1: Vertex, vertex2: Vertex, variables: List[IdentifierDecl],
                              mapping: mutable.HashMap[Val, Expr]): Option[Edge] = {
    val ctx = new Context()
    val solver = new ConstraintSolver(ctx)

    val changes = pathToVertex(vertex1.path)
    val iterations = vertex1.path.iterations

    val symbolicState = s.deepCopy()
    val symbolicState2 = s.deepCopy()

    changes.foreach(change => {
      val valLocation = symbolicState.getMemoryLoc(change._1)
      val tmp = change._2.apply(BinaryOp(Minus, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
        .apply(symbolicState.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic])
      val newVal = tmp match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState.updateMemoryLocation(valLocation, newVal)
    })
    val path1Constraint = Utility.applyTheState(vertex1.condition, symbolicState)
    val resChanges = new mutable.HashMap[Expr, Expr => Expr]()
    for (change <- changes) {
      resChanges.put(change._1, change._2.apply(iterations))
    }
    changes.foreach(change => {
      val valLocation = symbolicState2.getMemoryLoc(change._1)
      val newVal = change._2.apply(iterations).apply(symbolicState2.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]) match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState2.symbolicStore.storage.addVal(valLocation, newVal)
    })
    val ctxSolver = ctx.mkSolver()
    val path2Constraint = Utility.applyTheState(vertex2.condition, symbolicState2)
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
        val tmp = applyMapping(pathsConstraints, mapping)
        Some(summarization.Edge(vertex2, tmp, resChanges))
      case _ =>
        None
    }
  }

  def computePeriod(vertex1: Vertex, vertex2: Vertex, vertex3: Vertex): Option[Int] = {
    val symbolicState = s.deepCopy()
    val symbolicState2 = s.deepCopy()


    val changes = pathToVertex(vertex1.path)
    val changes2 = pathToVertex(vertex2.path)
    val iterations = vertex1.path.iterations

    changes.foreach(change => {
      val valLocation = symbolicState.getMemoryLoc(change._1)
      val tmp = change._2.apply(BinaryOp(Minus, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
        .apply(symbolicState.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic])
      val newVal = tmp match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState.updateMemoryLocation(valLocation, newVal)
    })
    val path1Constraint = Utility.applyTheState(vertex1.condition, symbolicState)
    val resChanges = new mutable.HashMap[Expr, Expr => Expr]()
    for (change <- changes) {
      resChanges.put(change._1, change._2.apply(iterations))
    }
    changes.foreach(change => {
      val valLocation = symbolicState2.getMemoryLoc(change._1)
      val newVal = change._2.apply(iterations).apply(symbolicState2.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]) match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState2.symbolicStore.storage.addVal(valLocation, newVal)
    })
    val path2Constraint = Utility.applyTheState(vertex2.condition, symbolicState2)
    val period = SymbolicVal(CodeLoc(0, 0))
    val symbolicState3 = symbolicState2.deepCopy()

    changes2.foreach(change => {
      val valLocation = symbolicState2.getMemoryLoc(change._1)
      val newVal = change._2.apply(BinaryOp(Minus, period, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
        .apply(symbolicState2.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]) match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState2.symbolicStore.storage.addVal(valLocation, newVal)
    })
    val path3Constraint = Utility.applyTheState(vertex2.condition, symbolicState2)

    changes2.foreach(change => {
      val valLocation = symbolicState3.getMemoryLoc(change._1)
      val newVal = change._2.apply(period)
        .apply(symbolicState3.symbolicStore.storage.getVal(valLocation).get.asInstanceOf[Symbolic]) match {
        case v: Val => v
        case e: Expr =>
          Utility.removeUnnecessarySymbolicExpr(SymbolicExpr(e, CodeLoc(0, 0)))
      }
      symbolicState3.symbolicStore.storage.addVal(valLocation, newVal)
    })
    val path4Constraint = Utility.applyTheState(vertex3.condition, symbolicState3)
    val ctxSolver = ctx.mkSolver()
    val pathsConstraints = {
      Utility.simplifyArithExpr(
        BinaryOp(
          AndAnd,
          BinaryOp(
            AndAnd,
            BinaryOp(AndAnd, path1Constraint, path2Constraint, CodeLoc(0, 0)),
            BinaryOp(AndAnd, path3Constraint, path4Constraint, CodeLoc(0, 0)),
            CodeLoc(0, 0)
          ),
          BinaryOp(
            AndAnd,
            BinaryOp(GreaterThan, iterations, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)),
            BinaryOp(GreaterEqual, period, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)),
            CodeLoc(0, 0)
          ),
          CodeLoc(0, 0)
        )
      )
    }
    val constraint = solver.createConstraint(pathsConstraints, symbolicState)
    ctxSolver.add(ConstraintSolver.getCondition(ctx, constraint))
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
            model = ctxSolver.getModel
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
    }
  }





}

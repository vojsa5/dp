package microc.symbolic_execution

import com.microsoft.z3.{BoolExpr, Context, Status}
import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, BinaryOp, CodeLoc, Divide, Equal, Expr, FieldAccess, GreaterEqual, GreaterThan, Identifier, IdentifierDecl, IfStmt, Input, LowerEqual, LowerThan, Minus, NestedBlockStmt, Not, NotEqual, Number, OrOr, Plus, Stmt, Times, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}
import microc.symbolic_execution.LoopSummary.getAllTruePaths
import microc.symbolic_execution.Value.{ArrVal, PointerVal, RecVal, Symbolic, SymbolicExpr, SymbolicVal, UninitializedRef, Val}

import scala.collection.mutable

object LoopSummary {


  def getAllTruePaths(stmt: CfgNode, loopId: Int): List[Path] = {
    var paths = List[Path]()
    paths = paths.appended(new Path(List[Stmt](), Number(1, CodeLoc(0, 0)), mutable.HashMap()))
    var curr = stmt
    while (curr.id != loopId) {
      curr.ast match {
        case IfStmt(guard, _, _, _) =>
          paths = paths.flatMap(
            path => {
              paths = getAllTruePaths(curr.succ.head, loopId)
                .map(pathContinuation => pathContinuation.addedCondition(guard))
                .map(pathContinuation => path.appendedAsPath(pathContinuation))
              paths = paths.appendedAll(
                getAllTruePaths(curr.succ.tail.head, loopId)
                  .map(pathContinuation => pathContinuation.addedCondition(Not(guard, guard.loc)))
                  .map(pathContinuation => path.appendedAsPath(pathContinuation)))
              paths
            }
          )
          return paths
        case stmt: Stmt =>
          paths = paths.map(path => path.appendedStatement(stmt))
          curr = curr.succ.head
      }
    }
    paths
  }

  def getSymbolicValsFromExpr(expr: Expr): List[SymbolicVal] = {
    expr match {
      case Not(expr, loc) => getSymbolicValsFromExpr(expr)
      case BinaryOp(operator, left, right, loc) => getSymbolicValsFromExpr(left).appendedAll(getSymbolicValsFromExpr(right))
      case id@Identifier(_, _) => List.empty
      case n@Number(_, _) => List.empty
      case v@SymbolicVal(_) => List(v)
      case SymbolicExpr(expr, _) => getSymbolicValsFromExpr(expr)
    }
  }
}


class LoopSummary(program: ProgramCfg,
                  subsumption: Option[PathSubsumption] = None,
                  ctx: Context = new Context(),
                  searchStrategy: SearchStrategy = new BFSSearchStrategy
                 ) extends SymbolicExecutor(program, subsumption, ctx, searchStrategy) {

  val unsummarizableLoops = mutable.HashSet[WhileStmt]()


  override def stepOnLoop(symbolicState: SymbolicState): Unit = {
    if (unsummarizableLoops.contains(symbolicState.nextStatement.ast.asInstanceOf[WhileStmt])) {
      return super.stepOnLoop(symbolicState)
    }

    val summarizationRes = summarizeLoop(symbolicState)
    if (summarizationRes.nonEmpty) {
      val (summary, newState) = summarizationRes.get
      for (trace <- summary) {
        var tmpState = symbolicState.deepCopy()
        tmpState = tmpState.addedLoopTrace(trace)

        for (change <- trace._2) {
          val name = change._1 match {
            case Identifier(name, _) => name
          }
          if (Utility.varIsFromOriginalProgram(name)) {
            val ptr = newState.getSymbolicValOpt(name).get.asInstanceOf[PointerVal]
            val ptrVal = tmpState.symbolicStore.getValOfPtr(ptr, true) match {
              case Some(UninitializedRef) =>
                Some(SymbolicVal(CodeLoc(0, 0)))
              case o =>
                o

            }
            val q = trace._2(change._1).apply(Number(0, CodeLoc(0, 0)))
            val q2 = trace._2(change._1).apply(SymbolicVal(CodeLoc(0, 0)))
            tmpState = tmpState.updatedVar(ptr, SymbolicExpr(trace._2(change._1).apply(ptrVal.get.asInstanceOf[Symbolic]), CodeLoc(0, 0)))
          }
        }
        step(tmpState)
        symbolicState.returnValue = tmpState.returnValue
      }
    }
    else {
      unsummarizableLoops.add(symbolicState.nextStatement.ast.asInstanceOf[WhileStmt])
      super.stepOnLoop(symbolicState)
    }
  }

//TODO remove
  val pathToVertex: mutable.HashMap[Path, mutable.HashMap[Expr, Expr => Expr => Expr]] = mutable.HashMap[Path, mutable.HashMap[Expr, Expr => Expr => Expr]]()


  def summarizeLoop(symbolicState: SymbolicState): Option[(mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])], SymbolicState)] = {
    summarizeLoopInner(symbolicState.nextStatement, symbolicState)
  }

  private def summarizeLoopInner(loop: CfgNode, symbolicState: SymbolicState): Option[(mutable.HashSet[(Expr, mutable.HashMap[Expr, Expr => Expr])], SymbolicState)] = {

    var vertices: List[Vertex] = List()
    var newState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
    val pathsOpt = getAllPathsInALoop(loop, symbolicState)
    if (pathsOpt.isEmpty) {
      return None
    }
    val paths = pathsOpt.get
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, pathToVertex(path), path.iterations))
    }
    val pda = PDA(this, vertices, symbolicState.variableDecls, solver, Number(1, CodeLoc(0, 0)), symbolicState)
    pda.initialize()

    for (v <- symbolicState.variableDecls) {
      val tmpSymVal = SymbolicVal(v.loc)
      newState = newState.addedVar(v.name, tmpSymVal)
    }
    Some((pda.summarizeType1Loop2(symbolicState), newState))
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
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc1)))))
            case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(_, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Not(symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc2), loc1)))))
            case BinaryOp(Plus, n@Number(_, loc2), Identifier(name2, loc1),  _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
            case BinaryOp(Minus, Number(value, loc2), Identifier(name2, loc1), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
            case BinaryOp(Plus, id@Identifier(_, loc2), Identifier(name2, loc1), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc1)))))
            case BinaryOp(Minus, id@Identifier(_, loc2), Identifier(name2, loc1), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Not(symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc2), loc1)))))

            case expr if !Utility.varIsFromOriginalProgram(name) =>
              variableChange += (name -> (iterations => (x => Utility.simplifyArithExpr(expr))))
            case _ =>

          }
        case _ =>
      }
    }
    variableChange
  }


  def getAllTruePaths2(stmt: CfgNode, loopId: Double, symbolicState: SymbolicState, updatedVars: mutable.HashMap[PointerVal, Expr => Expr => Expr]): Option[List[Path]] = {
    var paths = List[Path]()
    paths = paths.appended(new Path(List[Stmt](), Number(1, CodeLoc(0, 0)), mutable.HashMap()))
    var curr = stmt
    while (curr.id > loopId) {
      curr.ast match {
        case IfStmt(guard, _, _, _) =>
          paths = paths.flatMap(
            path => {
              var pathsOpt = getAllTruePaths2(curr.succ.head, loopId, symbolicState.deepCopy(), updatedVars)
              if (pathsOpt.isEmpty) {
                return None
              }
              paths = pathsOpt.get
                .map(pathContinuation => pathContinuation.addedCondition(guard))
                .map(pathContinuation => path.appendedAsPath(pathContinuation))

              pathsOpt = getAllTruePaths2(curr.succ.tail.head, loopId, symbolicState.deepCopy(), updatedVars)
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
          val summaryOpt = summarizeLoopInner(curr, symbolicState)
          if (summaryOpt.isEmpty) {
            return None
          }
          val summary = summaryOpt.get
          for (trace <- summary._1) {
            paths = paths.map(path => path.addedCondition(trace._1))
            for (update <- trace._2) {
              val name = update._1 match {
                case Identifier(name, _) => name
              }
              if (Utility.varIsFromOriginalProgram(name)) {
                val x = update._2.apply(Number(0, CodeLoc(0, 0)))
                paths = paths.map(path =>
                  path.updatedChanges(update._1,
                    iterations => x => Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, update._2.apply(x), CodeLoc(0, 0)), CodeLoc(0, 0)))
                  )
                )
                if (symbolicState.containsVar(name)) {
                  symbolicState.applyChange(name, update._2)
                }
              }
            }
          }
          curr = curr.succ.filter(node => node.id != curr.id + 1).head
        case otherStmt: AssignStmt =>
          val changeOpt = computeVariableChange2(otherStmt, symbolicState, updatedVars)
          if (changeOpt.nonEmpty) {
            stepOnAssign(otherStmt, symbolicState)
            val change = changeOpt.get
            change._1 match {
              case v@Identifier(name, loc) =>
                paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(v, change._2))
              case a@ArrayAccess(array, index, _) =>
                paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(a, change._2))
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
    Some(paths)
  }


  private def sameSymbolicVal(state: SymbolicState, ptr1: PointerVal, ptr2: PointerVal): Boolean = state.getVal(ptr1) == state.getVal(ptr2)



  def computeVariableChange2(stmt: Stmt, symbolicState: SymbolicState, updatedMemoryLocations: mutable.HashMap[PointerVal, (Expr) => ((Expr) => Expr)]): Option[(Expr, (Expr) => ((Expr) => Expr))] = {
    stmt match {
      case AssignStmt(id@Identifier(name, loc), expr, _) =>
        val rightSideMemoryLocation = symbolicState.getSymbolicValOpt(name).get
        Utility.simplifyArithExpr(expr) match {
          case BinaryOp(_, SymbolicVal(_), _, _) =>
            None
          case BinaryOp(_, _, SymbolicVal(_), _) =>
            None
          case BinaryOp(Plus, Identifier(name2, loc1), n@Number(_, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) =>
              val changeFunction: Expr => Expr => Expr = (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1))))
              updatedMemoryLocations.put(rightSideMemoryLocation, changeFunction)
              Some(id, changeFunction)
          case BinaryOp(Minus, Identifier(name2, loc1), Number(value, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) =>
              val changeFunction: Expr => Expr => Expr = (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1))))
              updatedMemoryLocations.put(rightSideMemoryLocation, changeFunction)
              Some(id, changeFunction)
          case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) && updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name3).get) =>
              None
          case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) && updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name3).get) =>
              None
          case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name3).get, rightSideMemoryLocation) && updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name2).get) =>
              None
          case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name3).get, rightSideMemoryLocation) && updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name2).get) =>
              None
          case BinaryOp(Plus, resId@Identifier(name2, loc1), id@Identifier(_, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) =>
              val v = symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic]
              val changeFunction: Expr => Expr => Expr = (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, v, loc2), loc1))))
              updatedMemoryLocations.put(rightSideMemoryLocation, changeFunction)
              Some(resId, changeFunction)
          case BinaryOp(Minus, resId@Identifier(name2, loc1), id@Identifier(_, loc2), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) =>
              val v = symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic]
              val changeFunction: Expr => Expr => Expr = (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, BinaryOp(Minus, Number(0, CodeLoc(0, 0)), v, loc2), loc2), loc1))))
              updatedMemoryLocations.put(rightSideMemoryLocation, changeFunction)
                Some(resId, changeFunction)
          case BinaryOp(Plus, n@Number(_, loc2), Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) =>
              val changeFunction: Expr => Expr => Expr = (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1))))
              updatedMemoryLocations.put(rightSideMemoryLocation, changeFunction)
              Some(id, changeFunction)
          case BinaryOp(Minus, Number(value, loc2), Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) =>
              val changeFunction: Expr => Expr => Expr = (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1))))
              updatedMemoryLocations.put(rightSideMemoryLocation, changeFunction)
              Some(id, changeFunction)
          case BinaryOp(Plus, id@Identifier(_, loc2), resId@Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) =>
              val v = symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic]
              val changeFunction: Expr => Expr => Expr = (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, v, loc2), loc1))))
              updatedMemoryLocations.put(rightSideMemoryLocation, changeFunction)
              Some(resId, changeFunction)
          case BinaryOp(Minus, id@Identifier(_, loc2), resId@Identifier(name2, loc1), _)
            if sameSymbolicVal(symbolicState, symbolicState.getSymbolicValOpt(name2).get, rightSideMemoryLocation) =>
            val v = symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic]
            val changeFunction: Expr => Expr => Expr = (iterations => (x =>
              Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, BinaryOp(Minus, Number(0, CodeLoc(0, 0)), v, loc2), loc2), loc1))))
            updatedMemoryLocations.put(rightSideMemoryLocation, changeFunction)
            Some(resId, changeFunction)
          case expr: BinaryOp if !Utility.varIsFromOriginalProgram(name) =>
            Some(id, (iterations => (x => Utility.simplifyArithExpr(expr))))
          case n@Not(expr, loc) =>
            Some(id, (iterations => (x => n)))
          case arr@ArrayNode(elems, loc) =>
            Some(id, (iterations => (x => arr)))
          case arr@ArrayAccess(Identifier(name, loc1), Number(n, loc2), loc3) if !updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name).get) =>
            val elem = symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicVal(name, loc).asInstanceOf[ArrVal].elems(n).address).asInstanceOf[Symbolic]
            Some(id, (iterations => (x => elem)))
          case f@FieldAccess(Identifier(name, loc1), field, loc2) =>
            val rec = symbolicState.getSymbolicVal(name, loc1).asInstanceOf[RecVal]
            val r = rec.fields(field).asInstanceOf[Symbolic]
            Some(id, (iterations => (x => r)))
          case n@Number(_, _) =>
            Some(id, (iterations => (x => n)))
          case a@Alloc(expr, _) =>
            Some(id, (iterations => (x => a)))
          case in@Input(loc) =>
            Some(id, (iterations => (x => SymbolicVal(CodeLoc(0, 0)))))
          case Identifier(name, loc) =>
            val location = symbolicState.getSymbolicValOpt(name).get
            if (!updatedMemoryLocations.contains(location)) {
              val v = symbolicState.getSymbolicVal(name, loc).asInstanceOf[Symbolic]
              Some(id, (iterations => (x => v)))
            }
            else {
              Some(id, updatedMemoryLocations(location))
            }
          case _ =>
            None
        }
      case AssignStmt(a@ArrayAccess(Identifier(name, loc), Number(index, _), _), expr, _) =>
        val arrayOnIndex = symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicVal(name, loc).asInstanceOf[ArrVal].elems(index).address)
        Utility.simplifyArithExpr(expr) match {
          case BinaryOp(_, SymbolicVal(_), _, _) =>
            None
          case BinaryOp(_, _, SymbolicVal(_), _) =>
            None
          case BinaryOp(Plus, Identifier(name2, loc1), n@Number(_, loc2), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex =>
              Some(a, (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
          case BinaryOp(Minus, Identifier(name2, loc1), Number(value, loc2), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex =>
              Some(a, (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
          case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex && updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name3).get) =>
              None
          case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex && updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name3).get) =>
              None
          case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name3).get.asInstanceOf[PointerVal].address) == arrayOnIndex && updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name2).get) =>
              None
          case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(name3, loc2), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name3).get.asInstanceOf[PointerVal].address) == arrayOnIndex && updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name2).get) =>
            None
          case BinaryOp(Plus, resId@Identifier(name2, loc1), id@Identifier(_, loc2), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex =>
              val v = symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic]
              Some(a, (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, v, loc2), loc1)))))
          case BinaryOp(Minus, resId@Identifier(name2, loc1), id@Identifier(_, loc2), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex =>
              val v = symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic]
              Some(a, (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, BinaryOp(Minus, Number(0, CodeLoc(0, 0)), v, loc2), loc2), loc1)))))
          case BinaryOp(Plus, n@Number(_, loc2), Identifier(name2, loc1), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex =>
              Some(a, (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
          case BinaryOp(Minus, Number(value, loc2), Identifier(name2, loc1), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex =>
              Some(a, (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
          case BinaryOp(Plus, id@Identifier(_, loc2), resId@Identifier(name2, loc1), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex =>
              val v = symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic]
              Some(a, (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, v, loc2), loc1)))))
          case BinaryOp(Minus, id@Identifier(_, loc2), resId@Identifier(name2, loc1), _)
            if symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicValOpt(name2).get.asInstanceOf[PointerVal].address) == arrayOnIndex =>
              val v = symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic]
              Some(a, (iterations => (x =>
                Utility.simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, BinaryOp(Minus, Number(0, CodeLoc(0, 0)), v, loc2), loc2), loc1)))))
          case arr@ArrayAccess(Identifier(name, loc1), Number(n, loc2), loc3) if !updatedMemoryLocations.contains(symbolicState.getSymbolicValOpt(name).get) =>
            val elem = symbolicState.symbolicStore.storage.memory(symbolicState.getSymbolicVal(name, loc)
              .asInstanceOf[ArrVal].elems(n).address).asInstanceOf[Symbolic]
            Some(a, (iterations => (x => elem)))
          case f@FieldAccess(Identifier(name, loc1), field, loc2) =>
            val rec = symbolicState.getSymbolicVal(name, loc1).asInstanceOf[RecVal]
            val r = rec.fields(name).asInstanceOf[Symbolic]
            Some(a, (iterations => (x => r)))
          case n@Number(_, _) =>
            Some(a, (iterations => (x => n)))
          case a@Alloc(expr, _) =>
            Some(a, (iterations => (x => a)))
          case in@Input(loc) =>
            Some(a, (iterations => (x => SymbolicVal(CodeLoc(0, 0)))))
          case id@Identifier(_, _) =>
            val v = symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic]
            Some(a, (iterations => (x => v)))
          case _ =>
            None
        }
   case _ => None
    }
  }



  def getAllPathsInALoop(stmt: CfgNode, symbolicState: SymbolicState): Option[List[Path]] = {
    var paths = List[Path]()
    var falsePath = new Path(List.empty, Number(1, stmt.ast.loc), mutable.HashMap())
    falsePath = falsePath.addedCondition(Not(stmt.ast.asInstanceOf[WhileStmt].guard, stmt.ast.loc))
    stmt.pred.minBy(node => node.id).ast match {
      case a@AssignStmt(Identifier(name, loc), expr, _) =>
        falsePath = falsePath.appendedStatement(a)
      case _ =>
    }
    paths = paths.appended(falsePath)
    val updatedVars = mutable.HashMap[PointerVal, Expr => Expr => Expr]()//getUpdatedVars(stmt.ast.asInstanceOf[WhileStmt])
    val pathsOpt = getAllTruePaths2(stmt.succ.minBy(node => node.id), stmt.id, symbolicState.deepCopy(), updatedVars)
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


  def getSymbolicRepressentation(v: Val, name: String, originalSymbolicState: SymbolicState, symbolicState: SymbolicState, symbolicState2: SymbolicState): Val = {
    val res = v match {
      case ArrVal(elems) =>
        ArrVal(elems.map(elem => {
            getSymbolicRepressentation(originalSymbolicState.getVal(elem).get, name, originalSymbolicState, symbolicState, symbolicState2)
          //in the recursive call the element is added to the last place
          PointerVal(symbolicState.symbolicStore.storage.size - 1)
          }))
      case _ =>
        SymbolicVal(CodeLoc(0, 0))
    }
    symbolicState.addedVar(name, v)
    symbolicState2.addedVar(name, v)
    res
  }


  def computePathRelationship(vertex1: Vertex, vertex2: Vertex, variables: List[IdentifierDecl], originalSymbolicState: SymbolicState): Option[Edge] = {
    val ctx = new Context()
    val solver = new ConstraintSolver(ctx)

    val changes = pathToVertex(vertex1.path)
    val iterations = vertex1.path.iterations

    var symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
    var symbolicState2 = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))

    val mapping: mutable.HashMap[Val, Identifier] = new mutable.HashMap[Val, Identifier]()
    for (v <- variables) {
      val tmpSymVal = getSymbolicRepressentation(originalSymbolicState.getSymbolicVal(v.name, v.loc, true), v.name, originalSymbolicState, symbolicState, symbolicState2)
      mapping.put(tmpSymVal, Identifier(v.name, v.loc))
    }
    changes.foreach(change => {
      change._1 match {
        case Identifier(name, loc) =>
          symbolicState = symbolicState.addedVar(name,
            change._2.apply(BinaryOp(Minus, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
              .apply(symbolicState.getSymbolicVal(name, CodeLoc(0, 0)).asInstanceOf[Symbolic]) match {
              case s@SymbolicVal(_) => s
              case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
              case _ => throw new Exception("IMPLEMENT")
            }
          )
        case ArrayAccess(Identifier(name, loc1), Number(value, _), loc2) =>
          val array = symbolicState.getSymbolicVal(name, CodeLoc(0, 0)).asInstanceOf[ArrVal]
          val valAtIndex = symbolicState.getVal(array.elems(value)).get
          val newPtr = symbolicState.addedAlloc(
            change._2.apply(BinaryOp(Minus, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)))
              .apply(valAtIndex.asInstanceOf[Symbolic]) match {
              case s@SymbolicVal(_) => s
              case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
              case _ => throw new Exception("IMPLEMENT")
            }
          )
          array.elems(value) = newPtr
      }
    })
    val path1Constraint = solver.applyTheState(vertex1.condition, symbolicState)
    val path1ConstraintOnce = solver.applyTheStateOnce(vertex1.condition, symbolicState)

    val resChanges = new mutable.HashMap[Expr, Expr => Expr]()
    for (change <- changes) {
      resChanges.put(change._1, change._2.apply(iterations))
    }
    changes.foreach(change => {
      change._1 match {
        case Identifier(name, loc) =>
          symbolicState2 = symbolicState2.addedVar(name,
            change._2.apply(iterations).apply(symbolicState2.getSymbolicVal(name, CodeLoc(0, 0)).asInstanceOf[Symbolic]) match {
              case s@SymbolicVal(_) => s
              case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
              case _ => throw new Exception("IMPLEMENT")
            }
          )
        case ArrayAccess(Identifier(name, loc1), Number(value, _), loc2) =>
          val array = symbolicState.getSymbolicVal(name, CodeLoc(0, 0)).asInstanceOf[ArrVal]
          val valAtIndex = symbolicState.getVal(array.elems(value)).get
          val newPtr = symbolicState.addedAlloc(
            change._2.apply(iterations).apply(valAtIndex.asInstanceOf[Symbolic]) match {
              case s@SymbolicVal(_) => s
              case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
              case _ => throw new Exception("IMPLEMENT")
            }
          )
          array.elems(value) = newPtr
    }})
    val ctxSolver = ctx.mkSolver()
    val path2Constraint = solver.applyTheState(vertex2.condition, symbolicState2)
    val path2ConstraintOnce = solver.applyTheStateOnce(vertex2.condition, symbolicState2)
    val pathsConstraints = {
      Utility.simplifyArithExpr(
        BinaryOp(
          AndAnd,
          BinaryOp(AndAnd, path1Constraint, path2Constraint, CodeLoc(0, 0)),
          BinaryOp(GreaterEqual, iterations, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)),
          CodeLoc(0, 0)
        )
      )
    }
    val pathsConstraintsOnce = {
      Utility.simplifyArithExpr(
          BinaryOp(AndAnd, path1ConstraintOnce, path2ConstraintOnce, CodeLoc(0, 0)),
      )
    }
    val constraint = solver.createConstraintWithState(pathsConstraints, symbolicState)
    val constraint2 = constraint.simplify()
    constraint match {
      case cond: BoolExpr => ctxSolver.add(cond)
    }
    ctxSolver.check() match {
      case Status.SATISFIABLE =>
        val tmp = applyMapping(pathsConstraints, mapping)
        println(tmp)
        Some(Edge(vertex2, tmp, resChanges))
      case _ =>
        None
    }
  }




  def applyMapping(expr: Expr, mapping: mutable.HashMap[Val, Identifier]): Expr = {
    expr match {
      case Not(expr, loc) =>
        Not(applyMapping(expr, mapping), loc)
      case BinaryOp(operator, left, right, loc) => BinaryOp(operator, applyMapping(left, mapping), applyMapping(right, mapping), loc)
      case i@Identifier(name, loc) => i
      case n@Number(_, _) => n
      case v@SymbolicVal(_) if mapping.contains(v) => mapping(v)
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => applyMapping(expr, mapping)
    }
  }





}

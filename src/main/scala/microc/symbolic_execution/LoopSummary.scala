package microc.symbolic_execution

import com.microsoft.z3.{BoolExpr, Context, Status}
import microc.ast.{AndAnd, AssignStmt, BinaryOp, CodeLoc, Divide, Equal, Expr, GreaterEqual, GreaterThan, Identifier, IdentifierDecl, IfStmt, LowerEqual, LowerThan, Minus, NestedBlockStmt, Not, NotEqual, Number, OrOr, Plus, Stmt, Times, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}
import microc.symbolic_execution.LoopSummary.{getAllTruePaths, simplifyArithExpr}
import microc.symbolic_execution.Value.{PointerVal, Symbolic, SymbolicExpr, SymbolicVal, UninitializedRef, Val}

import scala.collection.mutable

object LoopSummary {

  def simplifyArithExpr(expr: Expr): Expr = {//TODO if changed, repeat
    expr match {
      case n@Number(_, _) => n
      case BinaryOp(AndAnd, Number(1, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(OrOr, Number(0, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(AndAnd, expr, Number(1, _), _) => simplifyArithExpr(expr)
      case BinaryOp(OrOr, expr, Number(0, _), _) => simplifyArithExpr(expr)
      case BinaryOp(AndAnd, expr1, expr2, _) if expr1 == expr2 => simplifyArithExpr(expr1)
      case BinaryOp(OrOr, expr1, expr2, _) if expr1 == expr2 => simplifyArithExpr(expr1)
      case BinaryOp(Plus, expr, Number(0, _), _) => simplifyArithExpr(expr)
      case BinaryOp(Times, expr, Number(1, _), _) => simplifyArithExpr(expr)
      case BinaryOp(Plus, Number(0, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(Times, Number(1, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(operator, left, right, loc) =>
        (simplifyArithExpr(left), simplifyArithExpr(right)) match {
          case (Number(value, loc), Number(value2, _)) =>
            operator match {
              case Plus => Number(value + value2, loc)
              case Minus => Number(value - value2, loc)
              case Times => Number(value * value2, loc)
              case Divide => Number(value / value2, loc)
              case LowerThan => Number(if (value < value2) 1 else 0, loc)
              case LowerEqual => Number(if (value <= value2) 1 else 0, loc)
              case GreaterThan => Number(if (value > value2) 1 else 0, loc)
              case GreaterEqual => Number(if (value >= value2) 1 else 0, loc)
              case NotEqual => Number(if (value != value2) 1 else 0, loc)
              case Equal => Number(if (value == value2) 1 else 0, loc)
              case AndAnd => Number(if (value != 0 && value2 != 0) 1 else 0, loc)
              case OrOr => Number(if (value != 0 || value2 != 0) 1 else 0, loc)
            }
          case (a, b) =>
            BinaryOp(operator, a, b, loc)
        }
      case other => other
    }
  }


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
          if (Utility.varIsFromOriginalProgram(change._1)) {
            val ptr = newState.getSymbolicValOpt(change._1).get.asInstanceOf[PointerVal]
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
  val pathToVertex: mutable.HashMap[Path, mutable.HashMap[String, Expr => Expr => Expr]] = mutable.HashMap[Path, mutable.HashMap[String, Expr => Expr => Expr]]()


  def summarizeLoop(symbolicState: SymbolicState): Option[(mutable.HashSet[(Expr, mutable.HashMap[String, Expr => Expr])], SymbolicState)] = {
    summarizeLoopInner(symbolicState.nextStatement, symbolicState)
  }

  private def summarizeLoopInner(loop: CfgNode, symbolicState: SymbolicState): Option[(mutable.HashSet[(Expr, mutable.HashMap[String, Expr => Expr])], SymbolicState)] = {

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
                simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
            case BinaryOp(Minus, Identifier(name2, loc1), Number(value, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
            case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(_, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc1)))))
            case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(_, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Not(symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc2), loc1)))))
            case BinaryOp(Plus, n@Number(_, loc2), Identifier(name2, loc1),  _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
            case BinaryOp(Minus, Number(value, loc2), Identifier(name2, loc1), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
            case BinaryOp(Plus, id@Identifier(_, loc2), Identifier(name2, loc1), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc1)))))
            case BinaryOp(Minus, id@Identifier(_, loc2), Identifier(name2, loc1), _) if name == name2 =>
              variableChange += (name -> (iterations => (x =>
                simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Not(symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc2), loc1)))))

            case expr if !Utility.varIsFromOriginalProgram(name) =>
              variableChange += (name -> (iterations => (x => simplifyArithExpr(expr))))
            case _ =>

          }
        case _ =>
      }
    }
    variableChange
  }


  def getAllTruePaths2(stmt: CfgNode, loopId: Int, symbolicState: SymbolicState, updatedVars: mutable.HashSet[String]): Option[List[Path]] = {
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
              if (Utility.varIsFromOriginalProgram(update._1)) {
                val x = update._2.apply(Number(0, CodeLoc(0, 0)))
                paths = paths.map(path =>
                  path.updatedChanges(update._1,
                    iterations => x => simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, update._2.apply(x), CodeLoc(0, 0)), CodeLoc(0, 0)))
                  )
                )
                if (symbolicState.containsVar(update._1)) {
                  symbolicState.applyChange(update._1, update._2)
                }
              }
            }
          }
          curr = curr.succ.filter(node => node.id != curr.id + 1).head
        case otherStmt: AssignStmt =>
          val changeOpt = computeVariableChange2(otherStmt, symbolicState, updatedVars)
          stepOnAssign(otherStmt, symbolicState)
          if (changeOpt.nonEmpty) {
            val change = changeOpt.get
            paths = paths.map(path => path.appendedStatement(otherStmt).updatedChanges(change._1, change._2))
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


  def computeVariableChange2(stmt: Stmt, symbolicState: SymbolicState, updatedVars: mutable.HashSet[String]): Option[(String, (Expr) => ((Expr) => Expr))] = {
    stmt match {
      case AssignStmt(Identifier(name, loc), expr, _) =>
        simplifyArithExpr(expr) match {
          case BinaryOp(_, SymbolicVal(_), _, _) =>
            None
          case BinaryOp(_, _, SymbolicVal(_), _) =>
            None
          case BinaryOp(Plus, Identifier(name2, loc1), n@Number(_, loc2), _) if name == name2 =>
            Some(name, (iterations => (x =>
              simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
          case BinaryOp(Minus, Identifier(name2, loc1), Number(value, loc2), _) if name == name2 =>
            Some(name, (iterations => (x =>
              simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
          case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(name3, loc2), _) if name == name2 && updatedVars.contains(name3) =>
            None
          case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(name3, loc2), _) if name == name2 && updatedVars.contains(name3) =>
            None
          case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(name3, loc2), _) if name == name3 && updatedVars.contains(name2) =>
            None
          case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(name3, loc2), _) if name == name3 && updatedVars.contains(name2) =>
            None
          case BinaryOp(Plus, Identifier(name2, loc1), id@Identifier(_, loc2), _) if name == name2 =>
            Some(name, (iterations => (x =>
              simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc1)))))
          case BinaryOp(Minus, Identifier(name2, loc1), id@Identifier(_, loc2), _) if name == name2 =>
            Some(name, (iterations => (x =>
              simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Not(symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc2), loc1)))))
          case BinaryOp(Plus, n@Number(_, loc2), Identifier(name2, loc1), _) if name == name2 =>
            Some(name, (iterations => (x =>
              simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
          case BinaryOp(Minus, Number(value, loc2), Identifier(name2, loc1), _) if name == name2 =>
            Some(name, (iterations => (x =>
              simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
          case BinaryOp(Plus, id@Identifier(_, loc2), Identifier(name2, loc1), _) if name == name2 =>
            Some(name, (iterations => (x =>
              simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc1)))))
          case BinaryOp(Minus, id@Identifier(_, loc2), Identifier(name2, loc1), _) if name == name2 =>
            Some(name, (iterations => (x =>
              simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Not(symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic], loc2), loc2), loc1)))))
          case expr: BinaryOp if !Utility.varIsFromOriginalProgram(name) =>
            Some(name, (iterations => (x => simplifyArithExpr(expr))))
          case n@Number(_, _) =>
            Some(name, (iterations => (x => n)))
          case id@Identifier(_, _) =>
            Some(name, (iterations => (x => symbolicState.getSymbolicVal(id.name, id.loc).asInstanceOf[Symbolic])))
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
    val updatedVars = getUpdatedVars(stmt.ast.asInstanceOf[WhileStmt])
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
        case AssignStmt(left: Identifier, _, _) => res.add(left.name)
        case _ =>
      }
    }
    res
  }



  def computePathRelationship(vertex1: Vertex, vertex2: Vertex, variables: List[IdentifierDecl], symbolicState: SymbolicState): Option[Edge] = {
    val ctx = new Context()
    val solver = new ConstraintSolver(ctx)

    val changes = pathToVertex(vertex1.path)
    val iterations = vertex1.path.iterations

    var symbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
    var symbolicState2 = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))

    val mapping: mutable.HashMap[SymbolicVal, Identifier] = new mutable.HashMap[SymbolicVal, Identifier]()
    for (v <- variables) {
      val tmpSymVal = SymbolicVal(v.loc)
      symbolicState = symbolicState.addedVar(v.name, tmpSymVal)
      symbolicState2 = symbolicState2.addedVar(v.name, tmpSymVal)
      mapping.put(tmpSymVal, Identifier(v.name, v.loc))
    }
    changes.foreach(change => {
      symbolicState = symbolicState.addedVar(change._1,
        change._2.apply(BinaryOp(Minus, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0))).apply(symbolicState.getSymbolicVal(change._1, CodeLoc(0, 0)).asInstanceOf[Symbolic]) match {
          case s@SymbolicVal(_) => s
          case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
          case _ => throw new Exception("IMPLEMENT")
        }
      )
      val v = symbolicState.getSymbolicVal(change._1, CodeLoc(0, 0))
      v match {
        case s@SymbolicVal(_) => s
        case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
        case _ => throw new Exception("This should not happen")
      }
    })
    val path1Constraint = solver.applyTheState(vertex1.condition, symbolicState)
    val path1ConstraintOnce = solver.applyTheStateOnce(vertex1.condition, symbolicState)

    val resChanges = new mutable.HashMap[String, Expr => Expr]()
    for (change <- changes) {
      resChanges.put(change._1, change._2.apply(iterations))
    }
    changes.foreach(change => {
      symbolicState2 = symbolicState2.addedVar(change._1,
        change._2.apply(iterations).apply(symbolicState2.getSymbolicVal(change._1, CodeLoc(0, 0)).asInstanceOf[Symbolic]) match {
          case s@SymbolicVal(_) => s
          case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
          case _ => throw new Exception("IMPLEMENT")
        }
      )
      val v = symbolicState2.getSymbolicVal(change._1, CodeLoc(0, 0)) match {
        case s@SymbolicVal(_) => s
        case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
        case _ => throw new Exception("This should not happen")
      }
    })
    val ctxSolver = ctx.mkSolver()
    val path2Constraint = solver.applyTheState(vertex2.condition, symbolicState2)
    val path2ConstraintOnce = solver.applyTheStateOnce(vertex2.condition, symbolicState2)
    val pathsConstraints = {
      simplifyArithExpr(
        BinaryOp(
          AndAnd,
          BinaryOp(AndAnd, path1Constraint, path2Constraint, CodeLoc(0, 0)),
          BinaryOp(GreaterEqual, iterations, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)),
          CodeLoc(0, 0)
        )
      )
    }
    val pathsConstraintsOnce = {
      simplifyArithExpr(
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
        val tmp2 = {
          applyMapping(
            simplifyArithExpr(
              BinaryOp(
                AndAnd,
                path2Constraint,
                BinaryOp(GreaterEqual, iterations, Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)),
                CodeLoc(0, 0)
              )
            ),
            mapping
          )
        }
        Some(Edge(vertex2, tmp, resChanges))
      case _ =>
        None
    }
  }




  def applyMapping(expr: Expr, mapping: mutable.HashMap[SymbolicVal, Identifier]): Expr = {
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

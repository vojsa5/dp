package microc.symbolic_execution

import com.microsoft.z3.{BoolExpr, Context, Status}
import microc.ast.{AndAnd, AssignStmt, BinaryOp, CodeLoc, Divide, Equal, Expr, GreaterEqual, GreaterThan, Identifier, IdentifierDecl, IfStmt, LowerEqual, LowerThan, Minus, Not, NotEqual, Number, OrOr, Plus, Stmt, Times, WhileStmt}
import microc.cfg.{CfgNode, ProgramCfg}
import microc.symbolic_execution.LoopSummary.{computeVariableChange, getAllPathsInALoop2, simplifyArithExpr}
import microc.symbolic_execution.Value.{PointerVal, Symbolic, SymbolicExpr, SymbolicVal, UninitializedRef, Val}

import java.util
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
            }
          case (a, b) =>
            BinaryOp(operator, a, b, loc)
        }
      case other => other
    }
  }

  def computeVariableChange(stmts: List[Stmt]): mutable.HashMap[String, (Expr) => ((Expr) => Expr)] = {
    var variableChange = mutable.HashMap[String, Expr => (Expr => Expr)]()
    val num_it_variable = "TODO make this dynamic"
    for (stmt <- stmts) {
      stmt match {
        case AssignStmt(Identifier(name, loc), expr, _) =>
          expr match {
            case BinaryOp(Plus, Identifier(name2, loc1), n@Number(_, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x => simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1)))))
              //variableChange += (name -> (iterations => (x => BinaryOp(Plus, x, BinaryOp(Times, iterations, n, loc2), loc1))))
            case BinaryOp(Minus, Identifier(name2, loc1), Number(value, loc2), _) if name == name2 =>
              variableChange += (name -> (iterations => (x => simplifyArithExpr(BinaryOp(Plus, x, BinaryOp(Times, iterations, Number(-value, loc2), loc2), loc1)))))
            case expr =>
              variableChange += (name -> (iterations => (x => simplifyArithExpr(expr))))

          }
        case _ =>
      }
    }
    variableChange
  }

  def getAllPathsInALoop2(stmt: CfgNode, loopId: Int): List[Path] = {
    var paths = List[Path]()
    paths = paths.appended(new Path(List[Stmt](), Number(1, CodeLoc(0, 0))))
    var curr = stmt
    while (curr.id != loopId) {
      curr.ast match {
        case IfStmt(guard, _, _, _) =>
          paths = paths.flatMap(
            path => {
              paths = getAllPathsInALoop2(curr.succ.head, loopId)
                .map(pathContinuation => pathContinuation.addedCondition(guard))
                .map(pathContinuation => path.appendedAsPath(pathContinuation))
              paths = paths.appendedAll(
                getAllPathsInALoop2(curr.succ.tail.head, loopId)
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


class LoopSummary(program: ProgramCfg) extends SymbolicExecutor(program) {


  override def stepOnLoop(symbolicState: SymbolicState): Unit = {
    var vertices: List[Vertex] = List()
    val paths = getAllPathsInALoop(symbolicState.nextStatement)
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, pathToVertex(path), path.iterations))
    }
    val pda = PDA(this, vertices, symbolicState.variableDecls, solver, Number(1, CodeLoc(0, 0)), symbolicState)
    pda.initialize()
    var newState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))

    for (v <- symbolicState.variableDecls) {
      val tmpSymVal = SymbolicVal(v.loc)
      newState = newState.addedVar(v.name, tmpSymVal)
    }
    val summary = pda.summarizeType1Loop2(symbolicState)
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
          tmpState = tmpState.updatedVar(ptr, SymbolicExpr(trace._2(change._1).apply(ptrVal.get.asInstanceOf[Symbolic]), CodeLoc(0, 0)))
        }
      }
      step(tmpState)
    }
  }


  val pathToVertex: mutable.HashMap[Path, mutable.HashMap[String, Expr => Expr => Expr]] = mutable.HashMap[Path, mutable.HashMap[String, Expr => Expr => Expr]]()

  def getAllPathsInALoop(stmt: CfgNode): List[Path] = {
    var paths = List[Path]()
    var falsePath = new Path(List.empty, Number(1, stmt.ast.loc))
    falsePath = falsePath.addedCondition(Not(stmt.ast.asInstanceOf[WhileStmt].guard, stmt.ast.loc))
    stmt.pred.minBy(node => node.id).ast match {
      case a@AssignStmt(Identifier(name, loc), expr, _) =>
        falsePath = falsePath.appendedStatement(a)
      case _ =>
    }
    paths = paths.appended(falsePath)
    paths = paths.appendedAll(getAllPathsInALoop2(stmt.succ.minBy(node => node.id), stmt.id)
      .map(path => path.addedCondition(stmt.ast.asInstanceOf[WhileStmt].guard))
      .map(path => path.simplifiedCondition())
    )
    for (path <- paths) {
      pathToVertex.put(path, computeVariableChange(path.statements))
    }
    paths
  }



  def computePDA(paths: List[Path], variables: List[IdentifierDecl], symbolicState: SymbolicState): Unit = {


    for {
      (path1, index1) <- paths.zipWithIndex
      (path2, index2) <- paths.zipWithIndex if index1 != index2
    } {
      null;
      path1;
      path2;
      index1;
      index2;


    }
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








//  def computePathRelationship(vertex1: Vertex, vertex2: Vertex, variables: List[IdentifierDecl], symbolicState: SymbolicState): Option[Edge] = {
//
//    val ctx = new Context()
//    val solver = new ConstraintSolver(ctx)
//
//    val changes = pathToVertex(vertex1.path)
//    val iterations = vertex1.path.iterations
//
//    //var tmpSymbolicState = new SymbolicState(null, PathCondition.initial(), new SymbolicStore(Map.empty))
//    var tmpSymbolicState = symbolicState.deepCopy()
//    for (v <- variables) {
//      symbolicState.getSymbolicVal(v.name, CodeLoc(0, 0), true) match {
//        case UninitializedRef => {
//          tmpSymbolicState = tmpSymbolicState.addedVar(v.name, SymbolicVal(v.loc))
//        }
//        case _ =>
//      }
//    }
//    changes.foreach(change => {
//      val initialValue = if (Utility.varIsFromOriginalProgram(change._1)) {
//        solver.applyVal(symbolicState.getSymbolicVal(change._1, CodeLoc(0, 0), true), tmpSymbolicState)
//      }
//      else {
//        solver.applyVal(tmpSymbolicState.getSymbolicVal(change._1, CodeLoc(0, 0), true), tmpSymbolicState)
//      }
//      //val initialValue = solver.applyVal(tmpSymbolicState.getSymbolicVal(change._1, CodeLoc(0, 0), true), tmpSymbolicState)
//      tmpSymbolicState = tmpSymbolicState.addedVar(change._1,
//        change._2.apply(BinaryOp(Minus, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0))).apply(initialValue) match {
//          case s@SymbolicVal(_) => s
//          case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
//          case _ => throw new Exception("IMPLEMENT")
//        }
//      )
//      val v = tmpSymbolicState.getSymbolicVal(change._1, CodeLoc(0, 0))
//      v match {
//        case s@SymbolicVal(_) => s
//        case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
//        case _ => throw new Exception("This should not happen")
//      }
//    })
//    val path1Constraint = solver.applyTheState(vertex1.condition, tmpSymbolicState, true)
//
//    val resChanges = new mutable.HashMap[String, Expr => Expr]()
//    for (change <- changes) {
//      resChanges.put(change._1, change._2.apply(iterations))
//    }
//    changes.foreach(change => {
//      val initialValue = if (Utility.varIsFromOriginalProgram(change._1)) {
//        solver.applyVal(symbolicState.getSymbolicVal(change._1, CodeLoc(0, 0), true), tmpSymbolicState)
//      }
//      else {
//        solver.applyVal(tmpSymbolicState.getSymbolicVal(change._1, CodeLoc(0, 0), true), tmpSymbolicState)
//      }
//      tmpSymbolicState = tmpSymbolicState.addedVar(change._1,
//        change._2.apply(iterations).apply(initialValue) match {
//          case s@SymbolicVal(_) => s
//          case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
//          case _ => throw new Exception("IMPLEMENT")
//        }
//      )
//      val v = tmpSymbolicState.getSymbolicVal(change._1, CodeLoc(0, 0)) match {
//        case s@SymbolicVal(_) => s
//        case e: Expr => SymbolicExpr(e, CodeLoc(0, 0))
//        case _ => throw new Exception("This should not happen")
//      }
//    })
//    val ctxSolver = ctx.mkSolver()
//    val path2Constraint = solver.applyTheState(vertex2.condition, tmpSymbolicState, true)
//    val pathsConstraints =
//      simplifyArithExpr(
//        BinaryOp(
//          AndAnd,
//          BinaryOp(AndAnd, path1Constraint, path2Constraint, CodeLoc(0, 0)),
//          BinaryOp(GreaterEqual, iterations, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)),
//          CodeLoc(0, 0)
//        )
//      )
//    val constraint = solver.createConstraintWithState(pathsConstraints, tmpSymbolicState)
//    constraint match {
//      case cond: BoolExpr => ctxSolver.add(cond)
//    }
//    ctxSolver.check() match {
//      case Status.SATISFIABLE =>
////        val i = solver.applyTheStateOnce(vertex1.condition, tmpSymbolicState)
////        val j = solver.applyTheStateOnce(vertex2.condition, tmpSymbolicState)
////        val o = BinaryOp(AndAnd, solver.applyTheStateOnce(vertex1.condition, tmpSymbolicState), solver.applyTheStateOnce(vertex2.condition, tmpSymbolicState), CodeLoc(0, 0))
//        //Some(Edge(vertex2, BinaryOp(AndAnd, solver.applyTheStateOnce(vertex1.condition, tmpSymbolicState), solver.applyTheStateOnce(vertex2.condition, tmpSymbolicState), CodeLoc(0, 0)), resChanges))
//        Some(Edge(vertex2, pathsConstraints, resChanges))
//      case _ =>
//        None
//    }
//  }


}

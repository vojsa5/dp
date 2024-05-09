package microc.symbolic_execution

import microc.ast.{AndAnd, ArrayAccess, AssignStmt, BinaryOp, CodeLoc, Equal, Expr, FieldAccess, FunDecl, GreaterThan, Identifier, IdentifierDecl, LowerEqual, LowerThan, NestedBlockStmt, Number, WhileStmt}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.{Examples, MicrocSupport, symbolic_execution}
import munit.FunSuite
import com.microsoft.z3.{BoolExpr, Context, Status}
import microc.symbolic_execution.Value.{ArrVal, PointerVal, RecVal, SymbolicExpr, SymbolicVal, UninitializedRef, Val}
import microc.symbolic_execution.optimizations.Path
import microc.symbolic_execution.optimizations.summarization.{LoopSummarization, PDA, Vertex}

import scala.collection.mutable


class LoopSummarizationTest extends FunSuite with MicrocSupport with Examples {



  test("get all paths in a sequential loop") {
    val code =
      """
        |main() {
        |  var k, i, n, m;
        |  k = 0;
        |  i = 0;
        |  n = input;
        |  m = input;
        |  while (n < m) {
        |   k = k + 5;
        |   i = i + 2;
        |   n = n + 1;
        |  }
        |  return k * i;
        |}
        |""".stripMargin;
    val ctx = new Context()
    val constraintSolver = new ConstraintSolver(ctx)
    var symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val executor = new LoopSummarization(cfg)
    var stmt: CfgNode = cfg.getFce("main")
    val decls = stmt.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    symbolicState = symbolicState.updateVar("n", SymbolicVal(CodeLoc(1, 0)))
    symbolicState = symbolicState.updateVar("m", SymbolicVal(CodeLoc(2, 0)))
    symbolicState = symbolicState.updateVar("k", Number(0, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("i", Number(0, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("_t1", SymbolicExpr(BinaryOp(LowerThan, Identifier("n", CodeLoc(0, 0)), Identifier("m", CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))//normalized condition
    symbolicState = symbolicState.updateVar("_t2", UninitializedRef)
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    assert(paths.size == 2)
    var reachedEmpty = false
    for (i <- 0 until 2) {
      if (paths(i).statements.length == 1) {
        if (!reachedEmpty) {
          val n = ctx.mkIntConst("n")
          val m = ctx.mkIntConst("m")
          val comparison = ctx.mkGe(n, m)
          val constraint = ctx.mkEq(constraintSolver.createConstraint(paths(i).condition, symbolicState), comparison)
          val solver = ctx.mkSolver()
          constraint match {
            case cond: BoolExpr => solver.add(cond)
          }
          solver.check() match {
            case Status.SATISFIABLE =>
            case _ => fail("")
          }
          reachedEmpty = true
        }
        else {
          fail("Multiple empty paths in the loop")
        }
      }
      else {
        val path = paths(i)
        assert(path.statements.size == 4)
        assert(path.statements(0).isInstanceOf[AssignStmt])
        assert(path.statements(1).isInstanceOf[AssignStmt])
        assert(path.statements(2).isInstanceOf[AssignStmt])
        assert(path.statements(3).isInstanceOf[AssignStmt])
        val n = ctx.mkIntConst("n")
        val m = ctx.mkIntConst("m")
        val comparison = ctx.mkLt(n, m)
        val constraint = ctx.mkEq(constraintSolver.createConstraint(paths(i).condition, symbolicState), comparison)
        val solver = ctx.mkSolver()
        constraint match {
          case cond: BoolExpr => solver.add(cond)
        }
        solver.check() match {
          case Status.SATISFIABLE =>
          case _ => fail("")
        }
      }
    }
    assert(reachedEmpty)
  }

  test("summary") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(!pda.checkForConnectedCycles())
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(0, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
            val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
            assert(v.nonEmpty)
            val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
            if (v.toSet.size >= 2) {
              Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                case Number(value, _) =>
                  assert(value == trueRes)
                case a@_ =>
                  assert(false)

              }
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
              val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
              assert(v.nonEmpty)
              if (v.toSet.size >= 2) {
                Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                  case Number(value, _) =>
                    assert(value == trueRes)
                  case a@_ =>
                    Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                      case Number(value, _) =>
                        assert(value == trueRes + initialIterationCount)
                      case _ =>
                        assert(false)

                  }
                }
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }


  test("summary 1.5") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x + 1 < n) {
        |   if (z + 1 > x + 1) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
            var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
            assert(v.nonEmpty)
            val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
            if (v.toSet.size >= 2) {
              Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                case Number(value, _) =>
                  assert(value == trueRes)
                case a@_ =>
                  assert(false)

              }
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
              val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
              assert(v.nonEmpty)
              if (v.toSet.size >= 2) {
                Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                  case Number(value, _) =>
                    assert(value == trueRes)
                  case a@_ =>
                    Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                      case Number(value, _) =>
                        assert(value == trueRes + initialIterationCount)
                      case _ =>
                        assert(false)
                  }
                }
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }



  test("summary 1.6") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x + 1 + 1 < n) {
        |   if (z + 1 + 1 > x + 1 + 1) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
            var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
            assert(v.nonEmpty)
            val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
            if (v.toSet.size >= 2) {
              Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                case Number(value, _) =>
                  assert(value == trueRes)
                case a@_ =>
                  assert(false)
              }
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
              val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
              assert(v.nonEmpty)
              if (v.toSet.size >= 2) {
                Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                  case Number(value, _) =>
                    assert(value == trueRes)
                  case a@_ =>
                    Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                      case Number(value, _) =>
                        assert(value == trueRes + initialIterationCount)
                      case _ =>
                        assert(false)
                    }
                }
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }

//finish the code
  test("summary bigger increment") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 2;
        |   }
        |   else {
        |     z = z + 2;
        |   }
        |  }
        |
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + 2 * initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
            var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
            assert(v.nonEmpty)
            val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
            if (v.toSet.size >= 2) {
              Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                case Number(value, _) =>
                  assert(value - trueRes <= 1)
                case a@_ =>
                  assert(false)
              }
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
              val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
              assert(v.nonEmpty)
              if (v.toSet.size >= 2) {
                Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                  case Number(value, _) =>
                    assert(value - trueRes <= 1)
                  case a@_ =>
                    Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                      case Number(value, _) =>
                        assert(value - trueRes - 2 * initialIterationCount <= 1)
                      case _ =>
                        assert(false)
                    }
                }
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }


  test("summary2") {
    val code =
      """
        |main() {
        |  var n, x, z, a;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     a = x + 1;
        |     x = a;
        |   }
        |   else {
        |     a = z + 1;
        |     z = a;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "x" }.get._2
            val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
            var v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
            assert(v.nonEmpty)
            val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
            if (v.toSet.size >= 2) {
              Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                case Number(value, _) =>
                  assert(value == trueRes)
                case a@_ =>
                  assert(false)
              }
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists { case (Identifier(name, loc), _) => name == "z" }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  { case (Identifier(name, loc), _) => name == "z" }.get._2
              val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
              val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
              assert(v.nonEmpty)
              if (v.toSet.size >= 2) {
                Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                  case Number(value, _) =>
                    assert(value == trueRes)
                  case a@_ =>
                    Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                      case Number(value, _) =>
                        assert(value == trueRes + initialIterationCount)
                      case _ =>
                        assert(false)
                    }
                }
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }


  test("summary arrays") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = [input];
        |  z = [input];
        |  while (x[0] < n) {
        |   if (z[0] > x[0]) {
        |     x[0] = x[0] + 1;
        |   }
        |   else {
        |     z[0] = z[0] + 1;
        |   }
        |  }
        |  return 1 / (x[0] - z[0]);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
      if (decl.name == "x" || decl.name == "z") {
        symbolicState.updateVar(decl.name, ArrVal(Array(symbolicState.getSymbolicValOpt(decl.name).get.asInstanceOf[PointerVal])))
      }
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState.deepCopy(), mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  {
              case (ArrayAccess(Identifier(name, _), _, loc), _) => name == "x" || name == "z"
              case (Identifier(_, _), _) => false
            }.get._2
            val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
            val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
            assert(v.nonEmpty)
            val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
            if (v.toSet.size >= 2) {
              Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                case Number(value, _) =>
                  assert(value == trueRes)
                case a@_ =>
                  assert(false)
              }
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists {
              case (ArrayAccess(Identifier(name, _), _, loc), _) => name == "z"
              case (Identifier(_, _), _) => false
            }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  {
                case (ArrayAccess(Identifier(name, _), _, loc), _) => name == "z"
                case (Identifier(_, _), _) => false
              }.get._2
              val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
              val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
              assert(v.nonEmpty)
              if (v.toSet.size >= 2) {
                Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                  case Number(value, _) =>
                    assert(value == trueRes)
                  case a@_ =>
                    Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                      case Number(value, _) =>
                        assert(value == trueRes + initialIterationCount)
                      case _ =>
                        assert(false)
                    }
                }
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }



  test("summary records") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = {field: input};
        |  z = {field: input};
        |  while (x.field < n) {
        |   if (z.field > x.field) {
        |     x.field = x.field + 1;
        |   }
        |   else {
        |     z.field = z.field + 1;
        |   }
        |  }
        |  return 1 / (x.field - z.field);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
      if (decl.name == "x" || decl.name == "z") {
        val fields = mutable.HashMap[String, PointerVal]()
        fields.put("field", symbolicState.getSymbolicValOpt(decl.name).get)
        symbolicState.updateVar(decl.name, RecVal(fields))
      }
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState.deepCopy(), mapping)
    pda.initialize()
    assert(pda.entryStates.size == 3)
    assert(pda.exitStates.size == 1)
    assert(pda.edges.size == 3)

    val summary = pda.summarizeType1Loop2(symbolicState).get

    var lastIterCount = Number(1, CodeLoc(0, 0))
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + initialIterationCount + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            val change: Expr => SymbolicState => Expr = trace._2.find  {
              case (FieldAccess(Identifier(name, _), _, loc), _) => name == "x" || name == "z"
              case (Identifier(_, _), _) => false
            }.get._2
            val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
            val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
            assert(v.nonEmpty)
            val applied = pda.applyIterationsCount(expr, v.head, Number(initialIterationCount, CodeLoc(0, 0)))
            if (v.size >= 2) {
              Utility.simplifyArithExpr(pda.applyIterationsCount(Utility.simplifyArithExpr(applied), v.tail.head, lastIterCount)) match {
                case Number(value, _) =>
                  assert(value == trueRes)
                case a@_ =>
                  assert(false)
              }
            }
          }
        }
      }
    }

    lastIterCount = Number(0, CodeLoc(0, 0))
    var missingZ = 0;
    for (initialX <- 0 to 5) {
      for (initialIterationCount <- 0 to 5) {
        val trueRes = initialX + lastIterCount.value
        for (trace <- summary) {
          if (trace._2.nonEmpty) {
            if (trace._2.exists {
              case (FieldAccess(Identifier(name, _), _, loc), _) => name == "z"
              case (Identifier(_, _), _) => false
            }) {
              val change: Expr => SymbolicState => Expr = trace._2.find  {
                case (FieldAccess(Identifier(name, _), _, loc), _) => name == "z"
                case (Identifier(_, _), _) => false
              }.get._2
              val expr = change.apply(Number(initialX, CodeLoc(0, 0))).apply(symbolicState)
              val v = LoopSummarization.getSymbolicValsFromExpr(expr, symbolicState)
              assert(v.nonEmpty)
              if (v.size >= 2) {
                Utility.simplifyArithExpr(pda.applyIterationsCount(expr, v.head, lastIterCount)) match {
                  case Number(value, _) =>
                    assert(value == trueRes)
                  case a@_ =>
                    Utility.simplifyArithExpr(pda.applyIterationsCount(a, v.tail.head, Number(initialIterationCount, CodeLoc(0, 0)))) match {
                      case Number(value, _) =>
                        assert(value == trueRes + initialIterationCount)
                      case _ =>
                        assert(false)
                    }
                }
              }
            }
            else {
              missingZ += 1;
            }
          }
        }
      }
    }
    assert(missingZ / 36 == 1)//else branch encountered 6 * 6 times
  }





  test("empty loop finishes") {
    var code =
      """
        |main() {
        |    while (input) {
        |
        |    }
        |    return 1;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new LoopSummarization(cfg)
    executor.run()
    null
  }


  test("uncomputable change") {
    var code =
      """
        |main() {
        |    var i, j, k, n;
        |    i = 0;
        |    k = input;
        |    n = input;
        |    j = 0;
        |    while (k < n) {
        |       j = j + 1;
        |       i = i + j;
        |    }
        |    return 1;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt
    val decls = stmt.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }

    var symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    symbolicState = symbolicState.updateVar("j", Number(1, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("i", Number(0, CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("k", SymbolicVal(CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("n", SymbolicVal(CodeLoc(0, 0)))
    symbolicState = symbolicState.updateVar("_t1", SymbolicVal(CodeLoc(0, 0)))

    val executor = new LoopSummarization(cfg)
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.isEmpty)
  }


  test("summary type2") {
    val code =
      """
        |main() {
        |  var i, j, a;
        |  i = input;
        |  j = input;
        |  a = input;
        |  while (i < 100) {
        |   if (a <= 5) {
        |     a = a + 1;
        |   }
        |   else {
        |     a = a - 4;
        |   }
        |   if (j < 8) {
        |     j = j + 1;
        |   }
        |   else {
        |     j = j - 3;
        |   }
        |   i = i + 1;
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    var vertices :List[Vertex] = List()
    for (path <- paths) {
      vertices = vertices.appended(Vertex(path, path.condition, executor.pathToVertex(path), path.iterations))
    }
    val pda = PDA(executor, vertices, new ConstraintSolver(new Context()), Number(1, CodeLoc(0, 0)), symbolicState, mapping)
    assert(!pda.checkForConnectedCycles())
    pda.initialize()
    for (edge <- pda.edges) {
      if (edge._1.statements.size > 1) {
        assert(edge._2.size == 4)
      }
      else {
        assert(edge._2.isEmpty)
      }
    }
    null
  }


  test("change identity function") {
    val code =
      """
        |main() {
        |  var i, j, k, n;
        |  i = input;
        |  k = 1;
        |  n = input;
        |  while (i < n) {
        |     k = k;
        |     j = k;
        |     i = i + 1;
        |  }
        |  return k;
        |}
        |""".stripMargin;


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    symbolicState.updateVar("k", Number(1, CodeLoc(0, 0)))
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get
    for (path <- paths) {
      if (path.changes.nonEmpty) {
        val j = path.changes.find(ch => ch._1.asInstanceOf[Identifier].name == "j").get._2.apply(Number(1, CodeLoc(0, 0))).apply(Number(1, CodeLoc(0, 0))).apply(symbolicState)
        j match {
          case Number(value, _) =>
            assert(value == 1)
          case _ =>
            assert(false)
        }
        val k = path.changes.find(ch => ch._1.asInstanceOf[Identifier].name == "k").get._2.apply(Number(1, CodeLoc(0, 0))).apply(Number(1, CodeLoc(0, 0))).apply(symbolicState)
        k match {
          case Number(value, _) =>
            assert(value == 1)
          case _ =>
            assert(false)
        }
      }
    }
  }


  test("periods of cycles") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get

    val v1 = Vertex(paths(0), paths(0).condition, executor.pathToVertex(paths(0)), paths(0).iterations)
    val v2 = Vertex(paths(1), paths(1).condition, executor.pathToVertex(paths(1)), paths(1).iterations)
    var period = executor.computePeriod(v1, v2, v1)
    assert(period.nonEmpty)
    assert(period.get == 1)

    period = executor.computePeriod(v2, v1, v2)
    assert(period.nonEmpty)
    assert(period.get == 1)
    null
  }


  test("periods of cycles bigger increment") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 2;
        |   }
        |   else {
        |     z = z + 2;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get

    val v1 = Vertex(paths(0), paths(0).condition, executor.pathToVertex(paths(0)), paths(0).iterations)
    val v2 = Vertex(paths(1), paths(1).condition, executor.pathToVertex(paths(1)), paths(1).iterations)
    var period = executor.computePeriod(v1, v2, v1)
    assert(period.nonEmpty)
    assert(period.get == 1)

    period = executor.computePeriod(v2, v1, v2)
    assert(period.nonEmpty)
    assert(period.get == 1)
    null
  }

  test("periods of cycles bigger increment 2") {
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 2;
        |   }
        |  }
        |  return 1 / (x - z);
        |}
        |""".stripMargin;

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var stmt: CfgNode = cfg.getFce("main")
    val main = stmt

    while (!stmt.ast.isInstanceOf[WhileStmt]) {
      stmt = stmt.succ.head
    }
    val executor = new LoopSummarization(cfg)
    val decls = main.ast.asInstanceOf[FunDecl].block.vars.flatMap(_.decls)
    val symbolicState = new SymbolicState(null, Number(1, CodeLoc(0, 0)), new SymbolicStore(Map.empty))
    for (decl <- decls) {
      symbolicState.updateVar(decl.name, SymbolicVal(decl.loc))
    }
    val mapping = mutable.HashMap[Val, Expr]()
    val memoryCells = executor.getMemoryCellsFromConditions(executor.getAllConditionsInALoop(cfg, stmt))
    val pathsOpt = executor.getAllPathsInALoop(stmt, symbolicState, LoopSummarization.createSymbolicStateWithAllValuesSymbolic(symbolicState, mapping),
      memoryCells, mutable.HashMap(), mutable.HashSet(), mutable.HashSet(), mutable.HashSet(), mapping)
    assert(pathsOpt.nonEmpty)
    val paths = pathsOpt.get

    val v1 = Vertex(paths(0), paths(0).condition, executor.pathToVertex(paths(0)), paths(0).iterations)
    val v2 = Vertex(paths(1), paths(1).condition, executor.pathToVertex(paths(1)), paths(1).iterations)
    var period = executor.computePeriod(v1, v2, v1)
    assert(period.nonEmpty)
    assert(period.get == 1)

    period = executor.computePeriod(v2, v1, v2)
    assert(period.isEmpty)
    null
  }
}

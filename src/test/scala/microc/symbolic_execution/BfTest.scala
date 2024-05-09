package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.analyses.RecursionBasedAnalyses
import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.symbolic_execution.optimizations.merging.{AggressiveStateMerging, DynamicStateMerging, HeuristicBasedStateMerging}
import microc.symbolic_execution.optimizations.subsumption.PathSubsumption
import microc.{Examples, MicrocSupport}
import munit.FunSuite

import scala.collection.mutable

class BfTest extends FunSuite with MicrocSupport with Examples {
  val bfCode = """
                 |list_append(list, x) {
                 |    var node;
                 |
                 |    node = alloc {v: x, prev: list, next: null};
                 |    if (list == null) {
                 |    } else {
                 |        (*list).next = node;
                 |    }
                 |
                 |    return node;
                 |}
                 |
                 |list_prepend(list, x) {
                 |    var node;
                 |
                 |    node = alloc {v: x, prev: null, next: list};
                 |    if (list == null) {
                 |    } else {
                 |        (*list).prev = node;
                 |    }
                 |
                 |    return node;
                 |}
                 |
                 |read_code() {
                 |    var x, continue, code, first;
                 |    continue = 1;
                 |    code = null;
                 |    first = null;
                 |
                 |    while (continue) {
                 |        x = input;
                 |        // EOI
                 |        if (x == -1) {
                 |            continue = 0;
                 |        } else {
                 |            code = list_append(code, x);
                 |            if (first == null) {
                 |                first = code;
                 |            }
                 |        }
                 |    }
                 |
                 |    return first;
                 |}
                 |
                 |create_memory(size) {
                 |    var mem;
                 |    mem = null;
                 |
                 |    while(size > 0) {
                 |        mem = list_prepend(mem, 0);
                 |        size = size - 1;
                 |    }
                 |
                 |    return mem;
                 |}
                 |
                 |jump(code) {
                 |    var c, continue, direction, c_inc, c_dec;
                 |    c = 0;
                 |    continue = 1;
                 |
                 |    // '[' -> jumping right
                 |    if ((*code).v == 91) {
                 |        direction = 1;
                 |        c_inc = 91;
                 |        c_dec = 93;
                 |    } else {
                 |        // ']' <- jumping left
                 |        if ((*code).v == 93) {
                 |            direction = 0;
                 |            c_inc = 93;
                 |            c_dec = 91;
                 |        }
                 |    }
                 |
                 |    while (continue) {
                 |        if (code == null) {
                 |            continue = 0;
                 |        } else {
                 |            if ((*code).v == c_inc) {
                 |                c = c + 1;
                 |            } else {
                 |                if ((*code).v == c_dec) {
                 |                    c = c - 1;
                 |                }
                 |            }
                 |
                 |            if (c == 0) {
                 |                continue = 0;
                 |            } else {
                 |                if (direction == 1) {
                 |                    code = (*code).next;
                 |                } else {
                 |                    code = (*code).prev;
                 |                }
                 |            }
                 |        }
                 |    }
                 |
                 |    return code;
                 |}
                 |
                 |run(code, mem) {
                 |    var continue, status, inst, inst_code, next_inst;
                 |    status = 0;
                 |
                 |    if (code == null) {
                 |        continue = 0;
                 |    } else {
                 |        continue = 1;
                 |        next_inst = code;
                 |    }
                 |
                 |    while (continue) {
                 |        if (next_inst == null) {
                 |            continue = 0;
                 |        } else {
                 |            // get the current instruction
                 |            inst_code = (*next_inst).v;
                 |            inst = next_inst;
                 |            next_inst = null;
                 |
                 |            // '>' move the pointer to the right
                 |            if (inst_code == 62) {
                 |                mem = (*mem).next;
                 |            } else {
                 |                // '<' move the pointer to the left
                 |                if (inst_code == 60) {
                 |                    mem = (*mem).prev;
                 |                } else {
                 |                    // '+' increment the memory cell at the pointer
                 |                    if (inst_code == 43) {
                 |                        (*mem).v = (*mem).v + 1;
                 |                    } else {
                 |                        // '-' decrement the memory cell at the pointer
                 |                        if (inst_code == 45) {
                 |                            (*mem).v = (*mem).v - 1;
                 |                        } else {
                 |                            // '.' output the character signified by the cell at the pointer
                 |                            if (inst_code == 46) {
                 |                                output (*mem).v;
                 |                            } else {
                 |                                // ',' input a character and store it in the cell at the pointer
                 |                                if (inst_code == 44) {
                 |                                    (*mem).v = input;
                 |                                } else {
                 |                                    // '[' jump past the matching ']' if the cell at the pointer is 0
                 |                                    if (inst_code == 91) {
                 |                                        if ((*mem).v == 0) {
                 |                                            next_inst = jump(inst);
                 |                                        }
                 |                                    } else {
                 |                                        // ']' jump back to the matching '[' if the cell at the pointer is nonzero
                 |                                        if (inst_code == 93) {
                 |                                            if ((*mem).v == 0) {
                 |                                                // do nothing
                 |                                            } else {
                 |                                                next_inst = jump(inst);
                 |                                            }
                 |                                        } else {
                 |                                            // ignore anything else
                 |                                        }
                 |                                    }
                 |                                }
                 |                            }
                 |                        }
                 |                    }
                 |                }
                 |            }
                 |            if (next_inst == null) {
                 |                next_inst = (*inst).next;
                 |            }
                 |        }
                 |    }
                 |
                 |    return status;
                 |}
                 |
                 |main() {
                 |    var code, mem;
                 |    code = read_code();
                 |    mem = create_memory(30000);
                 |    return run(code, mem);
                 |}
                 |
                 |""".stripMargin

  val bfCodeNoWhile = """
                        |list_append(list, x) {
                        |    var node;
                        |
                        |    node = alloc {v: x, prev: list, next: null};
                        |    if (list == null) {
                        |    } else {
                        |        (*list).next = node;
                        |    }
                        |
                        |    return node;
                        |}
                        |
                        |list_prepend(list, x) {
                        |    var node;
                        |
                        |    node = alloc {v: x, prev: null, next: list};
                        |    if (list == null) {
                        |    } else {
                        |        (*list).prev = node;
                        |    }
                        |
                        |    return node;
                        |}
                        |
                        |read_code() {
                        |    var x, continue, code, first;
                        |    continue = 1;
                        |    code = null;
                        |    first = null;
                        |
                        |    if (continue) {
                        |        x = input;
                        |        // EOI
                        |        if (x == -1) {
                        |            continue = 0;
                        |        } else {
                        |            code = list_append(code, x);
                        |            if (first == null) {
                        |                first = code;
                        |            }
                        |        }
                        |    }
                        |
                        |    return first;
                        |}
                        |
                        |create_memory(size) {
                        |    var mem;
                        |    mem = null;
                        |
                        |    if (size > 0) {
                        |        mem = list_prepend(mem, 0);
                        |        size = size - 1;
                        |    }
                        |
                        |    return mem;
                        |}
                        |
                        |jump(code) {
                        |    var c, continue, direction, c_inc, c_dec;
                        |    c = 0;
                        |    continue = 1;
                        |
                        |    // '[' -> jumping right
                        |    if ((*code).v == 91) {
                        |        direction = 1;
                        |        c_inc = 91;
                        |        c_dec = 93;
                        |    } else {
                        |        // ']' <- jumping left
                        |        if ((*code).v == 93) {
                        |            direction = 0;
                        |            c_inc = 93;
                        |            c_dec = 91;
                        |        }
                        |    }
                        |
                        |    if (continue) {
                        |        if (code == null) {
                        |            continue = 0;
                        |        } else {
                        |            if ((*code).v == c_inc) {
                        |                c = c + 1;
                        |            } else {
                        |                if ((*code).v == c_dec) {
                        |                    c = c - 1;
                        |                }
                        |            }
                        |
                        |            if (c == 0) {
                        |                continue = 0;
                        |            } else {
                        |                if (direction == 1) {
                        |                    code = (*code).next;
                        |                } else {
                        |                    code = (*code).prev;
                        |                }
                        |            }
                        |        }
                        |    }
                        |
                        |    return code;
                        |}
                        |
                        |run(code, mem) {
                        |    var continue, status, inst, inst_code, next_inst;
                        |    status = 0;
                        |
                        |    if (code == null) {
                        |        continue = 0;
                        |    } else {
                        |        continue = 1;
                        |        next_inst = code;
                        |    }
                        |
                        |    if (continue) {
                        |        if (next_inst == null) {
                        |            continue = 0;
                        |        } else {
                        |            // get the current instruction
                        |            inst_code = (*next_inst).v;
                        |            inst = next_inst;
                        |            next_inst = null;
                        |
                        |            // '>' move the pointer to the right
                        |            if (inst_code == 62) {
                        |                mem = (*mem).next;
                        |            } else {
                        |                // '<' move the pointer to the left
                        |                if (inst_code == 60) {
                        |                    mem = (*mem).prev;
                        |                } else {
                        |                    // '+' increment the memory cell at the pointer
                        |                    if (inst_code == 43) {
                        |                        (*mem).v = (*mem).v + 1;
                        |                    } else {
                        |                        // '-' decrement the memory cell at the pointer
                        |                        if (inst_code == 45) {
                        |                            (*mem).v = (*mem).v - 1;
                        |                        } else {
                        |                            // '.' output the character signified by the cell at the pointer
                        |                            if (inst_code == 46) {
                        |                                output (*mem).v;
                        |                            } else {
                        |                                // ',' input a character and store it in the cell at the pointer
                        |                                if (inst_code == 44) {
                        |                                    (*mem).v = input;
                        |                                } else {
                        |                                    // '[' jump past the matching ']' if the cell at the pointer is 0
                        |                                    if (inst_code == 91) {
                        |                                        if ((*mem).v == 0) {
                        |                                            next_inst = jump(inst);
                        |                                        }
                        |                                    } else {
                        |                                        // ']' jump back to the matching '[' if the cell at the pointer is nonzero
                        |                                        if (inst_code == 93) {
                        |                                            if ((*mem).v == 0) {
                        |                                                // do nothing
                        |                                            } else {
                        |                                                next_inst = jump(inst);
                        |                                            }
                        |                                        } else {
                        |                                            // ignore anything else
                        |                                        }
                        |                                    }
                        |                                }
                        |                            }
                        |                        }
                        |                    }
                        |                }
                        |            }
                        |            if (next_inst == null) {
                        |                next_inst = (*inst).next;
                        |            }
                        |        }
                        |    }
                        |
                        |    return status;
                        |}
                        |
                        |main() {
                        |    var code, mem;
                        |    code = read_code();
                        |    mem = create_memory(30000);
                        |    return run(code, mem);
                        |}
                        |
                        |""".stripMargin




  test("bf if instead of while") {
    val code = bfCodeNoWhile
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    executor.run()
  }

  test("bf if instead of while coverage search") {
    val code = bfCodeNoWhile
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val covered = Some(mutable.HashSet[CfgNode]())
    val executor = new SymbolicExecutor(cfg, searchStrategy = new CoverageSearchStrategy(covered.get), covered = covered)
    executor.run()
  }

  test("bf if instead of while random path search") {
    val code = bfCodeNoWhile
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val covered = Some(mutable.HashSet[CfgNode]())
    val stateHistory = new ExecutionTree()
    val executor = new SymbolicExecutor(cfg, executionTree = Some(stateHistory), searchStrategy = new TreeBasedStrategy(stateHistory), covered = covered)
    executor.run()
  }


  test("bf if instead of while klee search") {
    val code = bfCodeNoWhile
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val covered = Some(mutable.HashSet[CfgNode]())
    val stateHistory = new ExecutionTree()
    val executor = new SymbolicExecutor(cfg, executionTree = Some(stateHistory), searchStrategy = new KleeSearchStrategy(stateHistory, covered.get), covered = covered)
    executor.run()
  }

  test("bf if instead of while subsumption") {
    val code = bfCodeNoWhile
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx))))
    executor.run()
  }

  test("bf if instead of while merging") {
    val code = bfCodeNoWhile
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg, None, searchStrategy = new AggressiveStateMerging(new BFSSearchStrategy))
    executor.run()
  }

  test("bf if instead of while smart merging") {
    val code = bfCodeNoWhile
    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
    val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
    for (node <- analysesResult) {
      val nodeCosts = new mutable.HashMap[String, Double]
      for (cost <- node._2) {
        nodeCosts.put(cost._1.name, cost._2)
      }
      variableCosts.put(node._1, nodeCosts)
    }
    val executor = new SymbolicExecutor(cfg, None, searchStrategy = new HeuristicBasedStateMerging(new BFSSearchStrategy, variableCosts, 3))
    executor.run()
  }


  test("bf if instead of while dynamic smart merging") {
    val code = bfCodeNoWhile
    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val analysesResult = new QueryCountAnalyses(cfg)(new SemanticAnalysis().analyze(program)).analyze()
    val variableCosts = new mutable.HashMap[CfgNode, mutable.HashMap[String, Double]]
    for (node <- analysesResult) {
      val nodeCosts = new mutable.HashMap[String, Double]
      for (cost <- node._2) {
        nodeCosts.put(cost._1.name, cost._2)
      }
      variableCosts.put(node._1, nodeCosts)
    }
    val limitCost = 3.0
    val depth = 3
    val stateHistory = new ExecutionTree()
    val dynamicStateMerging = new DynamicStateMerging(
      new HeuristicBasedStateMerging(new BFSSearchStrategy, variableCosts, limitCost),
      stateHistory,
      variableCosts,
      limitCost,
      depth
    )
    val executor = new SymbolicExecutor(cfg, None, searchStrategy = dynamicStateMerging)
    executor.run()
  }


  test("bf if instead of while smart merging 2") {
    val code = bfCodeNoWhile
    val program = parseUnsafe(code)
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    val tmp = new RecursionBasedAnalyses()(new SemanticAnalysis().analyze(program))
    tmp.compute(cfg)
    val executor = new SymbolicExecutor(cfg, None, searchStrategy = new HeuristicBasedStateMerging(new BFSSearchStrategy, tmp.mapping, 3))
    executor.run()
  }



}

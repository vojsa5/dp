package microc.symbolic_execution

import com.microsoft.z3.Context
import microc.ast.{CodeLoc, NestedBlockStmt, Number, WhileStmt}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class SymbolicExecutorTest extends FunSuite with MicrocSupport with Examples {

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

  val bfCodeNoVal = """
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


  test("possible error") {
    val code =
      """
        |main() {
        |  var x;
        |  x = input;
        |  return 1/x;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }

//  test("infinite paths") {
//    val code =
//      """
//        |main() {
//        |  var y;
//        |  y = input;
//        |  while (y > 0) {
//        |   y = y - 1;
//        |  }
//        |  return 0;
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new SymbolicExecutor(cfg);
//    try {
//      executor.run()
//      fail("Expected a StackOverflowError but it did not occur.")
//    }
//    catch {
//      case _: StackOverflowError =>
//      case other: Throwable => fail("Expected a StackOverflowError, but caught different exception: " + other)
//    }
//
//    null
//  }
//
//
//  test("infinite paths 2") {
//    val code =
//      """
//        |main() {
//        |  var y;
//        |  y = input;
//        |  y = y + 1;
//        |  while (y > 0) {
//        |   y = y - 1;
//        |  }
//        |  return 0;
//        |}
//        |""".stripMargin;
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new SymbolicExecutor(cfg);
//    try {
//      executor.run()
//      fail("Expected a StackOverflowError but it did not occur.")
//    }
//    catch {
//      case _: StackOverflowError =>
//      case other: Throwable => fail("Expected a StackOverflowError, but caught different exception: " + other)
//    }
//
//    null
//  }


  test("survey test") {
    val code =
      """
        |foobar(a, b) {
        |  var x, y;
        |  x = 1;
        |  y = 0;
        |  if (a != 0) {
        |   y = 3 + x;
        |   if (b == 0) {
        |     x = 2 * (a + b);
        |   }
        |  }
        |  return 1 / (x - y);
        |}
        |
        |main() {
        |  var y, x;
        |  y = input;
        |  x = input;
        |  x = foobar(x, y);
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }

  test("my5") {
    val code =
      """
        |main() {
        |  var y, x;
        |  y = 4;
        |  x = 0;
        |  while (y > 0) {
        |   y = y - 1;
        |   x = x + 1;
        |  }
        |  output x;
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

  test("error as nullptr dereference") {
    val code =
      """
        |main() {
        |  var y, x, a, b;
        |  a = input;
        |  y = input;
        |  if (a) {
        |   x = &y;
        |  }
        |  else {
        |   x = null;
        |  }
        |  return *x;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }


  test("error as use of uninitialized value") {
    val code =
      """
        |main() {
        |  var y, x, a, b;
        |  a = input;
        |  y = input;
        |  if (a) {
        |   x = &y;
        |  }
        |  else {
        |   x = null;
        |  }
        |  return *x;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }


  test("error as use of uninitialized value") {
    val code =
      """
        |main() {
        |  var y, a;
        |  a = [1, 2, 3];
        |  y = input;
        |  return a[y];
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }


  test("dfs strategy") {
    val code =
      """
        |main() {
        |  var y, x;
        |  y = 4;
        |  x = 0;
        |  while (y > 0) {
        |   y = y - 1;
        |   x = x + 1;
        |  }
        |  output x;
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg, searchStrategy = new DFSSearchStrategy());
    executor.run()
    null
  }


  test("random strategy") {
    val code =
      """
        |main() {
        |  var y, x;
        |  y = 4;
        |  x = 0;
        |  while (y > 0) {
        |   y = y - 1;
        |   x = x + 1;
        |  }
        |  output x;
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg, searchStrategy = new RandomSearchStrategy());
    executor.run()
    null
  }

  test("error does not happen") {
    val code =
      """
        |main() {
        |  var y,z;
        |  z = 0;
        |  y = 1;
        |  if (z == 0) {
        |   y = 2;
        |  }
        |  else {
        |   y = 3 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

  test("error in second path") {
    val code =
      """
        |main() {
        |  var y,z;
        |  z = input;
        |  y = 1;
        |  if (z == 0) {
        |   y = 2;
        |  }
        |  else {
        |   y = 3 / 0;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
    null
  }


  test("nested unreachable error") {
    val code =
      """
        |main() {
        |  var y,z;
        |  z = input;
        |  y = 1;
        |  if (z == 0) {
        |   y = 2;
        |  }
        |  else {
        |   y = 3 / z;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

  test("my2") {
    val code =
      """
        |main() {
        |  var x,y,z,a,b;
        |  a = 1;
        |  b = 2;
        |  z = a+b;
        |  y = a*b;
        |  while (y > a+b) {
        |    a = a+1;
        |    x = a+b;
        |  }
        |  return 0;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

  test("bf if instead of while") {
    val code = bfCodeNoVal
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    executor.run()
  }

  test("bf if instead of while subsumption") {
    val code = bfCodeNoVal
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)))
    executor.run()
  }

  test("bf if instead of while merging") {
    val code = bfCodeNoVal
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg, None, searchStrategy = new AgressiveStateMerging(new BFSSearchStrategy))
    executor.run()
  }

  test("bf if instead of while merging subsumption") {
    val code = bfCodeNoVal
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), searchStrategy = new AgressiveStateMerging(new BFSSearchStrategy))
    executor.run()
  }

//  test("bf") {
//    val code = bfCode
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new SymbolicExecutor(cfg)
//    executor.run()
//  }

  test("bf with subsumption") {
    val code = bfCode
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)))
    executor.run()
  }

//  test("bf with merging") {
//    val code = bfCode
//    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
//    val executor = new SymbolicExecutor(cfg, None, searchStrategy = new AgressiveStateMerging(new BFSSearchStrategy))
//    executor.run()
//  }

  test("bf with merging and subsumption") {
    val code = bfCode
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new SymbolicExecutor(cfg, Some(new PathSubsumption(new ConstraintSolver(ctx), ctx)), searchStrategy = new AgressiveStateMerging(new BFSSearchStrategy))
    executor.run()
  }




  test("sequential unbounded loop finishes with summarization correctly") {
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

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new LoopSummary(cfg)
    executor.run()
  }


  test("simple sequential summarization is correct") {

    var code =
      """
        |main() {
        |  var i, m;
        |  i = 0;
        |  m = input;
        |  if (m <= 0) {
        |   m = 1;
        |  }
        |  while (i < m) {
        |   i = i + 1;
        |  }
        |  return 1 / (i - m - 1);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    executor.run()


    code =
      """
        |main() {
        |  var i, m;
        |  i = 0;
        |  m = input;
        |  if (m <= 0) {
        |   m = 1;
        |  }
        |  while (i < m) {
        |   i = i + 1;
        |  }
        |  return 1 / (i - m);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }


    code =
      """
        |main() {
        |  var i, m;
        |  i = 0;
        |  m = input;
        |  if (m <= 0) {
        |   m = 1;
        |  }
        |  while (i < m) {
        |   i = i + 1;
        |  }
        |  return 1 / (i - m + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    executor.run()
  }

  test("sequential unbounded periodic loop finishes with summarization correctly") {
    var code =
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

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var ctx = new Context()
    var executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }

    code =
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
        |  return 1 / (x - n);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    ctx = new Context()
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("sequential unbounded periodic loop finishes with summarization correctly 2") {
    var code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  if (x >= n) {
        |   x = n - 1;
        |  }
        |  if (z >= n) {
        |   z = n - 1;
        |  }
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z - 1);
        |}
        |""".stripMargin;

    var cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    var executor = new LoopSummary(cfg)
    executor.run()


    code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  if (x >= n) {
        |   x = n - 1;
        |  }
        |  if (z >= n) {
        |   z = n - 1;
        |  }
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

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }


    code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  if (x >= n) {
        |   x = n - 1;
        |  }
        |  if (z >= n) {
        |   z = n - 1;
        |  }
        |  while (x < n) {
        |   if (z > x) {
        |     x = x + 1;
        |   }
        |   else {
        |     z = z + 1;
        |   }
        |  }
        |  return 1 / (x - z + 1);
        |}
        |""".stripMargin;

    cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    executor = new LoopSummary(cfg)
    executor.run()
  }


}

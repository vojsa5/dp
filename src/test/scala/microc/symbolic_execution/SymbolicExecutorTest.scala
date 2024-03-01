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

  test("multi functional") {
    val code =
      """
        |
        |fce(n) {
        |  while (n == 0) {
        |     n = 1 / 0;
        |  }
        |  return n + 2;
        |}
        |
        |main() {
        |  var a,b;
        |  b = 5;
        |  a = fce(b);
        |  return a;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }

  test("factorial") {
    val code =
      """
        |
        |fac(n) {
        |    var f;
        |
        |    if (n == 0) {
        |      f = 1;
        |    } else {
        |      f = n * fac(n - 1);
        |    }
        |
        |    return f;
        |}
        |
        |
        |main() {
        |  var a,b;
        |  b = 5;
        |  a = fac(b);
        |  output(a);
        |  return a;
        |}
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    executor.run()
    null
  }


  test("paths must finish main") {
    val code =
      """
        | foo(n) {
        |   var r;
        |   if (n == 1) {
        |     r = 1;
        |   }
        |   else {
        |     r = 0;
        |   }
        |   return r;
        | }
        |
        | main() {
        |   var x;
        |   x = input;
        |   x = 1 / foo(x);
        |   return x;
        | }
        |
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

  // valid programs without any input
  test("return 42") {
    val code =
      """
        | main() {
        |   return 42;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("basic-expressions") {
    val code =
      """
        | main() {
        |   return 1932/2/23;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("function-call-1") {
    val code =
      """
        | f(z) {
        |   return z + 1;
        | }
        |
        | main() {
        |   return f(f(2) + f(3));
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 8)
    null
  }

  test("direct assign") {
    val code =
      """
        | main() {
        |   var x, y;
        |   x = 21;
        |   y = x + 21;
        |   return y;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }


  test("indirect assign") {
    val code =
      """
        | main() {
        |   var x, y;
        |   x = 1;
        |   y = &x;
        |   *y = 42;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    val t = executor.run()
    assert(t == 42)
    null
  }

  test("basic recursion") {
    val code =
      """
        | f(n) {
        |  var r;
        |
        |  if (n == 0) {
        |    r = 1;
        |  } else {
        |    r = n * f(n - 1);
        |  }
        |  return r;
        |}
        |
        | main() {
        |   return f(5);
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 120)
    null
  }

  test("return var") {
    val code =
      """
        | main() {
        |  var x;
        |  x = 42;
        |  return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("return expr") {
    val code =
      """
        | main() {
        |  var x, y;
        |  x = 43;
        |  y = 1;
        |  return x-y;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("return comparison") {
    val code =
      """
        | main() {
        |  var x, y;
        |  x = 1;
        |  y = 1;
        |  return x == y;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 1)
    null
  }

  test("pointer-cmp-1") {
    val code =
      """
        | main() {
        |  var x;
        |  x = null;
        |  return x == null;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 1)
    null
  }

  test("pointer-cmp-2") {
    val code =
      """
        | main() {
        |  var x;
        |  x = alloc null;
        |  return *x == null;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 1)
    null
  }

  test("pointer-cmp-3") {
    val code =
      """
        | main() {
        |  var x, y;
        |  x = alloc null;
        |  y = x;
        |  return x == y;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 1)
    null
  }

  test("nested-blocks") {
    val code =
      """
        | main() {
        |   var x;
        |   x = 1;
        |   {
        |     x = x + 41;
        |   }
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("deref") {
    val code =
      """
        | main() {
        |   var x;
        |   x = alloc 1;
        |   *x = 42;
        |   return *x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("deref-null") {
    val code =
      """
        | main() {
        |   var x;
        |   x = null;
        |   *x = 42;
        |   return *x;
        | }
        |
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

  test("basic-pointer") {
    val code =
      """
        | main() {
        |   var x, y;
        |   x = 43;
        |   y = &x;
        |   *y = *y - 1;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("doubler-pointer") {
    val code =
      """
        | main() {
        |   var x, y, z;
        |   x = 43;
        |   y = &x;
        |   z = &y;
        |   **z = *y - 1;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg);
    assert(executor.run() == 42)
    null
  }

  test("ret-non-int-from-main") {
    val code =
      """
        |  main() {
        |   var x;
        |   x = 1;
        |   return &x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
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

  test("uninitialized-1") {
    val code =
      """
        |  main() {
        |   var x;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
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

  test("uninitialized-2") {
    val code =
      """
        | main() {
        |   var x;
        |   *x = 1;
        |   return x;
        | }
        |
        |""".stripMargin;
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
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

  test("array") {
    val code =
      """
        | main() {
        |   var a, b;
        |   a = [1,2];
        |   b = a[a[0]];
        |   a[a[0]-1] = 40;
        |   return b + a[0];
        | }
        |""".stripMargin
    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }

  test("array out of bounds") {
    val code =
      """
        | main() {
        |   var a;
        |   a = [1,2];
        |   a[2] = 1;
        |   return 0;
        | }
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }

  test("array out of bounds 2") {
    val code =
      """
        | main() {
        |   var a, b;
        |   a = [1,2];
        |   b = -1;
        |   a[b] = 1;
        |   return 0;
        | }
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }

  test("array store exception") {
    val code =
      """
        | main() {
        |   var a;
        |   a = [1, main];
        |   return 0;
        | }
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }

  test("array definition semantics") {
    val code =
      """
        | inf() {
        |   return inf();
        | }
        | main() {
        |   var a;
        |   a = [1, main, inf()];
        |   return 0;
        | }
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("non-array access") {
    val code =
      """
        | inf() {
        |   return inf();
        | }
        | main() {
        |   var a;
        |   a = 1;
        |   return a[inf()];
        | }
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }

  test("array wih multiple dimensions") {
    val code =
      """
        | main() {
        |   var a, b;
        |   a = [[0,1],[2,3,4]];
        |   b = a[0];
        |   b[1] = b[1] + 1;
        |   a[1][2] = a[1][0] * 2 * 10;
        |   return a[0][1] + a[1][2];
        | }
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }


  test("basic records") {
    val code =
      """
        |  main() {
        |   var r;
        |   r = { x: 1, y: 41};
        |   return r.x + r.y;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }

  test("missing field") {
    val code =
      """
        | main() {
        |   var r;
        |   r = { x: 1 };
        |   r.y = 42;
        |   return r.x;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("non-record-access") {
    val code =
      """
        | main() {
        |   var r;
        |   r = 1;
        |   return r.x;
        | }
        |
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("non-pointer-access") {
    val code =
      """
        | main() {
        |   var r;
        |   r = 1;
        |   (*r).x = 41;
        |   return r.x;
        | }
        |
        |
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("direct-field-assign") {
    val code =
      """
        | main() {
        |   var r;
        |   r = { x: 1 };
        |   r.x = 42;
        |   return r.x;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }


  test("indirect-field-assign") {
    val code =
      """
        | main() {
        |   var r, s, t;
        |   r = { x: 1 };
        |   s = &r;
        |   t = &s;
        |   (**t).x = 42;
        |   return r.x;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }

  test("nested records") {
    val code =
      """
        | main() {
        |   var r, s;
        |   r = { a: 1 };
        |   s = { a: &r, b: 2 };
        |   (*(s.a)).a = 40 + s.b;
        |   return r.a;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }


  test("missing fields") {
    val code =
      """
        | main() {
        |   var r;
        |   r = { a: 1 };
        |   r.b = 1;
        |   return r.b;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("no-nested-records") {
    val code =
      """
        | main() {
        |   var r1, r2;
        |   r1 = { a: 1 };
        |   r2 = { a: 1, b: r1 };
        |   return 0;
        | }
        |
        |""".stripMargin


    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    try {
      executor.run()
      fail("Expected a ExecutionException but it did not occur.")
    }
    catch {
      case _: ExecutionException =>
      case other: Throwable => fail("Expected a ExecutionException, but caught different exception: " + other)
    }
  }


  test("assign to records") {
    val code =
      """
        | main() {
        |   var r,s;
        |   r = { a: null, b: null };
        |   s = { c: 1 };
        |   r.a = &s;
        |   r.b = &s;
        |   s.c = 2;
        |   return (*(r.a)).c + (*(r.b)).c;
        | }
        |
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 4)
  }


  test("records-copy-1") {
    val code =
      """
        |main() {
        |   var a,b;
        |   a = { n:1 };
        |   b = a;
        |   b.n = 2;
        |   output a.n;
        |   output b.n;
        |   return 0;
        | }
        |
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }


  test("records-copy-2") {
    val code =
      """
        |main() {
        |   var a,b,c,d;
        |   a = { n:1 };
        |   b = { m: &a };
        |   c = b;
        |   d = a;
        |   d.n = 2;
        |   (*b.m).n = 3;
        |   (*c.m).n = 4;
        |   output a.n;
        |   output (*b.m).n;
        |   output (*c.m).n;
        |   output d.n;
        |   return 0;
        | }
        |
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
  }


  test("records-with-functions") {
    val code =
      """
        | inc(s) {
        |   (*s).c = (*s).c + 1;
        |   return *s;
        | }
        |
        | new() {
        |   return { c: 0, inc: inc };
        | }
        |
        | main() {
        |   var c, p;
        |   c = new();
        |   p = &c;
        |   return ((((c.inc)(p)).inc)(p)).c;
        | }
        |
        |""".stripMargin

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val executor = new SymbolicExecutor(cfg)
    assert(executor.run() == 42)
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
    val ctx = new Context()
    val executor = new LoopSummary(cfg)
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
    val code =
      """
        |main() {
        |  var n, x, z;
        |  n = input;
        |  x = input;
        |  z = input;
        |  if (x >= n) {
        |   x = n - 5;
        |  }
        |  if (z >= n) {
        |   z = n - 5;
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

    val cfg = new IntraproceduralCfgFactory().fromProgram(parseUnsafe(code));
    val ctx = new Context()
    val executor = new LoopSummary(cfg)
    executor.run()
  }


}

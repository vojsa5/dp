package microc.symbolic_execution

import microc.ast.{AssignStmt, FunDecl, IfStmt, VarStmt, WhileStmt}
import microc.cfg.{CfgNode, IntraproceduralCfgFactory}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class CFGfactoryTest extends FunSuite with MicrocSupport with Examples {

  test("get all paths in a sequential loop") {//TODO this is the normalized version
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
    val program = parseUnsafe(code);
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    assert(stmt.pred.size == 0)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[FunDecl])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[VarStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[VarStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 2)
    assert(stmt.succ.size == 2)
    assert(stmt.ast.isInstanceOf[WhileStmt])
    val whileStmt = stmt
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 2)
    assert(stmt.ast.isInstanceOf[IfStmt])
    stmt = stmt.succ.head
    null
  }


  test("test empty block") {//TODO this is the normalized version
    val code =
    """
      |main() {
      |  var x, z;
      |  x = input;
      |  z = input;
      |  if (z > x) {
      |
      |  }
      |  else {
      |    z = z + 1;
      |  }
      |  if (z > x) {
      |    z = z + 2;
      |  }
      |  else {
      |
      |  }
      |  return 1 / (x - z);
      |}
      |""".stripMargin;
    val program = parseUnsafe(code);
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    assert(stmt.pred.size == 0)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[FunDecl])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[VarStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[VarStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 2)
    assert(stmt.ast.isInstanceOf[IfStmt])
    stmt = stmt.succ.head
    null
  }


  test("if") {
    val code =
      """
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
        |
        |
        |main() {
        |    var x, continue, code, first;
        |    continue = 1;
        |    code = null;
        |    first = null;
        |
        |    if (x == -1) {
        |        continue = 0;
        |    }
        |    else {
        |        code = list_append(code, x);
        |        if (first == null) {
        |            first = code;
        |        }
        |    }
        |
        |    return first;
        |}
        |
        |""".stripMargin;

    val program = parseUnsafe(code);
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    assert(stmt.pred.size == 0)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[FunDecl])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[VarStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[VarStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 1)
    assert(stmt.ast.isInstanceOf[AssignStmt])
    stmt = stmt.succ.head
    assert(stmt.pred.size == 1)
    assert(stmt.succ.size == 2)
    assert(stmt.ast.isInstanceOf[IfStmt])
    null
  }


  test("if in while") {
    val code =
      """
        |
        |main() {
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
        |            code = null;
        |            if (first == null) {
        |                first = code;
        |            }
        |        }
        |    }
        |
        |    return first;
        |}
        |
        |""".stripMargin;

    val program = parseUnsafe(code);
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    null
  }


  test("if if") {
    val code =
      """
        |
        |main() {
        |   var res;
        |   if (input) {
        |      if (input) {
        |         res = 2;
        |      }
        |      else {
        |         res = 3;
        |      }
        |   }
        |   else {
        |     if (input) {
        |         res = 4;
        |      }
        |      else {
        |         res = 5;
        |      }
        |   }
        |
        |    return res;
        |}
        |
        |""".stripMargin;

    val program = parseUnsafe(code);
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    null
  }


  test("if if if") {
    val code =
      """
        |
        |main() {
        |   var res;
        |   if (input) {
        |      if (input) {
        |         if (input) {
        |           res = 1;
        |         }
        |         else {
        |           res = 2;
        |         }
        |      }
        |      else {
        |         res = 3;
        |      }
        |   }
        |   else {
        |     res = 4;
        |   }
        |
        |    return res;
        |}
        |
        |""".stripMargin;

    val program = parseUnsafe(code);
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    null
  }


  test("while while") {
    val code =
      """
        |
        |main() {
        |   var res;
        |   while (input) {
        |     while (input) {
        |       res = 1;
        |     }
        |   }
        |
        |    return res;
        |}
        |
        |""".stripMargin;

    val program = parseUnsafe(code);
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    null
  }

  test("while if") {
    val code =
      """
        |
        |main() {
        |   var res;
        |   while (input) {
        |      if (input) {
        |         res = 1;
        |      }
        |      else {
        |         res = 3;
        |      }
        |   }
        |
        |    return res;
        |}
        |
        |""".stripMargin;

    val program = parseUnsafe(code);
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    null
  }


  test("while if while") {
    val code =
      """
        |
        |main() {
        |   var res;
        |   while (input) {
        |      if (input) {
        |         while (input) {
        |           res = 1;
        |         }
        |      }
        |      else {
        |         res = 3;
        |      }
        |   }
        |
        |    return res;
        |}
        |
        |""".stripMargin;

    val program = parseUnsafe(code);
    val cfg = new IntraproceduralCfgFactory().fromProgram(program);
    var stmt: CfgNode = cfg.getFce("main")
    null
  }
}
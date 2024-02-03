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

}
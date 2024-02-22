package microc.symbolic_execution

import microc.ast.{BinaryOp, CodeLoc, GreaterThan, Identifier, Number, Plus}
import microc.symbolic_execution.Value.{IteVal, PointerVal, SymbolicExpr, SymbolicVal}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class SymbolicStoreTest extends FunSuite with MicrocSupport with Examples {
  test("test equals") {
    var store1 = new SymbolicStore(Map.empty)
    var store2 = new SymbolicStore(Map.empty)

    var ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    val y = SymbolicVal(CodeLoc(0, 0))
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(3))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(3))


    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    assert(store1.storeEquals(store2))
    assert(store2.storeEquals(store1))

    store1 = new SymbolicStore(Map.empty)
    store2 = new SymbolicStore(Map.empty)

    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(3))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(2, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(3))

    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    assert(!store1.storeEquals(store2))
    assert(!store2.storeEquals(store1))

    store1 = new SymbolicStore(Map.empty)
    store2 = new SymbolicStore(Map.empty)

    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(3))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, SymbolicVal(CodeLoc(0, 0)))

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(3))

    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    assert(!store1.storeEquals(store2))
    assert(!store2.storeEquals(store1))

    store1 = new SymbolicStore(Map.empty)
    store2 = new SymbolicStore(Map.empty)

    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(3))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(4))

    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    assert(!store1.storeEquals(store2))
    assert(!store2.storeEquals(store1))

    store1 = new SymbolicStore(Map.empty)
    store2 = new SymbolicStore(Map.empty)

    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(3))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(3))

    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    assert(!store1.storeEquals(store2))
    assert(!store2.storeEquals(store1))

    store1 = new SymbolicStore(Map.empty)
    store2 = new SymbolicStore(Map.empty)

    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(3))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(3))

    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(3, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    assert(!store1.storeEquals(store2))
    assert(!store2.storeEquals(store1))



    store1 = new SymbolicStore(Map.empty)
    store2 = new SymbolicStore(Map.empty)

    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(3))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(3))

    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    assert(!store1.storeEquals(store2))
    assert(!store2.storeEquals(store1))

  }



}

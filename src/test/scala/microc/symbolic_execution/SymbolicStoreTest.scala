package microc.symbolic_execution

import microc.ast.{BinaryOp, CodeLoc, GreaterThan, Identifier, Number, Plus}
import microc.symbolic_execution.Value.{IteVal, PointerVal, SymbolicExpr, SymbolicVal, UninitializedRef}
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class SymbolicStoreTest extends FunSuite with MicrocSupport with Examples {
  test("test equals") {//TODO split tests
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
    store1.updateRef(ptr, PointerVal(1))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(1))


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
    store1.updateRef(ptr, PointerVal(1))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(2, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(1))

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
    store1.updateRef(ptr, PointerVal(1))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, SymbolicVal(CodeLoc(0, 0)))

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(1))

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
    store1.updateRef(ptr, PointerVal(1))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(2))

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
    store1.updateRef(ptr, PointerVal(1))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(1))

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
    store1.updateRef(ptr, PointerVal(1))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(1))

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
    store1.updateRef(ptr, PointerVal(1))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(1))

    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    assert(!store1.storeEquals(store2))
    assert(!store2.storeEquals(store1))

  }

  test("frames equals") {
    var store1 = new SymbolicStore(Map.empty)
    var store2 = new SymbolicStore(Map.empty)
    store1.pushFrame()

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

    assert(!store1.storeEquals(store2))
    assert(!store2.storeEquals(store1))
  }


  test("merge stores") {
    var store1 = new SymbolicStore(Map.empty)
    var store2 = new SymbolicStore(Map.empty)

    var ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    var y = SymbolicVal(CodeLoc(0, 0))
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(2))

    ptr = store1.addNewVar("w2")
    store1.updateRef(ptr, PointerVal(2))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(2))

    ptr = store2.addNewVar("w2")
    store2.updateRef(ptr, PointerVal(2))


    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    var mergedStoreOpt = store1.mergeStores(store2, new PathCondition(None, Number(1, CodeLoc(0, 0))))
    assert(mergedStoreOpt.nonEmpty)
    var mergedStore = mergedStoreOpt.get
    assert(mergedStore.storeEquals(store1))
    assert(mergedStore.storeEquals(store2))
    assert(store1.storeEquals(mergedStore))
    assert(store2.storeEquals(mergedStore))







    store1 = new SymbolicStore(Map.empty)
    store2 = new SymbolicStore(Map.empty)
    store1.pushFrame()
    store2.pushFrame()

    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    y = SymbolicVal(CodeLoc(0, 0))
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(1))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(1))


    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    mergedStoreOpt = store1.mergeStores(store2, new PathCondition(None, Number(1, CodeLoc(0, 0))))
    assert(mergedStoreOpt.nonEmpty)
    mergedStore = mergedStoreOpt.get
    assert(mergedStore.storeEquals(store1))
    assert(mergedStore.storeEquals(store2))
    assert(store1.storeEquals(mergedStore))
    assert(store2.storeEquals(mergedStore))


  }


  test("merge stores with pointers") {
    var store1 = new SymbolicStore(Map.empty)
    var store2 = new SymbolicStore(Map.empty)

    var ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("a")
    store1.updateRef(ptr, UninitializedRef)

    ptr = store1.addNewVar("b")
    store1.updateRef(ptr, UninitializedRef)

    ptr = store1.addNewVar("c")
    store1.updateRef(ptr, UninitializedRef)

    ptr = store1.addNewVar("y")
    var y = SymbolicVal(CodeLoc(0, 0))
    store1.updateRef(ptr, y)

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store1.addNewVar("w")
    store1.updateRef(ptr, PointerVal(2))

    ptr = store1.addNewVar("v")
    store1.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("a")
    store2.updateRef(ptr, UninitializedRef)

    ptr = store2.addNewVar("b")
    store2.updateRef(ptr, UninitializedRef)

    ptr = store2.addNewVar("c")
    store2.updateRef(ptr, UninitializedRef)

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, y)

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, SymbolicExpr(BinaryOp(Plus, y, Number(1, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    ptr = store2.addNewVar("w")
    store2.updateRef(ptr, PointerVal(2))

    ptr = store2.addNewVar("v")
    store2.updateRef(ptr, IteVal(Number(1, CodeLoc(0, 0)), Number(2, CodeLoc(0, 0)), BinaryOp(GreaterThan, Identifier("a", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0)))

    val mergedStoreOpt = store1.mergeStores(store2, new PathCondition(None, Number(1, CodeLoc(0, 0))))
    assert(mergedStoreOpt.nonEmpty)
    val mergedStore = mergedStoreOpt.get
    assert(mergedStore.storeEquals(store1))
    assert(mergedStore.storeEquals(store2))
    assert(store1.storeEquals(mergedStore))
    assert(store2.storeEquals(mergedStore))

  }

  test("merge stores with different pointers") {
    var store1 = new SymbolicStore(Map.empty)
    var store2 = new SymbolicStore(Map.empty)

    var ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))
    store1.popFrame()
    store1.pushFrame()
    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))
    store1.popFrame()
    store1.pushFrame()
    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("y")
    store1.updateRef(ptr, PointerVal(2))

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, PointerVal(3))

    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))
    store2.popFrame()
    store2.pushFrame()
    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))
    store2.popFrame()
    store2.pushFrame()
    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, PointerVal(2))

    val merged = store1.mergeStores(store2, new PathCondition(None, Number(1, CodeLoc(0, 0))))
    assert(!merged.get.getVal("x", CodeLoc(0, 0)).isInstanceOf[IteVal])
    assert(merged.get.getVal("y", CodeLoc(0, 0)).isInstanceOf[IteVal])
    assert(merged.get.getVal("z", CodeLoc(0, 0)).isInstanceOf[IteVal])
    null
  }


  test("merge stores same pointers remain same") {
    var store1 = new SymbolicStore(Map.empty)
    var store2 = new SymbolicStore(Map.empty)

    var ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))
    store1.popFrame()
    store1.pushFrame()
    ptr = store1.addNewVar("x")
    store1.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store1.addNewVar("a")
    store1.updateRef(ptr, PointerVal(1))

    ptr = store1.addNewVar("y")
    store1.updateRef(ptr, PointerVal(2))

    ptr = store1.addNewVar("z")
    store1.updateRef(ptr, PointerVal(2))


    ptr = store2.addNewVar("x")
    store2.updateRef(ptr, Number(1, CodeLoc(0, 0)))

    ptr = store2.addNewVar("a")
    store2.updateRef(ptr, PointerVal(0))

    ptr = store2.addNewVar("y")
    store2.updateRef(ptr, PointerVal(1))

    ptr = store2.addNewVar("z")
    store2.updateRef(ptr, PointerVal(1))

    val mergedStoreOpt = store1.mergeStores(store2, new PathCondition(None, Number(1, CodeLoc(0, 0))))
    assert(mergedStoreOpt.nonEmpty)
    val mergedStore = mergedStoreOpt.get
    assert(mergedStore.storeEquals(store1))
    assert(mergedStore.storeEquals(store2))
    assert(store1.storeEquals(mergedStore))
    assert(store2.storeEquals(mergedStore))

    assert(mergedStore.getVal("y", CodeLoc(0, 0)).equalsVal(mergedStore.getVal("z", CodeLoc(0, 0))))
    assert(mergedStore.getVal("z", CodeLoc(0, 0)).equalsVal(mergedStore.getVal("y", CodeLoc(0, 0))))
  }
}

package microc.symbolic_execution

import microc.ast.{CodeLoc, Identifier, Loc}
import microc.symbolic_execution.ExecutionException.{errorIncompatibleTypes, errorUninitializedReference}
import microc.symbolic_execution.Value.{FunVal, IteVal, NullRef, PointerVal, RefVal, SymbolicVal, UninitializedRef, Val}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class SymbolicStore(functionDeclarations: Map[String, FunVal]) {

  case class Storage() {
    var size: Int = 0

    var memory: ArrayBuffer[Val] = ArrayBuffer()

    def deepCopy(): Storage = {
      val newStorage = Storage()
      newStorage.size = this.size
      newStorage.memory = ArrayBuffer()
      for (v <- this.memory) {
        newStorage.memory += v
      }
      newStorage
    }

    def getAddress: PointerVal = {
      val res = PointerVal(size)
      size += 1
      memory += UninitializedRef
      res
    }

    def getVal(ptr: PointerVal, allowReturnNonInitialized: Boolean = false): Option[Val] = {
      if (memory.size <= ptr.address) {
        return None
      }
      memory(ptr.address) match {
        case UninitializedRef if allowReturnNonInitialized => Some(UninitializedRef)
        case UninitializedRef => None
        case v => Some(v)
      }
    }

    def addVal(ptr: PointerVal, v: Val): Unit = {
      memory(ptr.address) = v
    }

    def addNewVal(v: Val): PointerVal = {
      val addr = getAddress.address
      memory(addr) = v
      PointerVal(addr)
    }

    def deleteVal(ptr: PointerVal): Unit = {
      memory(ptr.address) = UninitializedRef
    }
  }

  var storage: Storage = Storage()

  private var frames: Array[Map[String, RefVal]] = Array(Map.empty)

  def pushFrame(): Unit = frames = frames.appended(Map.empty)

  def popFrame(): Unit = {
    for (value <- frames.last.values) {
      value match {
        case PointerVal(address) => storage.deleteVal(PointerVal(address))
      }
    }
    frames = frames.dropRight(1)
  }

  def framesCnt(): Int = {
    frames.length
  }

  def addVar(name: String, ref: RefVal): Unit = {
    val frame = frames.last
    frames = frames.dropRight(1)
    frames = frames.appended(frame.updated(name, ref))
  }

  def addNewVar(name: String): PointerVal = {
    val res = storage.getAddress
    val frame = frames.last
    frames = frames.dropRight(1)
    frames = frames.appended(frame.updated(name, res))
    res
  }

  def findVar(name: String): Option[RefVal] = {
    for (frame <- frames.reverse) {
      if (frame.contains(name)) {
        return Some(frame(name))
      }
    }
    None
  }

  def getValOfPtr(ptr: PointerVal, allowReturnNonInitialized: Boolean = false): Option[Val] = {
    storage.getVal(ptr, allowReturnNonInitialized)
  }

  def getVal(name: String, loc: Loc, allowReturnNonInitialized: Boolean = false): Val = {
    findVar(name) match {
      case Some(PointerVal(decl)) =>
        storage.getVal(PointerVal(decl)) match {
          case Some(res) => res
          case None if allowReturnNonInitialized => UninitializedRef
          case None =>
            throw errorUninitializedReference(loc)
        }
      case Some(NullRef) => throw errorUninitializedReference(loc)
      //case Some(e@SymbolicExpr(_, _)) => e
      case Some(_) => throw new Exception("Internal error")
      case None =>
        functionDeclarations.get(name) match {
          case Some(fun) => fun
          case None =>
            throw new Exception("Unexpected input in interpreter. Semantic analyses does not work properly.")
        }
    }

  }

  def updateRef(ptr: PointerVal, v: Val): Unit = {
    storage.addVal(ptr, v)
  }

  def deepCopy(): SymbolicStore = {
    val res = new SymbolicStore(functionDeclarations)
    res.frames = Array.empty
    for (frame <- this.frames) {
      res.frames = res.frames.appended(frame)
    }
    res.storage = this.storage.asInstanceOf[res.Storage].deepCopy()
    res
  }


  def storeValues(v1: Val, v2: Val, store1: SymbolicStore, store2: SymbolicStore): Boolean = {
    (v1, v2) match {
      case (NullRef, NullRef) => true
      case (UninitializedRef, UninitializedRef) => true
      case (p1: PointerVal, p2: PointerVal) =>
        (store1.storage.getVal(p1), store2.storage.getVal(p2)) match {
          case (Some(s1), Some(s2)) =>
            storeValues(s1, s2, store1, store2)
          case (None, None) => true
        }
      case (v1, v2) =>
        v1.equals(v2)
    }
  }


  def storeEquals(symbolicStore: SymbolicStore): Boolean = {
    if (this.frames.size == symbolicStore.frames.size) {
      for (i <- 0 until this.frames.size) {
        val thisFrame = this.frames(i)
        val otherFrame = symbolicStore.frames(i)
        if (thisFrame.size == otherFrame.size) {
          val thisVars = thisFrame.keys
          val otherVars = otherFrame.keys
          if (thisVars == otherVars) {
            for (variable <- thisVars) {
              val a = thisFrame(variable)
              val b = otherFrame(variable)
              (thisFrame(variable), otherFrame(variable)) match {
                case (v1: PointerVal, v2: PointerVal) =>
                  val res = storeValues(v1, v2, this, symbolicStore)
                  if (!res) {
                    return false
                  }
                case (NullRef, _) =>
                  return false
                case (_, NullRef) =>
                  return false
                case _ =>
              }
            }
          }
          else {
            return false
          }
        }
        else {
          return false
        }
      }
      return true
    }
    false
  }


  def getPtr(res: SymbolicStore,
             store: SymbolicStore,
             ptr: PointerVal,
             pointerMapping: mutable.HashMap[Int, Int]): PointerVal = {
    store.storage.getVal(ptr) match {
      case Some(PointerVal(addr)) =>
        val addr1 = getPtr(res, store, PointerVal(addr), pointerMapping)
        val added = res.storage.addNewVal(addr1)
        pointerMapping.put(ptr.address, added.address)
        added
      case Some(v1) =>
        val addr = res.storage.addNewVal(v1)
        pointerMapping.put(ptr.address, addr.address)
        addr
      case None =>
        val addr = res.storage.addNewVal(UninitializedRef)
        pointerMapping.put(ptr.address, addr.address)
        addr
    }
  }



  def getPtrs(res: SymbolicStore,
             store1: SymbolicStore,
             store2: SymbolicStore,
             ptr1: PointerVal,
             ptr2: PointerVal,
             pointerMapping1: mutable.HashMap[Int, Int],
             pointerMapping2: mutable.HashMap[Int, Int]): (PointerVal, PointerVal) = {
    if (pointerMapping1.contains(ptr1.address) && pointerMapping2.contains(ptr2.address)) {
      return (PointerVal(pointerMapping1(ptr1.address)), PointerVal(pointerMapping2(ptr2.address)))
    }
    (store1.storage.getVal(ptr1), store2.storage.getVal(ptr2)) match {
      case (Some(PointerVal(p1)), Some(PointerVal(p2))) =>
        var (addr1: PointerVal, addr2: PointerVal) = getPtrs(res, store1, store2, PointerVal(p1), PointerVal(p2), pointerMapping1, pointerMapping2)
        if (addr1.address == addr2.address) {
          val added = res.storage.addNewVal(addr1)
          pointerMapping1.put(ptr1.address, added.address)
          pointerMapping2.put(ptr2.address, added.address)
          (added, added)
        }
        else {
          val added1 = res.storage.addNewVal(addr1)
          val added2 = res.storage.addNewVal(addr2)
          pointerMapping1.put(ptr1.address, added1.address)
          pointerMapping2.put(ptr2.address, added2.address)
          (added1, added2)
        }
      case (Some(v1), Some(v2)) if v1 == v2 =>
        val addr = res.storage.addNewVal(v1)
        pointerMapping1.put(ptr1.address, addr.address)
        pointerMapping2.put(ptr2.address, addr.address)
        (addr, addr)
      case (Some(v1), Some(v2)) =>
        val addr1 = res.storage.addNewVal(v1)
        pointerMapping1.put(ptr1.address, addr1.address)
        val addr2 = res.storage.addNewVal(v2)
        pointerMapping2.put(ptr2.address, addr2.address)
        (addr1, addr2)
      case (Some(PointerVal(addr)), None) =>
        var addr1 = getPtr(res, store1, PointerVal(addr), pointerMapping1)
        addr1 = res.storage.addNewVal(addr1)
        pointerMapping1.put(ptr1.address, addr1.address)
        val addr2 = res.storage.addNewVal(UninitializedRef)
        pointerMapping2.put(ptr2.address, addr2.address)
        (addr1, addr2)
      case (None, Some(PointerVal(addr))) =>
        val added = getPtr(res, store2, PointerVal(addr), pointerMapping2)
        val addr1 = res.storage.addNewVal(added)
        pointerMapping1.put(ptr1.address, addr1.address)
        val addr2 = res.storage.addNewVal(UninitializedRef)
        pointerMapping2.put(ptr2.address, addr2.address)
        (addr1, addr2)
      case (Some(v1), None) =>
        val addr1 = res.storage.addNewVal(v1)
        pointerMapping1.put(ptr1.address, addr1.address)
        val addr2 = res.storage.addNewVal(UninitializedRef)
        pointerMapping2.put(ptr2.address, addr2.address)
        (addr1, addr2)
      case (None, Some(v1)) =>
        val addr1 = res.storage.addNewVal(v1)
        pointerMapping1.put(ptr1.address, addr1.address)
        val addr2 = res.storage.addNewVal(UninitializedRef)
        pointerMapping2.put(ptr2.address, addr2.address)
        (addr1, addr2)
      case (None, None) =>
        val addr = res.storage.addNewVal(UninitializedRef)
        pointerMapping1.put(ptr1.address, addr.address)
        pointerMapping2.put(ptr2.address, addr.address)
        (addr, addr)
    }
  }


  // states should have the same number of frames
  def mergeStores(other: SymbolicStore, pathCondition: PathCondition): Option[SymbolicStore] = {
    val res = new SymbolicStore(functionDeclarations)
    val thisPointerMapping: mutable.HashMap[Int, Int] = new mutable.HashMap[Int, Int]()
    val otherPointerMapping: mutable.HashMap[Int, Int] = new mutable.HashMap[Int, Int]()
    for (i <- 0 until this.frames.size) {
      val thisFrame = this.frames(i)
      val otherFrame = other.frames(i)
      for (variable <- thisFrame.keys) {
        if (otherFrame.contains(variable)) {
          val p1 = thisFrame(variable)
          val p2 = otherFrame(variable)
          (thisFrame(variable), otherFrame(variable)) match {
            case (PointerVal(ptr1), PointerVal(ptr2)) => {
              val p = storage.getVal(PointerVal(ptr1))
              val o = other.storage.getVal(PointerVal(ptr2))
              val (addr1, addr2) = getPtrs(res, this, other, PointerVal(ptr1), PointerVal(ptr2), thisPointerMapping, otherPointerMapping)
              if (addr1.address == addr2.address) {
                res.addVar(variable, addr1)
              }
              else {
                val addr = res.storage.getAddress
                res.addVar(variable, addr)
                val v1 = res.storage.getVal(addr1).get
                val v2 = res.storage.getVal(addr2).get
                res.updateRef(addr, IteVal(v1, v2, pathCondition.expr, CodeLoc(0, 0)))
              }
//              (storage.getVal(PointerVal(ptr1)), other.storage.getVal(PointerVal(ptr2))) match {
//                case (Some(val1), Some(val2)) if val1 == val2 =>
//                  val addr = res.storage.getAddress
//                  res.addVar(variable, addr)
//                  res.updateRef(addr, val1)
//                  thisPointerMapping.put(ptr1, addr.address)
//                  otherPointerMapping.put(ptr2, addr.address)
//                case (Some(val1), Some(val2)) =>
//                  val addr = res.storage.getAddress
//                  res.addVar(variable, addr)
//                  res.updateRef(addr, IteVal(val1, val2, pathCondition.expr, CodeLoc(0, 0)))
//                  thisPointerMapping.put(ptr1, addr.address)
//                  otherPointerMapping.put(ptr2, addr.address)
//                case (None, None) =>
//                  val addr = res.storage.getAddress
//                  res.addVar(variable, addr)
//                  res.updateRef(addr, UninitializedRef)
//                  thisPointerMapping.put(ptr1, addr.address)
//                  otherPointerMapping.put(ptr2, addr.address)
//                case _ =>
//                  throw new Exception("")
//              }
            }
          }
        }
        else {
          thisFrame(variable) match {
            case PointerVal(ptr) =>
              val addr = res.storage.getAddress
              res.addVar(variable, addr)
              res.updateRef(addr, storage.getVal(PointerVal(ptr)).get)
          }
        }
      }
      for (variable <- otherFrame.keys) {
        if (!thisFrame.contains(variable)) {
          otherFrame(variable) match {
            case PointerVal(ptr) =>
              val addr = res.storage.getAddress
              res.addVar(variable, addr)
              res.updateRef(addr, other.storage.getVal(PointerVal(ptr)).get)
          }
        }
      }
      if (i < this.frames.length - 1) {
        res.pushFrame()
      }
    }
    Some(res)
  }
}
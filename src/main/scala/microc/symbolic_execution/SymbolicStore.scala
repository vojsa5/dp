package microc.symbolic_execution

import microc.ast.{CodeLoc, Expr, Identifier, Loc}
import microc.symbolic_execution.ExecutionException.{errorIncompatibleTypes, errorUninitializedReference}
import microc.symbolic_execution.Value.{ArrVal, FunVal, IteVal, NullRef, PointerVal, RecVal, RefVal, SymbolicVal, UninitializedRef, Val}

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
        newStorage.memory += (v match {
          case ArrVal(elems) => ArrVal(elems.map(elem => PointerVal(elem.address)))//deep copy pointers within an array
          case RecVal(fields) => RecVal(fields.map(field => (field._1, PointerVal(field._2.address))))//deep copy pointers within a record
          case _ => v
        })
      }
      newStorage
    }

    def getAddress: PointerVal = {
      val res = PointerVal(size)
      size += 1
      memory += UninitializedRef
      res
    }

    private def iteContainsUninitialized(iteVal: IteVal): Boolean = {
      iteVal match {
        case IteVal(trueState, falseState, _, _) if falseState == UninitializedRef || trueState == UninitializedRef => true
        case IteVal(trueState: IteVal, falseState: IteVal, _, _) => iteContainsUninitialized(trueState) || iteContainsUninitialized(falseState)
        case IteVal(trueState: IteVal, _, _, _) => iteContainsUninitialized(trueState)
        case IteVal(_, falseState: IteVal, _, _) => iteContainsUninitialized(falseState)
        case _ => false
      }
    }

    def getVal(ptr: PointerVal, allowReturnNonInitialized: Boolean = false): Option[Val] = {
      if (memory.size <= ptr.address) {
        return None
      }
      memory(ptr.address) match {
        case UninitializedRef if allowReturnNonInitialized => Some(UninitializedRef)
        case UninitializedRef => None
        case ite@IteVal(_, _, _, _)  => {
          if (iteContainsUninitialized(ite)) {
            if (allowReturnNonInitialized) {
              Some(ite)
            }
            else {
              None
            }
          }
          else {
            Some(ite)
          }
        }
        case v =>
          Some(v)
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

  private var frames: Array[Map[String, PointerVal]] = Array(Map.empty)

  def pushFrame(): Unit = frames = frames.appended(Map.empty)

  def popFrame(): Unit = {
//    for (value <- frames.last.values) {
//      value match {
//        case PointerVal(address) => storage.deleteVal(PointerVal(address))
//      }
//    }
    frames = frames.dropRight(1)
  }

  def framesCnt(): Int = {
    frames.length
  }

  def addVar(name: String, ref: PointerVal): Unit = {
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

  def findVar(name: String): Option[PointerVal] = {
    for (frame <- frames.reverse) {
      if (frame.contains(name)) {
        return Some(frame(name))
      }
    }
    None
  }

  def contains(name: String): Boolean = {
    for (frame <- frames.reverse) {
      if (frame.contains(name)) {
        storage.getVal(frame(name)) match {
          case Some(UninitializedRef) =>
            return false
          case Some(_) =>
            return true
          case _ =>
            return false
        }
      }
    }
    false
  }

  def getValOfPtr(ptr: PointerVal, allowReturnNonInitialized: Boolean = false): Option[Val] = {
    storage.getVal(ptr, allowReturnNonInitialized)
  }

  def getVal(name: String, loc: Loc, symbolicState: SymbolicState, allowReturnNonInitialized: Boolean = false): Val = {
    findVar(name) match {
      case Some(PointerVal(decl)) =>
        storage.getVal(PointerVal(decl)) match {
          case Some(res) => res
          case None if allowReturnNonInitialized => UninitializedRef
          case None =>
            throw errorUninitializedReference(loc, symbolicState)
        }
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


  def storeValuesEquals(v1: Val, v2: Val, store1: SymbolicStore, store2: SymbolicStore): Boolean = {
    (v1, v2) match {
      case (NullRef, NullRef) => true
      case (UninitializedRef, UninitializedRef) => true
      case (p1: PointerVal, p2: PointerVal) =>
        (store1.storage.getVal(p1), store2.storage.getVal(p2)) match {
          case (Some(s1), Some(s2)) =>
            storeValuesEquals(s1, s2, store1, store2)
          case (None, None) => true
        }
      case (p1: ArrVal, p2: ArrVal) =>
        if (p1.elems.length == p2.elems.length) {
          for (i <- p1.elems.indices) {
            (store1.storage.getVal(p1.elems(i)), store2.storage.getVal(p2.elems(i))) match {
              case (Some(s1), Some(s2)) if !storeValuesEquals(s1, s2, store1, store2) =>
                return false
              case (Some(_), Some(_)) =>
              case (None, None) =>
            }
          }
          return true
        }
        false
      case (v1, v2) =>
        v1.equalsVal(v2)
    }
  }


  def getDifferentVariables(symbolicStore: SymbolicStore): mutable.HashSet[String] = {
    val resMap: mutable.HashSet[String] = new mutable.HashSet[String]
    if (this.frames.size == symbolicStore.frames.size) {
      for (i <- 0 until this.frames.size) {
        val thisFrame = this.frames(i)
        val otherFrame = symbolicStore.frames(i)
        if (thisFrame.size == otherFrame.size) {
          val thisVars = thisFrame.keys
          val otherVars = otherFrame.keys
          if (thisVars == otherVars) {
            for (variable <- thisVars) {
              (thisFrame(variable), otherFrame(variable)) match {
                case (v1: PointerVal, v2: PointerVal) =>
                  val res = storeValuesEquals(v1, v2, this, symbolicStore)
                  if (!res) {
                    resMap.add(variable)
                  }
//                case (NullRef, _) =>
//                  resMap.add(variable)
//                case (_, NullRef) =>
//                  resMap.add(variable)
                case _ =>
              }
            }
          }
        }
      }
    }
    mutable.HashSet.empty
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
              (thisFrame(variable), otherFrame(variable)) match {
                case (v1: PointerVal, v2: PointerVal) =>
                  val res = storeValuesEquals(v1, v2, this, symbolicStore)
                  if (!res) {
                    return false
                  }
//                case (NullRef, _) =>
//                  return false
//                case (_, NullRef) =>
//                  return false
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


  def moveValue(res: SymbolicStore,
                store: SymbolicStore,
                ptr: PointerVal,
                pointerMapping: mutable.HashMap[Int, Int]): PointerVal = {
    if (pointerMapping.contains(ptr.address)) {
      return PointerVal(pointerMapping(ptr.address))
    }
    val addr = store.storage.getVal(ptr) match {
      case Some(PointerVal(addr)) =>
        val addr1 = moveValue(res, store, PointerVal(addr), pointerMapping)
        res.storage.addNewVal(addr1)
      case Some(ArrVal(elems)) =>
        var arr = Array[PointerVal]()
        for (i <- elems.indices) {
          arr = arr.appended(moveValue(res, store, elems(i), pointerMapping))
        }
        res.storage.addNewVal(ArrVal(arr))
      case Some(RecVal(fields)) =>
        var rec = mutable.HashMap[String, PointerVal]()
        for (field <- fields.keys) {
          rec.put(field, moveValue(res, store, fields(field), pointerMapping))
        }
        res.storage.addNewVal(RecVal(rec))
      case Some(v1) =>
        res.storage.addNewVal(v1)
      case None =>
        res.storage.addNewVal(UninitializedRef)
    }
    pointerMapping.put(ptr.address, addr.address)
    addr
  }



  def moveValues(res: SymbolicStore,
                 store1: SymbolicStore,
                 store2: SymbolicStore,
                 ptr1: PointerVal,
                 ptr2: PointerVal,
                 pointerMapping1: mutable.HashMap[Int, Int],
                 pointerMapping2: mutable.HashMap[Int, Int]): (PointerVal, PointerVal) = {
    if (pointerMapping1.contains(ptr1.address) && pointerMapping2.contains(ptr2.address)) {
      return (PointerVal(pointerMapping1(ptr1.address)), PointerVal(pointerMapping2(ptr2.address)))
    }
    if (pointerMapping1.contains(ptr1.address)) {
      return (PointerVal(pointerMapping1(ptr1.address)), moveValue(res, store2, ptr2, pointerMapping2))
    }
    if (pointerMapping2.contains(ptr2.address)) {
      return (moveValue(res, store1, ptr1, pointerMapping1), PointerVal(pointerMapping2(ptr2.address)))
    }
    (store1.storage.getVal(ptr1), store2.storage.getVal(ptr2)) match {
      case (Some(PointerVal(p1)), Some(PointerVal(p2))) =>
        var (addr1: PointerVal, addr2: PointerVal) = moveValues(res, store1, store2, PointerVal(p1), PointerVal(p2), pointerMapping1, pointerMapping2)
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
      case (Some(ArrVal(elems1)), Some(ArrVal(elems2))) =>
        if (elems1.length == elems2.length) {
          var arrayAreSame = true
          var arr1 = Array[PointerVal]()
          var arr2 = Array[PointerVal]()
          for (i <- elems1.indices) {
            var (addr1: PointerVal, addr2: PointerVal) =
              moveValues(res, store1, store2, elems1(i), elems2(i), pointerMapping1, pointerMapping2)
            arr1 = arr1.appended(addr1)
            arr2 = arr2.appended(addr2)
            if (addr1 != addr2) {
              arrayAreSame = false
            }
          }
          if (arrayAreSame) {
            val a1 = ArrVal(arr1)
            val added = res.storage.addNewVal(a1)
            pointerMapping1.put(ptr1.address, added.address)
            pointerMapping2.put(ptr2.address, added.address)
            (added, added)
          }
          else {
            val a1 = ArrVal(arr1)
            val a2 = ArrVal(arr2)
            val added1 = res.storage.addNewVal(a1)
            val added2 = res.storage.addNewVal(a2)
            pointerMapping1.put(ptr1.address, added1.address)
            pointerMapping2.put(ptr2.address, added2.address)
            (added1, added2)
          }
        }
        else {
          throw  new Exception("this should never happen")
        }
      case (Some(RecVal(fields1)), Some(RecVal(fields2))) =>
        if (fields1.keys == fields2.keys) {
          var arrayAreSame = true
          var rec1 = mutable.HashMap[String, PointerVal]()
          var rec2 = mutable.HashMap[String, PointerVal]()
          for (field <- fields1.keys) {
            var (addr1: PointerVal, addr2: PointerVal) =
              moveValues(res, store1, store2, fields1(field), fields2(field), pointerMapping1, pointerMapping2)
            rec1.put(field, addr1)
            rec2.put(field, addr2)
            if (addr1 != addr2) {
              arrayAreSame = false
            }
          }
          if (arrayAreSame) {
            val a1 = RecVal(rec1)
            val added = res.storage.addNewVal(a1)
            pointerMapping1.put(ptr1.address, added.address)
            pointerMapping2.put(ptr2.address, added.address)
            (added, added)
          }
          else {
            val a1 = RecVal(rec1)
            val a2 = RecVal(rec2)
            val added1 = res.storage.addNewVal(a1)
            val added2 = res.storage.addNewVal(a2)
            pointerMapping1.put(ptr1.address, added1.address)
            pointerMapping2.put(ptr2.address, added2.address)
            (added1, added2)
          }
        }
        else {
          throw new Exception("IMPLEMENT")
        }
      case (Some(v1), Some(v2)) if v1.equalsVal(v2) =>
        val addr = res.storage.addNewVal(v1)
        pointerMapping1.put(ptr1.address, addr.address)
        pointerMapping2.put(ptr2.address, addr.address)
        (addr, addr)
      case (None, None) =>
        val addr = res.storage.addNewVal(UninitializedRef)
        pointerMapping1.put(ptr1.address, addr.address)
        pointerMapping2.put(ptr2.address, addr.address)
        (addr, addr)
      case (_, _) =>
        (moveValue(res, store1, ptr1, pointerMapping1), moveValue(res, store2, ptr2, pointerMapping2))
    }
  }


  // states should have the same number of frames
  def mergeStores(other: SymbolicStore, pathCondition: Expr): Option[SymbolicStore] = {
    val res = new SymbolicStore(functionDeclarations)
    val thisPointerMapping: mutable.HashMap[Int, Int] = new mutable.HashMap[Int, Int]()
    val otherPointerMapping: mutable.HashMap[Int, Int] = new mutable.HashMap[Int, Int]()
    for (i <- 0 until this.frames.size) {
      val thisFrame = this.frames(i)
      val otherFrame = other.frames(i)
      for (variable <- thisFrame.keys) {
        if (otherFrame.contains(variable)) {
          (thisFrame(variable), otherFrame(variable)) match {
            case (PointerVal(ptr1), PointerVal(ptr2)) => {
              val (addr1, addr2) = moveValues(res, this, other, PointerVal(ptr1), PointerVal(ptr2), thisPointerMapping, otherPointerMapping)
              if (addr1.address == addr2.address) {
                res.addVar(variable, addr1)
              }
              else {
                val addr = res.storage.getAddress
                res.addVar(variable, addr)
                val v1 = res.storage.getVal(addr1, true).get
                res.storage.getVal(addr2, true).get match {
                  case UninitializedRef =>
                    System.out.println("dafdsfddf")
                  case _ =>
                }

                val v2 = res.storage.getVal(addr2, true).get
                res.updateRef(addr, IteVal(v1, v2, pathCondition, CodeLoc(0, 0)))
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
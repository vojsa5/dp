package microc.symbolic_execution

import microc.ast.{BinaryOp, CodeLoc, Expr, Identifier, Loc, Not, OrOr}
import microc.symbolic_execution.ExecutionException.{errorIncompatibleTypes, errorUninitializedReference}
import microc.symbolic_execution.Value.{ArrVal, FunVal, IteVal, NullRef, PointerVal, RecVal, RefVal, Symbolic, SymbolicVal, UninitializedRef, Val}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer


object SymbolicStore {

  def mergePathCondition(pathCondition: Expr, symbolicStore: SymbolicStore, res: SymbolicStore, pointerMapping: mutable.HashMap[Int, Int]): Expr = {
    pathCondition match {
      case PointerVal(address) =>
        pointerMapping.get(address) match {
          case Some(addr) =>
            res.storage.getVal(PointerVal(addr)).get.asInstanceOf[Symbolic]
          case None =>
            val v = mergePathCondition(
              symbolicStore.getValOfPtr(PointerVal(address)).get.asInstanceOf[Symbolic],
              symbolicStore,
              res,
              pointerMapping
            ).asInstanceOf[Symbolic]
            val ptr = res.storage.addNewVal(v)
            pointerMapping.put(address, ptr.address)
            v
        }
      case IteVal(trueState, falseState, expr, loc) =>
        val ite = IteVal(
          pointerMapping.get(trueState.address) match {
            case Some(addr) =>
              PointerVal(addr)
            case None =>
              val v = mergePathCondition(
                trueState,
                symbolicStore,
                res,
                pointerMapping
              ).asInstanceOf[Symbolic]
              val ptr = res.storage.addNewVal(v)
              pointerMapping.put(trueState.address, ptr.address)
              ptr
          },
          pointerMapping.get(falseState.address) match {
            case Some(addr) =>
              PointerVal(addr)
            case None =>
              val v = mergePathCondition(
                falseState,
                symbolicStore,
                res,
                pointerMapping
              ).asInstanceOf[Symbolic]
              val ptr = res.storage.addNewVal(v)
              pointerMapping.put(falseState.address, ptr.address)
              ptr
          },
          expr,
          loc
        )
        ite
      case BinaryOp(op, left, right, loc) =>
        BinaryOp(
          op,
          mergePathCondition(left, symbolicStore, res, pointerMapping),
          mergePathCondition(right, symbolicStore, res, pointerMapping),
          loc
        )
      case Not(expr, loc) => Not(mergePathCondition(expr, symbolicStore, res, pointerMapping), loc)
      case other => other
    }
  }

}


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

//    private def iteContainsUninitialized(iteVal: IteVal): Boolean = {
//      iteVal match {
//        case IteVal(trueState, falseState, _, _) if falseState == UninitializedRef || trueState == UninitializedRef => true
//        case IteVal(trueState: IteVal, falseState: IteVal, _, _) => iteContainsUninitialized(trueState) || iteContainsUninitialized(falseState)
//        case IteVal(trueState: IteVal, _, _, _) => iteContainsUninitialized(trueState)
//        case IteVal(_, falseState: IteVal, _, _) => iteContainsUninitialized(falseState)
//        case _ => false
//      }
//    }

    private def iteContainsUninitialized(iteVal: IteVal, store: Storage): Boolean = {
      iteVal match {
        case IteVal(trueState, falseState, expr, loc) =>
          (store.getVal(trueState, true), store.getVal(falseState, true)) match {
            case (Some(r1), Some(r2)) =>
              (r1, r2) match {
                case (UninitializedRef, UninitializedRef) => true
                case (i1: IteVal, i2: IteVal) =>
                  iteContainsUninitialized(i1, store) || iteContainsUninitialized(i2, store)
                case (i1: IteVal, i2) =>
                  iteContainsUninitialized(i1, store)
                case (i1, i2: IteVal) =>
                  iteContainsUninitialized(i2, store)
                case other =>
                  false
              }
            case _ =>
              throw new Exception("this should never happen")
          }
        case _ =>
          false
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
          if (iteContainsUninitialized(ite, this)) {
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

  private var frames: Array[mutable.HashMap[String, PointerVal]] = Array(mutable.HashMap.empty)

  def pushFrame(): Unit = frames = frames.appended(mutable.HashMap.empty)

  def popFrame(): Unit = {
    frames = frames.dropRight(1)
  }

  def lastFrameVars(): mutable.HashSet[String] = {
    val res = mutable.HashSet[String]()
    res.addAll(frames.last.keys)
    res
  }

  def framesCnt(): Int = {
    frames.length
  }

  def addVar(name: String, ref: PointerVal): Unit = {
    frames.last.put(name, ref)
  }

  def addNewVar(name: String): PointerVal = {
    val res = storage.getAddress
    frames.last.put(name, res)
    res
  }

  def findVar(name: String): Option[PointerVal] = {
//    for (frame <- frames.reverse) {
//      if (frame.contains(name)) {
//        return Some(frame(name))
//      }
//    }
//    None
    frames.last.get(name)
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
          case _ => false
        }
      case (p1: ArrVal, p2: ArrVal) =>
        if (p1.elems.length == p2.elems.length) {
          for (i <- p1.elems.indices) {
            (store1.storage.getVal(p1.elems(i)), store2.storage.getVal(p2.elems(i))) match {
              case (Some(s1), Some(s2)) if !storeValuesEquals(s1, s2, store1, store2) =>
                return false
              case (Some(_), Some(_)) =>
              case (None, None) =>
              case _ =>
                return false
            }
          }
          return true
        }
        false
        //TODO records
      case (IteVal(trueState1, falseState1, expr1, _), IteVal(trueState2, falseState2, expr2, _)) =>
        (store1.storage.getVal(trueState1), store2.storage.getVal(trueState2), store1.storage.getVal(falseState1), store2.storage.getVal(falseState2)) match {
          case (Some(s1), Some(s2), Some(s3), Some(s4)) =>
            storeValuesEquals(s1, s2, store1, store2) && storeValuesEquals(s3, s4, store1, store2) && expr1.equals(expr2)
          case (Some(s1), Some(s2), None, None) =>
            storeValuesEquals(s1, s2, store1, store2) && expr1.equals(expr2)
          case (None, None, Some(s3), Some(s4)) =>
            storeValuesEquals(s3, s4, store1, store2) && expr1.equals(expr2)
          case (None, None, None, None) =>
            expr1.equals(expr2)
          case _ =>
            false
        }
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
    resMap
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
      case Some(IteVal(trueState, falseState, expr, loc)) =>
        val ite = IteVal(
          moveValue(res, store, trueState, pointerMapping),
          moveValue(res, store, falseState, pointerMapping),
          expr,
          loc
        )
        res.storage.addNewVal(ite)
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
                 pointerMapping2: mutable.HashMap[Int, Int],
                 pathCondition: Expr): (PointerVal, PointerVal) = {
    if (pointerMapping1.contains(ptr1.address) && pointerMapping2.contains(ptr2.address)) {
      return (PointerVal(pointerMapping1(ptr1.address)), PointerVal(pointerMapping2(ptr2.address)))
    }
    if (pointerMapping1.contains(ptr1.address)) {
      return (PointerVal(pointerMapping1(ptr1.address)), res.storage.addNewVal(moveValue(res, store2, ptr2, pointerMapping2)))
    }
    if (pointerMapping2.contains(ptr2.address)) {
      return (res.storage.addNewVal(moveValue(res, store1, ptr1, pointerMapping1)), PointerVal(pointerMapping2(ptr2.address)))
    }
    (store1.storage.getVal(ptr1), store2.storage.getVal(ptr2)) match {
      case (Some(PointerVal(p1)), Some(PointerVal(p2))) =>
        val (addr1: PointerVal, addr2: PointerVal) = moveValues(res, store1, store2, PointerVal(p1), PointerVal(p2), pointerMapping1, pointerMapping2, pathCondition)
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
          var arr = Array[PointerVal]()
          for (i <- elems1.indices) {
            val (addr1: PointerVal, addr2: PointerVal) = {
              moveValues(res, store1, store2, elems1(i), elems2(i), pointerMapping1, pointerMapping2, pathCondition)
            }
            if (addr1 == addr2) {
              arr = arr.appended(addr1)
            }
            else {
              val ite = IteVal(addr1, addr2, pathCondition, CodeLoc(0, 0))
              arr = arr.appended(res.storage.addNewVal(ite))
            }
          }
          val a = ArrVal(arr)
          val added = res.storage.addNewVal(a)
          pointerMapping1.put(ptr1.address, added.address)
          pointerMapping2.put(ptr2.address, added.address)
          (added, added)
        }
        else {
          if (elems1.length < elems2.length) {
            var arr = Array[PointerVal]()
            for (i <- elems1.indices) {
              val (addr1: PointerVal, addr2: PointerVal) = {
                moveValues(res, store1, store2, elems1(i), elems2(i), pointerMapping1, pointerMapping2, pathCondition)
              }
              if (addr1 == addr2) {
                arr = arr.appended(addr1)
              }
              else {
                val ite = IteVal(addr1, addr2, pathCondition, CodeLoc(0, 0))
                arr = arr.appended(res.storage.addNewVal(ite))
              }
            }
            for (i <- elems2.indices) {
              if (elems1.length <= i) {
                arr = arr.appended(
                  res.storage.addNewVal(
                    IteVal(
                      moveValue(res, store2, elems2(i), pointerMapping2),
                      res.storage.addNewVal(UninitializedRef),
                      pathCondition,
                      CodeLoc(0, 0)
                    )
                  )
                )
              }
            }
            val a = ArrVal(arr)
            val added = res.storage.addNewVal(a)
            pointerMapping1.put(ptr1.address, added.address)
            pointerMapping2.put(ptr2.address, added.address)
            (added, added)
          }
          else {
            var arr = Array[PointerVal]()
            for (i <- elems2.indices) {
              val (addr1: PointerVal, addr2: PointerVal) = {
                moveValues(res, store1, store2, elems1(i), elems2(i), pointerMapping1, pointerMapping2, pathCondition)
              }
              if (addr1 == addr2) {
                arr = arr.appended(addr1)
              }
              else {
                val ite = IteVal(addr1, addr2, pathCondition, CodeLoc(0, 0))
                arr = arr.appended(res.storage.addNewVal(ite))
              }
            }
            for (i <- elems1.indices) {
              if (elems2.length <= i) {
                arr = arr.appended(
                  res.storage.addNewVal(
                    IteVal(
                      moveValue(res, store1, elems1(i), pointerMapping1),
                      res.storage.addNewVal(UninitializedRef),
                      pathCondition,
                      CodeLoc(0, 0)
                    )
                  )
                )
              }
            }
            val a = ArrVal(arr)
            val added = res.storage.addNewVal(a)
            pointerMapping1.put(ptr1.address, added.address)
            pointerMapping2.put(ptr2.address, added.address)
            (added, added)
          }
        }
      case (Some(RecVal(fields1)), Some(RecVal(fields2))) =>
        if (fields1.keys == fields2.keys) {
          val rec = mutable.HashMap[String, PointerVal]()
          for (field <- fields1.keys) {
            var (addr1: PointerVal, addr2: PointerVal) =
              moveValues(res, store1, store2, fields1(field), fields2(field), pointerMapping1, pointerMapping2, pathCondition)
            if (addr1 == addr2) {
              rec.put(field, addr1)
            }
            else {
              val ite = IteVal(addr1, addr2, pathCondition, CodeLoc(0, 0))
              rec.put(field, res.storage.addNewVal(ite))
            }
          }
          val r = RecVal(rec)
          val added = res.storage.addNewVal(r)
          pointerMapping1.put(ptr1.address, added.address)
          pointerMapping2.put(ptr2.address, added.address)
          (added, added)
        }
        else {
          throw new Exception("this should never happen.")
        }
      case (Some(IteVal(trueState1, falseState1, expr1, loc1)), Some(IteVal(trueState2, falseState2, expr2, loc2))) if expr1 == expr2 =>
        val t1 = moveValues(res, store1, store2, trueState1, trueState2, pointerMapping1, pointerMapping2, pathCondition)
        val t2 = moveValues(res, store1, store2, falseState1, falseState2, pointerMapping1, pointerMapping2, pathCondition)
        val newTrueState = if (t1._1 == t1._2) {
          t1._1
        }
        else {
          val ite = IteVal(t1._1, t1._2, pathCondition, CodeLoc(0, 0))
          res.storage.addNewVal(ite)
        }
        val newFalseState = if (t2._1 == t2._2) {
          t2._1
        }
        else {
          val ite = IteVal(t2._1, t2._2, pathCondition, CodeLoc(0, 0))
          res.storage.addNewVal(ite)
        }
        val ite = IteVal(newTrueState, newFalseState, expr1, loc1)
        val added = res.storage.addNewVal(ite)
        pointerMapping1.put(ptr1.address, added.address)
        pointerMapping2.put(ptr2.address, added.address)
        (added, added)
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
        val p1 = moveValue(res, store1, ptr1, pointerMapping1)
        val p2 = moveValue(res, store2, ptr2, pointerMapping2)
        val ite = IteVal(p1, p2, pathCondition, CodeLoc(0, 0))
        val addr = res.storage.addNewVal(ite)
        (addr, addr)
    }
  }



  // states should have the same number of frames
  def mergeStores(other: SymbolicStore, pathCondition: Expr, pathCondition2: Expr): Option[(SymbolicStore, Expr)] = {
    val res = new SymbolicStore(functionDeclarations)
    val thisPointerMapping: mutable.HashMap[Int, Int] = new mutable.HashMap[Int, Int]()
    val otherPointerMapping: mutable.HashMap[Int, Int] = new mutable.HashMap[Int, Int]()
    val start = System.currentTimeMillis()
    for (i <- 0 until this.frames.size) {
      val thisFrame = this.frames(i)
      val otherFrame = other.frames(i)
      for (variable <- thisFrame.keys) {
        if (otherFrame.contains(variable)) {
          (thisFrame(variable), otherFrame(variable)) match {
            case (PointerVal(ptr1), PointerVal(ptr2)) =>
              val (addr1, addr2) = moveValues(res, this, other, PointerVal(ptr1), PointerVal(ptr2), thisPointerMapping, otherPointerMapping, pathCondition)
              if (addr1.address == addr2.address) {
                res.addVar(variable, addr1)
              }
              else {
                val addr = res.storage.getAddress
                res.addVar(variable, addr)
                val ite = IteVal(addr1, addr2, pathCondition, CodeLoc(0, 0))
                res.updateRef(addr, ite)
              }

          }
        }
      }
      if (i < this.frames.length - 1) {
        res.pushFrame()
      }
    }
    val end = System.currentTimeMillis()
    //val r = Utility.simplifyADisjunction(pathCondition, pathCondition2)//this proved to be too slow
    System.out.println("MERGING2: ", end - start)
    Some(res, BinaryOp(OrOr, pathCondition, pathCondition2, CodeLoc(0, 0)))
  }
}
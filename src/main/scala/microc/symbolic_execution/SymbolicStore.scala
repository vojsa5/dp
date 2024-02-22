package microc.symbolic_execution

import microc.ast.{CodeLoc, Identifier, Loc}
import microc.symbolic_execution.ExecutionException.{errorIncompatibleTypes, errorUninitializedReference}
import microc.symbolic_execution.Value.{FunVal, IteVal, NullRef, PointerVal, RefVal, SymbolicVal, UninitializedRef, Val}

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

    def getVal(ptr: PointerVal): Option[Val] = {
      if (memory.size <= ptr.address) {
        return None
      }
      memory(ptr.address) match {
        case UninitializedRef => None
        case v => Some(v)
      }
    }

    def addVal(ptr: PointerVal, v: Val): Unit = {
      memory(ptr.address) = v
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

  def getValOfPtr(ptr: PointerVal): Option[Val] = {
    storage.getVal(ptr)
  }

  def getVal(name: String, loc: Loc): Val = {
    findVar(name) match {
      case Some(PointerVal(decl)) =>
        storage.getVal(PointerVal(decl)) match {
          case Some(res) => res
          case None => throw errorUninitializedReference(loc)
        }
      case Some(NullRef) => throw errorUninitializedReference(loc)
      //case Some(e@SymbolicExpr(_, _)) => e
      case Some(_) => throw new Exception("Internal error")
      case None =>
        functionDeclarations.get(name) match {
          case Some(fun) => fun
          case None => throw new Exception("Unexpected input in interpreter. Semantic analyses does not work properly.")
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
                case (PointerVal(ptr1), PointerVal(ptr2)) =>
                  if (!storage.getVal(PointerVal(ptr1)).get.equals(symbolicStore.storage.getVal(PointerVal(ptr2)).get)) {
                    return false
                  }
                case (NullRef, _) => return false
                case (_, NullRef) => return false
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


  def mergeStores(other: SymbolicStore, pathCondition: PathCondition): Option[SymbolicStore] = {
    val res = new SymbolicStore(functionDeclarations)
    for (i <- 0 until this.frames.size) {
      if (i < this.frames.size) {
        val thisFrame = this.frames(i)
        if (i < other.frames.size) {
          val otherFrame = this.frames(i)
          for (variable <- thisFrame.keys) {
            if (otherFrame.contains(variable)) {
              (thisFrame(variable), otherFrame(variable)) match {
                case (PointerVal(ptr1), PointerVal(ptr2)) => {
                  (storage.getVal(PointerVal(ptr1)), storage.getVal(PointerVal(ptr2))) match {
                    case (Some(val1), Some(val2)) if val1 == val2 =>
                      val addr = res.storage.getAddress
                      res.addVar(variable, addr)
                      res.updateRef(addr, val1)
                    case (Some(val1), Some(val2)) =>
                      val addr = res.storage.getAddress
                      res.addVar(variable, addr)
                      res.updateRef(addr, IteVal(val1, val2, pathCondition.expr, CodeLoc(0, 0)))
                    case _ => throw new Exception("this should never happen.")
                  }
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
        }
      }
    }
    Some(res)
  }

}

package microc.symbolic_execution

import microc.ast.Identifier
import microc.symbolic_execution.ExecutionException.errorUninitializedReference
import microc.symbolic_execution.Value.{NullRef, PointerVal, RefVal, SymbolicExpr, UninitializedRef, Val}

import scala.collection.mutable.ArrayBuffer

class SymbolicStore() {

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

  private var frames: List[Map[String, RefVal]] = List(Map.empty)

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

  def addNewVar(name: String): Unit = {
    val frame = frames.last
    frames = frames.dropRight(1)
    frames = frames.appended(frame.updated(name, storage.getAddress))
  }

  def findVar(name: String): Option[RefVal] = {
    for (frame <- frames.reverse) {
      if (frame.contains(name)) {
        return Some(frame(name))
      }
    }
    None
  }

  def getVal(ptr: PointerVal): Option[Val] = {
    storage.getVal(ptr)
  }

  def getValForId(id: Identifier): Val = {
    val t = findVar(id.name)
    t match {
      case Some(PointerVal(decl)) =>
        val e = storage.getVal(PointerVal(decl))
        e match {
          case Some(res) => res
          case None => throw errorUninitializedReference(id.loc)
        }
      case Some(NullRef) => throw errorUninitializedReference(id.loc)
      //case Some(e@SymbolicExpr(_, _)) => e
      case Some(_) => throw new Exception("Internal error")
      /*case None =>
        functionDeclarations.get(id.name) match {
          case Some(fun) => fun
          case None => throw new Exception("Unexpected input in interpreter. Semantic analyses does not work properly.")
        }*/

    }

  }

  def updateRef(ptr: PointerVal, v: Val): Unit = {
    storage.addVal(ptr, v)
  }

  def deepCopy(): SymbolicStore = {
    val res = new SymbolicStore()
    res.frames = List.empty
    for (frame <- this.frames) {
      res.frames = res.frames.appended(frame)
    }
    res.storage = this.storage.asInstanceOf[res.Storage].deepCopy()
    res
  }

}

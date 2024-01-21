package microc.interpreter

import microc.{ProgramException, ast}
import microc.ast._
import microc.cli.Reporter
import microc.util.CharacterSets.NL
import org.w3c.dom.NamedNodeMap

import java.io.{Reader, Writer}
import java.nio.CharBuffer
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer


case class ExecutionException(message: String, loc: Loc) extends ProgramException(message) {
  override def format(reporter: Reporter): String = reporter.formatError("execution", message, loc)
}

object ExecutionException {
  def errorMissingMainFunction(program: Program): ExecutionException =
    ExecutionException(s"Missing main function, declared functions are ${program.funs.map(_.name)}", program.loc)

  def errorIO(loc: Loc, cause: Throwable): ExecutionException =
    ExecutionException(s"I/O error ${cause.getMessage}", loc)

  def errorNonRecordFieldAccess(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-record ($value) field access", loc)

  def errorNonExistingFieldAccess(loc: Loc, rec: String, field: String): ExecutionException =
    ExecutionException(s"Non-existing field ($field) access in $rec", loc)

  def errorNullDereference(loc: Loc): ExecutionException =
    ExecutionException(s"Null-pointer pointer dereference", loc)

  def errorNonPointerDereference(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-pointer ($value) pointer dereference", loc)

  def errorNonIntCondition(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-integer ($value) condition guard", loc)

  def errorNonIntReturn(fun: FunDecl): ExecutionException =
    ExecutionException(s"Non-integer return from function ${fun.name}", fun.block.ret.expr.loc)

  def errorNonIntOutput(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-integer ($value) output", loc)

  def errorNonIntInput(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-integer ($value) input", loc)

  def errorNonIntArithmetics(loc: Loc): ExecutionException =
    ExecutionException(s"Non-integer arithmetic operation", loc)

  def errorUninitializedReference(loc: Loc): ExecutionException =
    ExecutionException(s"Uninitialized variable", loc)

  def errorNonFunctionApplication(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-function ($value) application", loc)

  def errorRecordNestedFields(loc: Loc): ExecutionException =
    ExecutionException("Nested records are not supported, use pointers", loc)

  def errorNotAssignableExpression(expr: Expr): ExecutionException =
    ExecutionException(s"Expression is not assignable ($expr)", expr.loc)

  def errorInvalidArgumentList(loc: Loc, fun: FunDecl, actual: Int): ExecutionException =
    ExecutionException(s"Invalid argument list: expected ${fun.params.size}, got: $actual", loc)

  def errorDivByZero(loc: Loc): ExecutionException =
    ExecutionException(s"Division by zero", loc)

}

/** Values in microc programs
 */
object Value {

  sealed trait Val

  class RefVal() extends Val {
    override def toString: String = s"<pointer ${hashCode()}>"
  }

  def errorIncompatibleTypes(loc: Loc, left: String, right: String): ExecutionException =
    ExecutionException(s"Incompatible types, cannot assign $right into $left", loc)

  object UninitializedRef extends RefVal {

  }

  case class PointerVal(address: Int) extends RefVal {

  }

  case object ReturnRef extends RefVal {
    override def toString: String = "return"
  }

  case class IntVal(value: Int) extends Val {
    override def toString: String = value.toString
  }

  object NullRef extends RefVal {
    override def toString: String = "null"
  }

  case class RecVal(fields: mutable.Map[String, Val]) extends Val {
    override def toString: String = fields.map { case (k, v) => s"$k:$v" }.mkString("{", ",", "}")
  }


  case class FunVal(fun: FunDecl) extends Val

  def errorNonArrayAccess(loc: Loc, value: String): ExecutionException =
    ExecutionException(s"Non-array ($value) element access", loc)
}

trait Interpreter {

  /** Interprets a program
   *
   * @param mainArgs
   *   the arguments to the main function
   * @return
   *   the result of the main function
   */
  def run(mainArgs: List[Int]): Int
}


class MicroCInterpreter(program: Program, stdin: Reader, stdout: Writer, ascii: Boolean) extends Interpreter {


  import Value._
  import ExecutionException._

  private case class Storage() {
    var size: Int = 0

    var memory: ArrayBuffer[Val] = ArrayBuffer()

    def getAddress: PointerVal = {
      val res = PointerVal(size)
      size += 1
      memory += UninitializedRef
      res
    }

    def getVal(ptr: PointerVal): Option[Val] = {
      if (memory.size <= ptr.address)
        None
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


  private case class StackFrames(storage: Storage) {

    private var frames: List[mutable.Map[String, RefVal]] = List(mutable.Map.empty)

    def push(): Unit = frames = frames.appended(mutable.Map.empty)

    def pop(): Unit = {
      for (value <- frames.last.values) {
        value match {
          case PointerVal(address) => storage.deleteVal(PointerVal(address))
        }
      }
      frames = frames.dropRight(1)
    }

    def add(name: String, ref: RefVal): Unit = frames.last.update(name, ref)

    def find(name: String): Option[RefVal] = {
      for (frame <- frames.reverse) {
        if (frame.contains(name)) {
          return Some(frame(name))
        }
      }
      None
    }

    def globalFrame(): StackFrames = {
      var res = StackFrames(storage)
      res.frames = res.frames.appended(this.frames.head)
      res
    }
  }


  /** Interprets a program
   *
   * @param mainArgs
   * the arguments to the main function
   * @return
   * the result of the main function
   */

  private var functionDeclarations: Map[String, FunVal] = Map.empty
  private var storage: Storage = Storage()


  override def run(mainArgs: List[Int]): Int = {
    val main = program.funs.find(fun => fun.name == "main").getOrElse(throw errorMissingMainFunction(program))
    if (main.params.size != mainArgs.size) {
      throw errorInvalidArgumentList(main.loc, main, mainArgs.size)
    }
    var i = 0
    var stackFrames: StackFrames = StackFrames(storage)
    while (i < mainArgs.size) {
      val ptr = storage.getAddress
      storage.addVal(ptr, IntVal(mainArgs(i)))
      stackFrames.add(main.params(i).name, ptr)
      i += 1
    }
    val l = interpretNode(program, stackFrames)
    l match {
      case IntVal(value) => value
      case _ => throw errorNonIntReturn(main)
    }
  }


  private def getTarget(expr: Expr, stackFrames: StackFrames): PointerVal = {
    expr match {
      case Deref(pointer, loc) =>
        storage.getVal(
          getTarget(pointer, stackFrames)
        ) match {
          case Some(PointerVal(address)) => PointerVal(address)
          case Some(NullRef) => throw errorNullDereference(loc)
          case Some(v) => throw errorNonPointerDereference(pointer.loc, v.toString)
          case None => throw errorUninitializedReference(pointer.loc)
        }
      case Identifier(name, loc) =>
        stackFrames.find(name) match {
          case Some(PointerVal(address)) => PointerVal(address)
          case _ if functionDeclarations.contains(name) => throw errorNonPointerDereference(loc, functionDeclarations(name).toString)
          case _ => throw errorUninitializedReference(loc)
        }
      case e => throw errorNotAssignableExpression(e)
    }
  }

  private def copyVal(value: Val, loc: Loc): Val = {
    value match {
      case RecVal(_) => throw errorRecordNestedFields(loc)
      case IntVal(value) => IntVal(value).copy()
      case PointerVal(address) => PointerVal(address).copy()
      case v => v
    }
  }


  private def interpretNode(astNode: AstNode, stackFrames: StackFrames): Val = {
    astNode match {
      case Program(_, _) =>
        for (fun <- program.funs) {
          if (fun.name == "main") {
            return interpretNode(fun, stackFrames)
          }
          else {
            functionDeclarations = functionDeclarations.updated(fun.name, FunVal(fun))
          }
        }
        throw errorMissingMainFunction(program)
      case FunDecl(_, _, block, _) => interpretNode(block, stackFrames)
      case FunBlockStmt(vars, stmts, ret, _) =>
        vars.foreach(v => interpretNode(v, stackFrames))
        stmts.foreach(v => interpretNode(v, stackFrames))
        interpretNode(ret, stackFrames)
      case ReturnStmt(expr, _) => interpretNode(expr, stackFrames)
      case Number(value, _) => IntVal(value)
      case BinaryOp(operator, left, right, loc) =>
        IntVal(
          (operator, interpretNode(left, stackFrames), interpretNode(right, stackFrames)) match {
            case (_, IntVal(value1), IntVal(value2)) =>
              (operator, value1, value2) match {
                case (Plus, value1, value2) => value1 + value2
                case (Minus, value1, value2) => value1 - value2
                case (Times, value1, value2) => value1 * value2
                case (Divide, _, 0) => throw errorDivByZero(loc)
                case (Divide, value1, value2) => value1 / value2
                case (Equal, value1, value2) => if (value1 == value2) 1 else 0
                case (GreatThan, value1, value2) => if (value1 > value2) 1 else 0
                case (_, _, _) => throw errorNonIntArithmetics(loc)
              }
            case (Equal, NullRef, NullRef) => 1
            case (Equal, PointerVal(address1), PointerVal(address2)) => if (address1.equals(address2)) 1 else 0
            case (Equal, PointerVal(_), NullRef) => 0
            case (Equal, NullRef, PointerVal(_)) => 0
            case (_, _, _) => throw errorNonIntArithmetics(loc)
          })
      case CallFuncExpr(targetFun, args, loc) =>
        val fceArgs = args.map(arg => interpretNode(arg, stackFrames))
        interpretNode(targetFun, stackFrames) match {
          case FunVal(fce) =>
            if (fce.params.size != fceArgs.size) {
              throw errorInvalidArgumentList(loc, fce, fceArgs.size)
            }
            var i = 0
            val newStackFrames = StackFrames(storage)
            while (i < fceArgs.size) {
              val ptr = storage.getAddress
              storage.addVal(ptr, interpretNode(args(i), stackFrames))
              newStackFrames.add(fce.params(i).name, ptr)
              i += 1
            }
            interpretNode(fce, newStackFrames)
          case v => throw errorNonFunctionApplication(loc, v.toString)
        }
      case AssignStmt(FieldAccess(record, field, loc), right, _) =>
        val assigned = interpretNode(right, stackFrames)
        interpretNode(record, stackFrames) match {
          case RecVal(fields) if fields.contains(field) => fields.update(field, assigned)
          case RecVal(fields) => throw errorNonExistingFieldAccess(loc, RecVal(fields).toString, field)
          case _ => throw errorNotAssignableExpression(record)
        }
        NullRef
      case AssignStmt(left: Expr, right: Expr, loc: Loc) =>
        val ptr = getTarget(left, stackFrames)
        val assigned = interpretNode(right, stackFrames)
        assigned match {
          case RecVal(fields) =>
            val newRec = RecVal(
              fields.map {
                case (k, v) => k -> copyVal(v, loc)
              }
            )
            storage.addVal(ptr, newRec)
          case _ => storage.addVal(ptr, assigned)
        }
        NullRef
      case Alloc(expr, _) =>
        val ptr = storage.getAddress
        storage.addVal(ptr, interpretNode(expr, stackFrames))
        ptr
      case Deref(pointer, loc) =>
        interpretNode(pointer, stackFrames) match {
          case PointerVal(address) =>
            storage.getVal(PointerVal(address)) match {
              case Some(ret) => ret
              case None => throw new Exception("Internal error")
            }
          case NullRef => throw errorNullDereference(loc)
          case v => throw errorNonPointerDereference(pointer.loc, v.toString)
        }
      case FieldAccess(record, field, loc) =>
        interpretNode(record, stackFrames) match {
          case RecVal(fields) =>
            fields.get(field) match {
              case Some(res) => res
              case None => throw errorNonExistingFieldAccess(loc, RecVal(fields).toString, field)
            }
          case v => throw errorNonRecordFieldAccess(loc, v.toString)
        }
      case Identifier(name, loc) =>
        stackFrames.find(name) match {
          case Some(PointerVal(decl)) =>
            storage.getVal(PointerVal(decl)) match {
              case Some(res) => res
              case None => throw errorUninitializedReference(loc)
            }
          case Some(NullRef) => throw errorUninitializedReference(loc)
          case Some(_) => throw new Exception("Internal error")
          case None =>
            functionDeclarations.get(name) match {
              case Some(fun) => fun
              case None => throw new Exception("Unexpected input in interpreter. Semantic analyses does not work properly.")
            }
        }
      case IdentifierDecl(name, loc) =>
        stackFrames.add(name, storage.getAddress)
        NullRef
      case IfStmt(guard, thenBranch, elseBranch, loc) =>
        val evaluatedGuard = interpretNode(guard, stackFrames)
        evaluatedGuard match {
          case IntVal(0) => elseBranch match {
            case Some(value) => interpretNode(value, stackFrames)
            case None => NullRef
          }
          case IntVal(_) => interpretNode(thenBranch, stackFrames)
          case _ => throw errorNonIntCondition(loc, evaluatedGuard.toString)
        }
      case Input(loc) =>/*
        if (ascii) {
          val readArr = Array.fill(7)(0): Array[Char]
          stdin.read(readArr)
          var res = 0
          var curr = 0
          var tmp = readArr(curr)
          if (tmp == 0) {
            return IntVal(-1)
          }
          while (tmp >= '0' && tmp <= '9') {
            res *= 10
            res += tmp - '0'
            curr += 1
            tmp = readArr(curr)
          }
          return IntVal(res)
        }
        var tmp = stdin.read()
        if (tmp == -1) {
          return IntVal(-1)
        }
        var res = 0
        while (tmp >= '0' && tmp <= '9') {
          res *= 10
          res += tmp - '0'
          tmp = stdin.read()
        }
        if (res == 0) {
          throw errorNonIntInput(loc, tmp.toString)
        }*/
        IntVal(0)
      case NestedBlockStmt(body, _) =>
        stackFrames.push()
        body.foreach(stmt => interpretNode(stmt, stackFrames))
        stackFrames.pop()
        NullRef
      case Null(_) => NullRef
      case OutputStmt(expr, loc) =>
        /*val r = interpretNode(expr, stackFrames)
        r match {
          case IntVal(value) =>
            if (ascii) {
              val vCopy = value.toString
              val writeArr = Array.fill(vCopy.length + 1)('\n'): Array[Char]
              var curr = 0
              for (ch <- vCopy) {
                writeArr.update(curr, ch)
                curr += 1
              }
              stdout.write(writeArr, 0, writeArr.length)
            }
            else {
              stdout.write(r.toString)
              stdout.write(NL)
            }
          case v => throw errorNonIntOutput(loc, v.toString)
        }*/
        NullRef
      case Record(fields, _) =>
        val fieldsMap: mutable.Map[String, Val] = mutable.Map.empty
        fields.foreach(field =>
          interpretNode(field, stackFrames) match {
            case RecVal(_) => throw errorRecordNestedFields(field.expr.loc)
            case res => fieldsMap.update(field.name, res)
          }
        )
        RecVal(fieldsMap)
      case RecordField(_, expr, _) => interpretNode(expr, stackFrames)
      case VarRef(id, _) => stackFrames.find(id.name).get
      case VarStmt(decls, _) =>
        decls.foreach(decl => interpretNode(decl, stackFrames))
        NullRef
      case WhileStmt(guard, block, _) =>
        while (true) {
          val cond = interpretNode(guard, stackFrames)
          cond match {
            case IntVal(0) =>
              return NullRef
            case _ => interpretNode(block, stackFrames)
          }
        }
        NullRef
    }
  }
}

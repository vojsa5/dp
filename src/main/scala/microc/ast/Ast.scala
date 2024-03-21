package microc.ast

import microc.symbolic_execution.Value
import microc.symbolic_execution.Value.Symbolic

trait Loc extends Ordered[Loc] {
  def line: Int
  def col: Int

  override def toString: String = s"$line:$col"
}

/** A source code location of an AST node.
  *
  * @param line
  *   The line number.
  * @param col
  *   The column number.
  */
case class CodeLoc(line: Int, col: Int) extends Loc {
  override def toString: String = s"$line:$col"

  override def compare(that: Loc): Int = {
    val d = this.line - that.line
    if (d == 0) this.col - that.col else d
  }
}

/** A binary operator */
sealed trait BinaryOperator

object BinaryOperator {
  def apply(s: String): BinaryOperator = s match {
    case "+"  => Plus
    case "-"  => Minus
    case "*"  => Times
    case "/"  => Divide
    case "!=" => NotEqual
    case "==" => Equal
    case ">"  => GreaterThan
    case "<"  => LowerThan
    case ">="  => GreaterEqual
    case "<="  => LowerEqual
    case "&&" => AndAnd
    case "||" => OrOr
  }
}

case object Plus extends BinaryOperator {
  override def toString: String = "+"
}

case object Minus extends BinaryOperator {
  override def toString: String = "-"
}

case object Times extends BinaryOperator {
  override def toString: String = "*"
}

case object Divide extends BinaryOperator {
  override def toString: String = "/"
}

case object Equal extends BinaryOperator {
  override def toString: String = "=="
}

case object NotEqual extends BinaryOperator {
  override def toString: String = "!="
}

case object GreaterThan extends BinaryOperator {
  override def toString: String = ">"
}

case object LowerThan extends BinaryOperator {
  override def toString: String = "<"
}

case object GreaterEqual extends BinaryOperator {
  override def toString: String = ">="
}

case object LowerEqual extends BinaryOperator {
  override def toString: String = "<="
}

case object AndAnd extends BinaryOperator {
  override def toString: String = "&&"
}

case object OrOr extends BinaryOperator {
  override def toString: String = "||"
}

// ----------------------------------------------------------------------------
// BASE NODES
// ----------------------------------------------------------------------------

object AstNode {
  private val Printer = new AstPrinter()
}

/** An AST node
  */
abstract class AstNode extends Ordered[AstNode] {

  /** The source code location of the AST node.
    *
    * @return
    *   a source code location.
    */
  def loc: Loc

  def children: Iterable[AstNode] = Iterable.empty

  def tree: Iterable[AstNode] = Iterable(this) ++ children.flatMap(_.tree)

  override def toString: String = {
    AstNode.Printer.print(this) + s"[$loc]"
  }

  override def compare(that: AstNode): Int = this.loc.compare(that.loc)
}

trait Expr extends AstNode {
  def equals(other: Expr): Boolean
}

sealed trait Stmt extends AstNode

sealed trait Decl extends AstNode {
  def name: String
}

/** A statement in a nested block.
  *
  * It cannot be a declaration or a return.
  */
sealed trait StmtInNestedBlock extends Stmt

// ----------------------------------------------------------------------------
// EXPRESSIONS
// ----------------------------------------------------------------------------

case class Null(loc: Loc) extends Expr with Symbolic {

  override def equals(other: Expr): Boolean =
    other match {
      case Null(_) => true
      case _ => false
    }

  override def equalsVal(other: Value.Val): Boolean =
    other match {
      case Null(_) => true
      case _ => false
    }
}

case class Number(value: Int, loc: Loc) extends Expr with Symbolic {
  override def equals(other: Expr): Boolean =
    other match {
      case Number(val2, _) => val2 == value
      case _ => false
    }

  override def equalsVal(other: Value.Val): Boolean =
    other match {
      case Number(val2, _) => val2 == value
      case _ => false
    }
}

case class Identifier(name: String, loc: Loc) extends Expr {
  override def equals(other: Expr): Boolean =
    other match {
      case Identifier(name2, _) => name == name2
      case _ => false
    }
}

case class BinaryOp(operator: BinaryOperator, left: Expr, right: Expr, loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = List(left, right)
  override def toString: String = s"($left $operator $right)"

  override def equals(other: Expr): Boolean =
    other match {
      case BinaryOp(operator2, left2, right2, _) => operator == operator2 && left.equals(left2) && right.equals(right2)
      case _ => false
    }
}

case class CallFuncExpr(targetFun: Expr, args: List[Expr], loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = targetFun :: args

  override def equals(other: Expr): Boolean =
    other match {
      case CallFuncExpr(fun2, args2, _) =>
        if (args.size == args2.size) {
          for (i <- args.indices) {
            if (!args(i).equals(args2(i))) {
              return false
            }
          }
          return targetFun.equals(fun2)
        }
        false
      case _ => false
    }
}

/** Read of one integer from standard input.
  *
  * @param loc
  *   The source code location.
  */
case class Input(loc: Loc) extends Expr {
  override def equals(other: Expr): Boolean =
    other match {
      case Input(_) => true
      case _ => false
    }
}

case class Alloc(expr: Expr, loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = List(expr)

  override def equals(other: Expr): Boolean =
    other match {
      case Alloc(expr2, _) => expr.equals(expr2)
      case _ => false
    }
}

/** Variable reference.
  *
  * It is used to create a pointer to a variable `id` (&id).
  *
  * @param id
  *   The target variable.
  * @param loc
  *   The source code location.
  */
case class VarRef(id: Identifier, loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = List(id)

  override def equals(other: Expr): Boolean =
    other match {
      case VarRef(id2, _) => id.equals(id2)
      case _ => false
    }
}

/** Pointer dereference
  *
  * It is used to dereference a pointer `p` (`*p`).
  *
  * @param pointer
  *   The pointer to dereference
  * @param loc
  *   The source code location
  */
case class Not(expr: Expr, loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = List(expr)
  override def toString: String = s"!$expr"

  override def equals(other: Expr): Boolean =
    other match {
      case Not(expr2, _) => expr.equals(expr2)
      case _ => false
    }
}

case class Deref(pointer: Expr, loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = List(pointer)

  override def equals(other: Expr): Boolean =
    other match {
      case Deref(pointer2, _) => pointer.equals(pointer2)
      case _ => false
    }
}

case class Record(fields: List[RecordField], loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = fields

  override def equals(other: Expr): Boolean =
    other match {
      case Record(fields2, _) => {
        if (fields.size == fields2.size) {
          for (i <- fields.indices) {
            val f1 = fields(i)
            val f2 = fields2(i)
            if (!f1.expr.equals(f2.expr) || f1.name != f2.name) {
              return false
            }
          }
          return true
        }
        false
      }
      case _ => false
    }
}

case class RecordField(name: String, expr: Expr, loc: Loc) extends AstNode {
  override def children: Iterable[AstNode] = List(expr)
}

/** Accessing a field of a record (x.y).
  *
  * @param record
  *   The expression that evaluates to a record value.
  * @param field
  *   The name of the field of the record.
  * @param loc
  *   The source code location.
  */
case class FieldAccess(record: Expr, field: String, loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = List(record)

  override def equals(other: Expr): Boolean = {
    other match {
      case FieldAccess(record2, field2, _) => record.equals(record2) && field == field2
      case _ => false
    }
  }
}

case class ArrayNode(elems: List[Expr], loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = elems

  override def equals(other: Expr): Boolean =
    other match {
      case ArrayNode(elems2, _) => {
        if (elems.size == elems2.size) {
          for (i <- elems.indices) {
            if (!elems(i).equals(elems2(i))) {
              return false
            }
          }
          return true
        }
        false
      }
      case _ => false
    }
}

case class ArrayAccess(array: Expr, index: Expr, loc: Loc) extends Expr {
  override def children: Iterable[AstNode] = List(array, index)

  override def equals(other: Expr): Boolean =
    other match {
      case ArrayAccess(array2, index2, _) => array.equals(array2) && index.equals(index2)
      case _ => false
    }
}

// ----------------------------------------------------------------------------
// STATEMENTS
// ----------------------------------------------------------------------------

/** An Assignment.
  *
  * @param left
  *   The LValue (where to assign)
  * @param right
  *   The RValue (what to assign)
  * @param loc
  *   The source code location
  */
case class AssignStmt(left: Expr, right: Expr, loc: Loc) extends StmtInNestedBlock {
  override def children: Iterable[AstNode] = List(left, right)
}

case object DirectWrite {
  def unapply(expr: Expr): Option[Identifier] = expr match {
    case x: Identifier => Some(x)
    case _             => None
  }
}

case object IndirectWrite {
  def unapply(expr: Expr): Option[Deref] = expr match {
    case x: Deref => Some(x)
    case _        => None
  }
}

case object DirectFieldWrite {
  def unapply(expr: Expr): Option[(Identifier, String, Loc)] = expr match {
    case FieldAccess(record: Identifier, field, loc) => Some((record, field, loc))
    case _                                           => None
  }
}

case object IndirectFieldWrite {
  def unapply(expr: Expr): Option[(Deref, String, Loc)] = expr match {
    case FieldAccess(record: Deref, field, loc) => Some((record, field, loc))
    case _                                      => None
  }
}

case object ArrayWrite {
  def unapply(expr: Expr): Option[(Expr, Expr, Loc)] = expr match {
    case ArrayAccess(array, index, loc) => Some((array, index, loc))
    case _                              => None
  }
}

sealed trait Block extends Stmt {
  def body: List[Stmt]

  override def children: Iterable[AstNode] = body
}

object Block {
  def unapply(that: Block): Option[List[Stmt]] = Some(that.body)
}

/** Represents a block of statements surrounded by curly braces.
  *
  * {{{
  * {
  *   stmt_1
  *   stmt_2
  *   ...
  *   stmt_n
  * }
  * }}}
  *
  * @param body
  *   The list of statements in this block
  * @param loc
  *   The location
  */
case class NestedBlockStmt(body: List[StmtInNestedBlock], loc: Loc) extends Block with StmtInNestedBlock

case class FunBlockStmt(vars: List[VarStmt], stmts: List[StmtInNestedBlock], ret: ReturnStmt, loc: Loc) extends Block {
  val body: List[Stmt] = vars ++ (stmts :+ ret)
}

case class ReturnStmt(expr: Expr, loc: Loc) extends Stmt {
  override def children: Iterable[AstNode] = List(expr)
}

case class IfStmt(guard: Expr, thenBranch: StmtInNestedBlock, elseBranch: Option[StmtInNestedBlock], loc: Loc)
    extends StmtInNestedBlock {
  override def children: Iterable[AstNode] = guard :: thenBranch :: elseBranch.map(x => List(x)).getOrElse(Nil)
}

case class WhileStmt(guard: Expr, block: StmtInNestedBlock, loc: Loc) extends StmtInNestedBlock {
  override def children: Iterable[AstNode] = List(guard, block)
}

case class OutputStmt(expr: Expr, loc: Loc) extends StmtInNestedBlock {
  override def children: Iterable[AstNode] = List(expr)
}

/** Function local variables declaration.
  *
  * @param decls
  *   The list of variable declarations.
  * @param loc
  *   The source code location.
  */
case class VarStmt(decls: List[IdentifierDecl], loc: Loc) extends Stmt {
  override def children: Iterable[AstNode] = decls
}

case class AddConditionStatement(condition: Expr, loc: Loc) extends Stmt {
  override def children: Iterable[AstNode] = List(condition)
  override def toString: String = condition.toString + loc.toString
}

case class IdentifierDecl(name: String, loc: Loc) extends Decl

case class FunDecl(name: String, params: List[IdentifierDecl], block: FunBlockStmt, loc: Loc) extends Decl {
  override def toString: String = s"$name(${params.mkString(",")}){...}:$loc"

  override def children: Iterable[AstNode] = params :+ block
}

/** The complete program.
  *
  * A program is just a list of functions. The `main` function is where the execution begins.
  *
  * @param funs
  *   The list of functions.
  * @param loc
  *   The source code location.
  */
case class Program(funs: List[FunDecl], loc: Loc) extends AstNode {
  def mainFunOption: Option[FunDecl] =
    funs.find(_.name == "main")

  override def children: Iterable[AstNode] = funs

  def declarations: Iterable[Decl] = tree.collect { case x: Decl => x }
}

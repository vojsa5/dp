package microc.analysis

import microc.ProgramException
import microc.ast.{Alloc, ArrayWrite, AssignStmt, AstNode, BinaryOp, CallFuncExpr, Decl, Deref, DirectFieldWrite, DirectWrite, Divide, Equal, Expr, FieldAccess, FunBlockStmt, FunDecl, Identifier, IdentifierDecl, IfStmt, IndirectFieldWrite, IndirectWrite, Input, Loc, Minus, NestedBlockStmt, Null, Number, OutputStmt, Plus, Program, Record, RecordField, ReturnStmt, Times, VarRef, VarStmt, WhileStmt}
import microc.cli.Reporter
import microc.util.CharacterSets.NL

import scala.collection.immutable.{Iterable, Map, Set}
import scala.collection.mutable

case class SemanticError(msg: String, loc: Loc)

case class SemanticException(errors: List[SemanticError])
  extends ProgramException("Semantic errors: " + errors.mkString("\n")) {

  override def format(reporter: Reporter): String =
    errors.sortBy(_.loc).map(x => reporter.formatError("semantic", x.msg, x.loc)).mkString(NL)
}

/** Semantic analysis for μC.
 *
 * It checks the following:
 *   - Use of an undeclared identifier.
 *   - Duplicate identifiers. note: there is a single namespace (shared by both functions and identifiers)
 *   - Duplicate record field names.
 *   - Assignment to a function.
 *   - Getting address of a function.
 *
 * The result is a map of declarations, i.e., a map of identifiers to their declarations.
 */
class SemanticAnalysis {
  type Env = Map[String, Decl]

  def analyze(program: Program): Declarations = {
    val visitor = new DeclarationVisitor()
    visitor.visit(program, Map.empty)

    if (visitor.errors.isEmpty) {
      visitor.declarations.toMap
    } else {
      throw SemanticException(visitor.errors.toList)
    }
  }

  class DeclarationVisitor {
    val declarations = mutable.Map[Identifier, Decl]()
    val errors = mutable.Buffer[SemanticError]()

    def visit(node: AstNode, env: Env): Unit = {
      node match {
        case Program(funs, _) =>
          val extended = extendEnv(env, funs)
          visitChildren(node, extended)

        case FunDecl(_, params, body, _) =>
          val extended = extendEnv(env, params)
          visitChildren(node, extended)

        case FunBlockStmt(vars, stmts, ret, _) =>
          val extended = extendEnv(env, vars.flatMap(_.decls))
          visitChildren(node, extended)

        case ident @ Identifier(name, loc) =>
          env.get(name) match {
            case Some(decl) => declarations += (ident -> decl)
            case None       => errors += SemanticError(s"identifier '$name' not declared", loc)
          }

        case VarRef(id, loc) =>
          env.get(id.name) match {
            case Some(_: FunDecl) =>
              errors += SemanticError(s"cannot take an address of a function", loc)
            case _ => visit(id, env)
          }

        case AssignStmt(left, _, loc) =>
          left match {
            case DirectFieldWrite(_, _, _)   => // OK
            case IndirectFieldWrite(_, _, _) => // OK
            case ArrayWrite(_, _, _)         => // OK
            case IndirectWrite(_)            => // OK
            case DirectWrite(Identifier(name, _)) =>
              env.get(name) match {
                case Some(_: FunDecl) => errors += SemanticError(s"cannot assign to a function", loc)
                case _                =>
              }
            case _ => // anything else is NOT-OK
              errors += SemanticError(s"cannot assign into rvalue $left", loc)
          }
          visitChildren(node, env)

        case Record(fields, _) =>
          fields.foldLeft(Set[String]()) { (acc, f) =>
            if (acc.contains(f.name))
              errors += SemanticError(s"duplicate field name '${f.name}'", f.loc)
            acc + f.name
          }
          visitChildren(node, env)

        case RecordField(_, _: Record, loc) =>
          errors += SemanticError("nested record are not allowed", loc)
          visitChildren(node, env)

        case _ =>
          visitChildren(node, env)
      }
    }

    private def visitChildren(node: AstNode, env: Env): Unit = node.children.foreach(visit(_, env))

    private def extendEnv(env: Env, decls: Iterable[_ <: Decl]): Env =
      decls.foldLeft(env) { (acc, d) =>
        acc.get(d.name) match {
          case Some(x) =>
            errors += SemanticError(s"identifier '${d.name}' already declared (${x.loc})", d.loc)
            acc
          case None =>
            acc + (d.name -> d)
        }
      }
  }
}

package microc.symbolic_execution

import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, BinaryOp, CallFuncExpr, Decl, Divide, Equal, Expr, GreaterEqual, GreaterThan, Identifier, IfStmt, Input, LowerEqual, LowerThan, Minus, Not, NotEqual, Null, Number, OrOr, OutputStmt, Plus, ReturnStmt, Stmt, Times, WhileStmt}

import scala.util.Random

object Utility {
  def varIsFromOriginalProgram(name: String): Boolean = {
    !(name.length > 2 && name(0) == '_' && name(1) == 't')
  }

  def generateRandomString(): String = {
    (1 to 10).map(_ => "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"(new Random().nextInt(52))).mkString
  }

  def containsUnpredictability(expr: Expr): Boolean = {
    expr match {
      case BinaryOp(operator, left, right, loc) => containsUnpredictability(left) || containsUnpredictability(right)
      case Not(expr, loc) => containsUnpredictability(expr)
      case Alloc(expr, loc) => containsUnpredictability(expr)
      case Input(loc) => true
      case CallFuncExpr(targetFun, args, loc) => true
      case Identifier(name, loc) => true
      case Number(value, loc) => false
      case Null(loc) => false
    }
  }

//  def getCountOfPotentialErrors(expr: Expr): Int = {
//    expr match {
//      case BinaryOp(Divide, left, right, _) =>
//        getCountOfPotentialErrors(left) + getCountOfPotentialErrors(right)+ (if (Utility.expressionCanCauseError(right)) 1 else 0)
//      case BinaryOp(_, left, right, _) => getCountOfPotentialErrors(left) + getCountOfPotentialErrors(right)
//      case Not(expr, _) => getCountOfPotentialErrors(expr)
//      case Alloc(expr, _) => getCountOfPotentialErrors(expr)
//      case Input(_) => 0
//      case CallFuncExpr(targetFun, args, loc) => ???
//      case Identifier(name, loc) => 0
//      case Number(value, loc) => 0
//      case Null(_) => 0
//    }
//  }

  def expressionCanCauseError(expr: Expr): Boolean = {
    expr match {
      case BinaryOp(Divide, left, right, _) => containsUnpredictability(right) || expressionCanCauseError(left) || expressionCanCauseError(right)
      case BinaryOp(_, left, right, _) => expressionCanCauseError(left) || expressionCanCauseError(right)
      case Not(expr, _) => expressionCanCauseError(expr)
      case Alloc(expr, _) => expressionCanCauseError(expr)
      case Input(_) => false
      case CallFuncExpr(targetFun, args, loc) => false//TODO
      case Identifier(_, _) => false
      case Number(_, _) => false
      case Null(_) => false
      case ArrayNode(elems, _) => elems.exists(elem => expressionCanCauseError(elem))
      case ArrayAccess(array, index, _) => expressionCanCauseError(array) || expressionCanCauseError(index) || containsUnpredictability(index)
      case _ => false
    }
  }

  def statementCanCauseError(stmt: Stmt): Boolean = {
      stmt match {
        case OutputStmt(expr, _) => expressionCanCauseError(expr)
        case ReturnStmt(expr, _) => expressionCanCauseError(expr)
        case IfStmt(expr, _, _, _) => expressionCanCauseError(expr)
        case WhileStmt(expr, _, _) => expressionCanCauseError(expr)
        case AssignStmt(_, right, _) => expressionCanCauseError(right)
      }
  }

  def getIdentifiersThatCanCauseError(expr: Expr): Set[Identifier] = {
    expr match {
      case BinaryOp(Divide, left, right, _) => getAllIdentifierNames(right)  ++ getIdentifiersThatCanCauseError(right)
      case BinaryOp(_, left, right, _) => getIdentifiersThatCanCauseError(left) ++ getIdentifiersThatCanCauseError(right)
      case Not(expr, _) => getIdentifiersThatCanCauseError(expr)
      case Alloc(expr, _) => getIdentifiersThatCanCauseError(expr)
      case Input(_) => Set.empty
      case CallFuncExpr(targetFun, args, loc) => args.flatMap(arg => getAllIdentifierNames(arg)).toSet
      case Identifier(_, _) => Set.empty
      case Number(_, _) => Set.empty
      case Null(_) => Set.empty
      case ArrayNode(elems, _) => elems.flatMap(elem => getIdentifiersThatCanCauseError(elem)).toSet
      case ArrayAccess(array, index, _) => getAllIdentifierNames(array) ++ getAllIdentifierNames(index)
      case _ => Set.empty
    }
  }


  def getAllIdentifierNames(node: Expr): Set[Identifier] = {
    node match {
      case id@Identifier(_, _) => Set(id)
      case BinaryOp(_, left, right, _) => getAllIdentifierNames(left) ++ getAllIdentifierNames(right)
      case Number(value, loc) => Set.empty
      case ArrayNode(elems, loc) => elems.flatMap(elem => getAllIdentifierNames(elem)).toSet
      case i@Input(_) => Set.empty
      case ArrayAccess(array, index, loc) => getAllIdentifierNames(array) ++ getAllIdentifierNames(index)
      case _ => Set.empty
    }
  }

  def simplifyArithExpr(expr: Expr): Expr = {//TODO if changed, repeat
    var res = expr match {
      case n@Number(_, _) => n
      case BinaryOp(AndAnd, Number(1, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(OrOr, Number(0, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(AndAnd, expr, Number(1, _), _) => simplifyArithExpr(expr)
      case BinaryOp(OrOr, expr, Number(0, _), _) => simplifyArithExpr(expr)
      case BinaryOp(AndAnd, expr1, expr2, _) if expr1 == expr2 => simplifyArithExpr(expr1)
      case BinaryOp(OrOr, expr1, expr2, _) if expr1 == expr2 => simplifyArithExpr(expr1)
      case BinaryOp(Plus, expr, Number(0, _), _) => simplifyArithExpr(expr)
      case BinaryOp(Times, expr, Number(1, _), _) => simplifyArithExpr(expr)
      case BinaryOp(Plus, Number(0, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(Times, Number(1, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(OrOr, Not(expr1, _), expr2, loc) if expr1 == expr2 => Number(1, loc)
      case BinaryOp(OrOr, expr1, Not(expr2, _), loc) if expr1 == expr2 => Number(1, loc)
      case BinaryOp(operator, left, right, loc) =>
        (simplifyArithExpr(left), simplifyArithExpr(right)) match {
          case (Number(value, loc), Number(value2, _)) =>
            operator match {
              case Plus => Number(value + value2, loc)
              case Minus => Number(value - value2, loc)
              case Times => Number(value * value2, loc)
              case Divide => Number(value / value2, loc)
              case LowerThan => Number(if (value < value2) 1 else 0, loc)
              case LowerEqual => Number(if (value <= value2) 1 else 0, loc)
              case GreaterThan => Number(if (value > value2) 1 else 0, loc)
              case GreaterEqual => Number(if (value >= value2) 1 else 0, loc)
              case NotEqual => Number(if (value != value2) 1 else 0, loc)
              case Equal => Number(if (value == value2) 1 else 0, loc)
              case AndAnd => Number(if (value != 0 && value2 != 0) 1 else 0, loc)
              case OrOr => Number(if (value != 0 || value2 != 0) 1 else 0, loc)
            }
          case (a, b) =>
            BinaryOp(operator, a, b, loc)
        }
      case other => other
    }
    if (res != expr) {
      res = simplifyArithExpr(res)
    }
    res
  }
}

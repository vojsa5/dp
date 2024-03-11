package microc.ast

import scala.collection.mutable.ListBuffer


class AstNormalizer {

  var universalsCnt = 1

  def createVar(vars: ListBuffer[IdentifierDecl], declaredVars: List[VarStmt], loc: Loc): Expr = {
    var name = "_t" + universalsCnt.toString
    var newDecl = IdentifierDecl(name, loc)
    while (declaredVars.exists(stmt => stmt.decls.exists(decl => decl.name == newDecl.name))) {
      universalsCnt += 1
      name = "_t" + universalsCnt.toString
      newDecl = IdentifierDecl(name, loc)
    }
    vars.append(newDecl)
    val rightSide: Expr = Identifier(name, loc)
    universalsCnt += 1
    rightSide
  }

  def getTarget(expr: Expr, newStmts: ListBuffer[StmtInNestedBlock], newVars: ListBuffer[IdentifierDecl], declaredVars: List[VarStmt]): Expr = {
    expr match {
      case Deref(FieldAccess(record, field, _), loc) =>
        val rightSide = createVar(newVars, declaredVars, loc)
        newStmts.append(AssignStmt(rightSide, FieldAccess(record, field, loc), loc))
        Deref(rightSide, loc)
      case Deref(pointer, loc) =>
        val pointerNormalized = getTarget(pointer, newStmts, newVars, declaredVars)
        val rightSide = createVar(newVars, declaredVars, loc)
        newStmts.append(AssignStmt(rightSide, Deref(pointerNormalized, loc), loc))
        rightSide
      case _ =>
        expr
    }
  }

  def normalize(program: Program): Program = {
    val newFuns: ListBuffer[FunDecl] = ListBuffer.empty
    for (fun <- program.funs) {
      val newVars: ListBuffer[IdentifierDecl] = ListBuffer.empty
      val newStmts: ListBuffer[StmtInNestedBlock] = ListBuffer.empty;
      for (stmt <- fun.block.stmts) {
        normalizeStatement(stmt, newStmts, newVars, fun.block.vars)
      }
      val ret: ReturnStmt = ReturnStmt(normalizeExpr(fun.block.ret.expr, newStmts, newVars, fun.block.vars), fun.block.ret.loc)
      var vars = fun.block.vars;
      val newVarsList = newVars.toList
      if (newVarsList.nonEmpty) {
        vars = vars.prepended(VarStmt(newVarsList, fun.loc))
      }
      newFuns.append(FunDecl(fun.name, fun.params, FunBlockStmt(vars, newStmts.toList, ret, fun.block.loc), fun.loc))
    }
    Program(newFuns.toList, program.loc)
  }


  def normalizeStatement(stmt: StmtInNestedBlock, stmts: ListBuffer[StmtInNestedBlock], vars: ListBuffer[IdentifierDecl], declaredVars: List[VarStmt]): Unit = {
      stmt match {
        case AssignStmt(left, right, loc) =>
          val newLeft: Expr = left match {
            case Deref(pointer, loc) => Deref(getTarget(pointer, stmts, vars, declaredVars), loc)
            case FieldAccess(record, field, loc) =>
              FieldAccess(getTarget(record, stmts, vars, declaredVars), field, loc)
            case left => left
          }
          normalizeAssign(newLeft, right, stmts, vars, declaredVars, loc)
        case OutputStmt(expr, loc) =>
          stmts.append(OutputStmt(normalizeExpr(expr, stmts, vars, declaredVars), loc))
        case IfStmt(guard, thenBranch, elseBranch, loc) =>
          var newStmts: ListBuffer[StmtInNestedBlock] = ListBuffer.empty
          val guardExpr: Expr = normalizeExpr(guard, stmts, vars, declaredVars)
          normalizeStatement(thenBranch, newStmts, vars, declaredVars)
          val thenBranchBlock = NestedBlockStmt(newStmts.toList, loc)
          val elseBranchBlock =
            elseBranch match {
              case Some(value) =>
                newStmts = ListBuffer.empty
                normalizeStatement(value, newStmts, vars, declaredVars)
                Some(NestedBlockStmt(newStmts.toList, loc))
              case None => None
            }
          stmts.append(IfStmt(guardExpr, thenBranchBlock, elseBranchBlock, loc))
        case WhileStmt(guard, block, loc) =>
          val guardStmts: ListBuffer[StmtInNestedBlock] = ListBuffer.empty
          val newStmts: ListBuffer[StmtInNestedBlock] = ListBuffer.empty
          val bodyStmts: ListBuffer[StmtInNestedBlock] = ListBuffer.empty
          val guardExpr: Expr = normalizeExpr(guard, guardStmts, vars, declaredVars)
          normalizeStatement(block, bodyStmts, vars, declaredVars)
          newStmts.appendAll(bodyStmts.toList)
          newStmts.appendAll(guardStmts)
          val loopBlock = NestedBlockStmt(newStmts.toList, loc)
          stmts.appendAll(guardStmts)
          stmts.append(WhileStmt(guardExpr, loopBlock, loc))
        case NestedBlockStmt(body, loc) =>
          for (stmt <- body) {
            normalizeStatement(stmt, stmts, vars, declaredVars)
          }
        case stmt =>
          stmts.append(stmt)
      }
  }


  def normalizeAssign(left: Expr, right: Expr, stmts: ListBuffer[StmtInNestedBlock], vars: ListBuffer[IdentifierDecl], declaredVars: List[VarStmt], loc: Loc) = {
    stmts.append(AssignStmt(left, normalizeAssigned(right, stmts, vars, declaredVars), loc))
  }


  def normalizeAssigned(assigned: Expr, stmts: ListBuffer[StmtInNestedBlock], vars: ListBuffer[IdentifierDecl], declaredVars: List[VarStmt]): Expr = {
    assigned match {
      case BinaryOp(operator, leftExpr, rightExpr, loc) =>
        BinaryOp(operator, normalizeExpr(leftExpr, stmts, vars, declaredVars), normalizeExpr(rightExpr, stmts, vars, declaredVars), loc)
      case Not(expr, loc) =>
        Not(normalizeExpr(expr, stmts, vars, declaredVars), loc)
      case CallFuncExpr(targetFun, args, loc) =>
        val targetNormalized = normalizeExpr(targetFun, stmts, vars, declaredVars)
        val argsNormalized = args.map(arg => normalizeExpr(arg, stmts, vars, declaredVars))
        CallFuncExpr(targetNormalized, argsNormalized, loc)
      case Deref(pointer, loc) =>
        Deref(normalizeExpr(pointer, stmts, vars, declaredVars), loc)
      case Alloc(expr, loc) =>
        Alloc(normalizeExpr(expr, stmts, vars, declaredVars), loc)
      case Record(fields, loc) =>
        Record(fields.map(field => RecordField(field.name, normalizeAssigned(field.expr, stmts, vars, declaredVars), field.loc)), loc)
      case _ =>
        assigned
    }
  }


  def normalizeExpr(node: Expr, stmts: ListBuffer[StmtInNestedBlock], vars: ListBuffer[IdentifierDecl], declaredVars: List[VarStmt]): Expr = {
    var rightSide: Expr = node
    node match {
      case BinaryOp(operator, left, right, loc) =>
        val leftNormalized = normalizeExpr(left, stmts, vars, declaredVars)
        val rightNormalized = normalizeExpr(right, stmts, vars, declaredVars)
        rightSide = createVar(vars, declaredVars, loc)
        stmts.append(AssignStmt(rightSide, BinaryOp(operator, leftNormalized, rightNormalized, loc), loc))
      case Not(expr, loc) =>
        val normalized = normalizeExpr(expr, stmts, vars, declaredVars)
        rightSide = createVar(vars, declaredVars, loc)
        stmts.append(AssignStmt(rightSide, Not(normalized, loc), loc))
      case CallFuncExpr(targetFun, args, loc) =>
        val targetNormalized = normalizeExpr(targetFun, stmts, vars, declaredVars)
        val argsNormalized = args.map(arg => normalizeExpr(arg, stmts, vars, declaredVars))
        rightSide = createVar(vars, declaredVars, loc)
        stmts.append(AssignStmt(rightSide, CallFuncExpr(targetNormalized, argsNormalized, loc), loc))
      case Deref(pointer, loc) =>
        val deref = normalizeExpr(pointer, stmts, vars, declaredVars)
        rightSide = createVar(vars, declaredVars, loc)
        stmts.append(AssignStmt(rightSide, Deref(deref, loc), loc))
      case Alloc(expr, loc) =>
        val alloc = normalizeExpr(expr, stmts, vars, declaredVars)
        rightSide = createVar(vars, declaredVars, loc)
        stmts.append(AssignStmt(rightSide, Alloc(alloc, loc), loc))
      case Input(loc) =>
        rightSide = createVar(vars, declaredVars, loc)
        stmts.append(AssignStmt(rightSide, Input(loc), loc))
      case ArrayAccess(array, index, loc) =>
        val arr = normalizeExpr(array, stmts, vars, declaredVars)
        val i = normalizeExpr(index, stmts, vars, declaredVars)
        rightSide = createVar(vars, declaredVars, loc)
        stmts.append(AssignStmt(rightSide, ArrayAccess(arr, i, loc), loc))
      case FieldAccess(record, field, loc) =>
        val rec = normalizeExpr(record, stmts, vars, declaredVars)
        rightSide = createVar(vars, declaredVars, loc)
        stmts.append(AssignStmt(rightSide, FieldAccess(rec, field, loc), loc))
      case _ =>
    }
    rightSide
  }
}

package microc.symbolic_execution

import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, AstPrinter, BinaryOp, CallFuncExpr, CodeLoc, Decl, Deref, Divide, Equal, Expr, FieldAccess, GreaterEqual, GreaterThan, Identifier, IfStmt, Input, LowerEqual, LowerThan, Minus, NestedBlockStmt, Not, NotEqual, Null, Number, OrOr, OutputStmt, Plus, Record, RecordField, ReturnStmt, Stmt, Times, VarRef, WhileStmt}
import microc.cfg.CfgNode
import microc.symbolic_execution.ExecutionException.errorDivByZero
import microc.symbolic_execution.Value.{ArrVal, IteVal, NullRef, PointerVal, RecVal, Symbolic, SymbolicExpr, SymbolicVal, Val}

import scala.collection.immutable.HashSet
import scala.collection.mutable
import scala.util.Random

object Utility {
  def varIsFromOriginalProgram(name: String): Boolean = {
    !(name.length > 2 && name(0) == '_' && (name(1) == 't' || name(1) == 'l'))
  }

  def getName(expr: Expr): String = {
    expr match {
      case Identifier(name, _) => name
      case ArrayAccess(array, index, loc) => getName(array)
      case FieldAccess(record, field, loc) => getName(record)
      case Deref(pointer, loc) => getName(pointer)
    }
  }

  def isSubsumptionVar(name: String): Boolean = {
    name.length > 2 && name(0) == '_' && name(1) == 'l'
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


  def expressionCanCauseError(expr: Expr): Boolean = {
    expr match {
      case BinaryOp(Divide, left, right, _) => containsUnpredictability(right) || expressionCanCauseError(left) || expressionCanCauseError(right)
      case BinaryOp(_, left, right, _) => expressionCanCauseError(left) || expressionCanCauseError(right)
      case Not(expr, _) => expressionCanCauseError(expr)
      case Alloc(expr, _) => expressionCanCauseError(expr)
      case Input(_) => false
      case CallFuncExpr(targetFun, args, loc) => args.exists(arg => expressionCanCauseError(arg))
      case Identifier(_, _) => false
      case Number(_, _) => false
      case Null(_) => false
      case ArrayNode(elems, _) => elems.exists(elem => expressionCanCauseError(elem))
      case ArrayAccess(array, index, _) => expressionCanCauseError(array) || expressionCanCauseError(index) || containsUnpredictability(index)
      case Record(fields, loc) => fields.exists(field => expressionCanCauseError(field.expr))
      case FieldAccess(record, field, loc) => expressionCanCauseError(record)
      case Deref(pointer, loc) => expressionCanCauseError(pointer)
      case _ => false
    }
  }

  def statementCanCauseError(stmt: Stmt): Boolean = {
      stmt match {
        case OutputStmt(expr, _) => expressionCanCauseError(expr)
        case ReturnStmt(expr, _) => expressionCanCauseError(expr)
        case IfStmt(expr, _, _, _) => expressionCanCauseError(expr)
        case WhileStmt(expr, _, _) => expressionCanCauseError(expr)
        case AssignStmt(left, right, _) => expressionCanCauseError(left) || expressionCanCauseError(right)
        case _ => false
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
      case Deref(pointer, _) => getIdentifiersThatCanCauseError(pointer)
      case ArrayNode(elems, _) => elems.flatMap(elem => getIdentifiersThatCanCauseError(elem)).toSet
      case ArrayAccess(array, index, _) => getIdentifiersThatCanCauseError(array) ++ getAllIdentifierNames(index)
      case Record(fields, _) => fields.flatMap(field => getIdentifiersThatCanCauseError(field.expr)).toSet
      case FieldAccess(record, _, _) => getIdentifiersThatCanCauseError(record)
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
      case Record(fields, loc) => fields.flatMap(field => getAllIdentifierNames(field.expr)).toSet
      case FieldAccess(record, field, loc) => getAllIdentifierNames(record)
      case Deref(pointer, loc) => getAllIdentifierNames(pointer)
      case _ => Set.empty
    }
  }

  def simplifyArithExpr(expr: Expr): Expr = {
    var res = expr match {
      case n@Number(_, _) => n
      case BinaryOp(AndAnd, Number(1, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(OrOr, Number(0, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(AndAnd, expr, Number(1, _), _) => simplifyArithExpr(expr)
      case BinaryOp(OrOr, expr, Number(0, _), _) => simplifyArithExpr(expr)
      case BinaryOp(AndAnd, Number(0, loc), expr, _) => Number(0, loc)
      case BinaryOp(OrOr, Number(1, loc), expr, _) => Number(1, loc)
      case BinaryOp(AndAnd, expr, Number(0, loc), _) => Number(0, loc)
      case BinaryOp(OrOr, expr, Number(1, loc), _) => Number(1, loc)
      case BinaryOp(AndAnd, expr1, expr2, _) if expr1.equals(expr2) => simplifyArithExpr(expr1)
      case BinaryOp(OrOr, expr1, expr2, _) if expr1.equals(expr2) => simplifyArithExpr(expr1)
      case BinaryOp(Plus, expr, Number(0, _), _) => simplifyArithExpr(expr)
      case BinaryOp(Times, expr, Number(1, _), _) => simplifyArithExpr(expr)
      case BinaryOp(Plus, Number(0, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(Times, Number(1, _), expr, _) => simplifyArithExpr(expr)
      case BinaryOp(Times, Number(0, _), _, loc) => Number(0, loc)
      case BinaryOp(Times, _, Number(0, _), loc) => Number(0, loc)
      case BinaryOp(OrOr, Not(expr1, _), expr2, loc) if expr1.equals(expr2) => Number(1, loc)
      case BinaryOp(OrOr, expr1, Not(expr2, _), loc) if expr1.equals(expr2) => Number(1, loc)
      case BinaryOp(operator, left, right, loc) =>
        (simplifyArithExpr(left), simplifyArithExpr(right)) match {
          case (Number(value, loc), Number(value2, _)) =>
            operator match {
              case Plus => Number(value + value2, loc)
              case Minus => Number(value - value2, loc)
              case Times => Number(value * value2, loc)
              case Divide => {
                if (value2 == 0) {
                  throw errorDivByZero(loc, null)
                }
                Number(value / value2, loc)
              }
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
      case Not(Number(value, loc), _) =>
        Number(if (value == 0) {
          1
        }
        else {
          0
        }, loc)
      case other => other
    }
    if (res != expr) {
      res = simplifyArithExpr(res)
    }
    res
  }

  def applyVal(v: Val, state: SymbolicState, allowReturnNonInitialized: Boolean = false): Expr = {
    v match {
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case NullRef => NullRef
      case PointerVal(addr) => PointerVal(addr)
      case SymbolicExpr(expr, _) => applyTheState(expr, state, allowReturnNonInitialized)
      case IteVal(val1, val2, cond, loc) =>
        (applyVal(state.getValOnMemoryLocation(val1).get, state), applyVal(state.getValOnMemoryLocation(val2).get, state)) match {
          case (a: Symbolic, b: Symbolic) => IteVal(state.addVal(a), state.addVal(b), applyTheState(cond, state, allowReturnNonInitialized), loc)
          case (a: Symbolic, b) => IteVal(state.addVal(a), state.addVal(SymbolicExpr(b, loc)), applyTheState(cond, state, allowReturnNonInitialized), loc)
          case (a, b: Symbolic) => IteVal(state.addVal(SymbolicExpr(a, loc)), state.addVal(b), applyTheState(cond, state, allowReturnNonInitialized), loc)
          case (a, b) => IteVal(state.addVal(SymbolicExpr(a, loc)), state.addVal(SymbolicExpr(b, loc)), applyTheState(cond, state, allowReturnNonInitialized), loc)
        }
      case r@RecVal(_) => r
      case a@ArrVal(_) => a
      case _ =>
        throw new Exception("this should never happen")
    }
  }

  def applyTheState(expr: Expr, state: SymbolicState, allowReturnNonInitialized: Boolean = false): Expr = {
    var res = expr match {
      case Not(expr, loc) =>
        Not(applyTheState(expr, state, allowReturnNonInitialized), loc)
      case BinaryOp(operator, left, right, loc) => BinaryOp(operator, applyTheState(left, state, allowReturnNonInitialized), applyTheState(right, state, allowReturnNonInitialized), loc)
      case Identifier(name, loc) => applyVal(state.getValueOfVar(name, loc, allowReturnNonInitialized), state, allowReturnNonInitialized)
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case NullRef => NullRef
      case PointerVal(addr) => PointerVal(addr)
      case SymbolicExpr(expr, _) => applyTheState(expr, state, allowReturnNonInitialized)
      case r@RecVal(_) => r
      case a@ArrVal(_) => a
      case i@Input(loc) => SymbolicVal(CodeLoc(0, 0))
      case Deref(pointer, loc) =>
        Deref(applyTheState(pointer, state, allowReturnNonInitialized), loc)
      case ArrayAccess(array, index, loc) =>
        ArrayAccess(applyTheState(array, state, allowReturnNonInitialized), applyTheState(index, state, allowReturnNonInitialized), loc)
      case ArrayNode(elems, loc) =>
        ArrayNode(elems.map(elem => applyTheState(elem, state, allowReturnNonInitialized)), loc)
      case FieldAccess(record, field, loc) =>
        FieldAccess(applyTheState(record, state, allowReturnNonInitialized), field, loc)
      case Record(fields, loc) =>
        Record(fields.map(field => RecordField(field.name, applyTheState(field.expr, state, allowReturnNonInitialized), field.loc)), loc)
      case _ =>
        throw new Exception("")
    }
    if (res != expr) {
      res = applyTheState(res, state, allowReturnNonInitialized)
    }
    res
  }



  def removeUnnecessarySymbolicExpr(expr: SymbolicExpr): Val = {
    expr.value match {
      case inner@SymbolicExpr(_, _) => removeUnnecessarySymbolicExpr(inner)
      case n@Number(_, _) => n
      case s@SymbolicVal(_) => s
      case p@PointerVal(_) => p
      case a@ArrVal(_) => a
      case r@RecVal(_) => r
      case other => //at least for arrnode, do not remove symbolic expr
        expr
    }
  }


  def replaceExpr(expr: Expr, toReplace: Expr, newValue: Expr): Expr = {
    expr match {
      case _ if expr.equals(toReplace) => newValue
      case Not(expr, loc) =>
        Not(replaceExpr(expr, toReplace,newValue), loc)
      case BinaryOp(operator, left, right, loc) =>
        BinaryOp(operator, replaceExpr(left, toReplace, newValue), replaceExpr(right, toReplace, newValue), loc)
      case id@Identifier(_, _) => id
      case n@Number(_, _) => n
      case v@SymbolicVal(_) => v
      case SymbolicExpr(expr, _) => replaceExpr(expr, toReplace, newValue)
      case Null(loc) => Null(loc)
      case Input(loc) => SymbolicVal(CodeLoc(0, 0))
      case ArrayAccess(array, index, loc) => ArrayAccess(replaceExpr(array, toReplace, newValue), replaceExpr(index, toReplace, newValue), loc)
      case ArrayNode(elems, loc) => ArrayNode(elems.map(elem => replaceExpr(elem, toReplace, newValue)), loc)
      case Deref(pointer, loc) => Deref(replaceExpr(pointer, toReplace, newValue), loc)
      case VarRef(id, loc) => replaceExpr(id, toReplace, newValue)
      case FieldAccess(record, field, loc) => FieldAccess(replaceExpr(record, toReplace, newValue), field, loc)
      case Record(fields, loc) => Record(fields.map(field => RecordField(field.name, replaceExpr(field.expr, toReplace, newValue), field.loc)), loc)
      case Alloc(expr, loc) => Alloc(replaceExpr(expr, toReplace, newValue), loc)
    }
  }

  def replaceWithMapping(expr: Expr, mapping: mutable.HashMap[Val, Expr], symbolicState: SymbolicState): Expr = {
    expr match {
      case BinaryOp(operator, left, right, loc) =>
        BinaryOp(operator, replaceWithMapping(left, mapping, symbolicState), replaceWithMapping(right, mapping, symbolicState), loc)
      case Not(expr, loc) =>
        Not(replaceWithMapping(expr, mapping, symbolicState), loc)
      case SymbolicExpr(expr, loc) =>
        SymbolicExpr(replaceWithMapping(expr, mapping, symbolicState), loc)
      case ArrayAccess(array, index, loc) =>
        ArrayAccess(replaceWithMapping(array, mapping, symbolicState), replaceWithMapping(index, mapping, symbolicState), loc)
      case v@SymbolicVal(_) if mapping.contains(v) =>
        symbolicState.getValAtMemoryLoc(mapping(v)).asInstanceOf[Symbolic]
      case e => e
    }
  }

  def containsVariableNotStartingInAProgram(expr: Expr): Boolean = {
    expr match {
      case BinaryOp(operator, left, right, loc) => containsVariableNotStartingInAProgram(left) || containsVariableNotStartingInAProgram(right)
      case Not(expr, _) => containsVariableNotStartingInAProgram(expr)
      case Identifier(name, _) => !Utility.varIsFromOriginalProgram(name)
      case SymbolicExpr(expr, _) => containsVariableNotStartingInAProgram(expr)
      case _ => false
    }
  }

  def getMemoryCellsFromAnExpr(expr: Expr): mutable.HashSet[Expr] = {
    expr match {
      case BinaryOp(_, left, right, _) =>
        val res = mutable.HashSet[Expr]()
        res.addAll(getMemoryCellsFromAnExpr(left))
        for (e <- getMemoryCellsFromAnExpr(right)) {
          if (res.forall(e2 => !e.equals(e2))) {
            res.add(e)
          }
        }
        res
      case Not(expr, _) =>
        getMemoryCellsFromAnExpr(expr)
      case id@Identifier(_, _) =>
        val res = mutable.HashSet[Expr]()
        res.add(id)
        res
      case d@Deref(_, _) =>
        val res = mutable.HashSet[Expr]()
        res.add(d)
        res
      case a@ArrayAccess(_, _, _) =>
        val res = mutable.HashSet[Expr]()
        res.add(a)
        res
      case f@FieldAccess(_, _, _) =>
        val res = mutable.HashSet[Expr]()
        res.add(f)
        res
      case SymbolicExpr(expr, _) =>
        getMemoryCellsFromAnExpr(expr)
      case _ =>
        mutable.HashSet()
    }
  }


  def exprContainsAMemoryLocation(expr: Expr, vars: mutable.HashSet[String], printer: AstPrinter): Boolean = {
    expr match {
      case BinaryOp(_, left, right, _) =>
        exprContainsAMemoryLocation(left, vars, printer) || exprContainsAMemoryLocation(right, vars, printer)
      case Not(expr, _) =>
        exprContainsAMemoryLocation(expr, vars, printer)
      case SymbolicExpr(expr, _) =>
        exprContainsAMemoryLocation(expr, vars, printer)
      case id@Identifier(_, _) if vars.contains(printer.print(id)) =>
        true
      case a@ArrayAccess(_, _, _) if vars.contains(printer.print(a)) =>
        true
      case _ =>
        false
    }
  }

  def getMemoryLocationsFromExpr(expr: Expr, printer: AstPrinter): mutable.HashSet[String] = {
    expr match {
      case BinaryOp(_, left, right, _) =>
        val res = getMemoryLocationsFromExpr(left, printer)
        res.addAll(getMemoryLocationsFromExpr(right, printer))
        res
      case Not(expr, _) =>
        getMemoryLocationsFromExpr(expr, printer)
      case id@Identifier(_, _) =>
        mutable.HashSet(printer.print(id))
      case a@ArrayAccess(_, _, _) =>
        mutable.HashSet(printer.print(a))
      case f@FieldAccess(_, _, _) =>
        mutable.HashSet(printer.print(f))
      case d@Deref(_, _) =>
        mutable.HashSet(printer.print(d))
      case SymbolicExpr(v, _) =>
        getMemoryLocationsFromExpr(v, printer)
      case _ =>
        mutable.HashSet()
    }
  }

  def isNotUpdatedByUnpredictableLoc(name: String, locationsWithUnpredictability: mutable.HashSet[String],
                                     updatedBy: mutable.HashMap[String, mutable.HashSet[String]], visited: mutable.HashSet[String]): Boolean = {
    if (locationsWithUnpredictability.contains(name)) {
      return false
    }
    if (visited.contains(name)) {
      return true
    }
    visited.add(name)
    updatedBy.get(name) match {
      case Some(updated) =>
        updated.forall(up => isNotUpdatedByUnpredictableLoc(up, locationsWithUnpredictability, updatedBy, visited))
      case None =>
        true
    }
  }

  def getConjunctions(expr: Expr): mutable.HashSet[Expr] = {
    expr match {
      case binOp: BinaryOp =>
        binOp.operator match {
          case AndAnd =>
            val res = getConjunctions(binOp.left).addAll(getConjunctions(binOp.right))
            res.add(expr)
            res
          case _ =>
            val res = mutable.HashSet[Expr]()
            res.add(expr)
            res
        }
      case _ =>
        val res = mutable.HashSet[Expr]()
        res.add(expr)
        res
    }
  }

  def simplifyADisjunction(expr1: Expr, expr2: Expr): Expr = {
    val disjunctions1 = getConjunctions(expr1)
    val disjunctions2 = getConjunctions(expr2)
    val sharedDisjunctions = mutable.HashSet[Expr]()
    val uniqueDisjuntions1 = mutable.HashSet[Expr]()
    val uniqueDisjuntions2 = mutable.HashSet[Expr]()
    for (disjunction <- disjunctions1) {
      if (disjunctions2.contains(disjunction)) {
        sharedDisjunctions.add(disjunction)
      }
      else {
        uniqueDisjuntions1.add(disjunction)
      }
    }
    for (disjunction <- disjunctions2) {
      if (!disjunctions1.contains(disjunction)) {
        uniqueDisjuntions2.add(disjunction)
      }
    }
    var sharedConjunction: Expr = null
    var uniqueConjunction1: Expr = null
    var uniqueConjunction2: Expr = null
    for (disjunction <- sharedDisjunctions) {
      if (sharedConjunction == null) {
        sharedConjunction = disjunction
      }
      else {
        sharedConjunction = BinaryOp(AndAnd, sharedConjunction, disjunction, CodeLoc(0, 0))
      }
    }
    for (disjunction <- uniqueDisjuntions1) {
      if (uniqueConjunction1 == null) {
        uniqueConjunction1 = disjunction
      }
      else {
        uniqueConjunction1 = BinaryOp(OrOr, uniqueConjunction1, disjunction, CodeLoc(0, 0))
      }
    }
    for (disjunction <- uniqueDisjuntions2) {
      if (uniqueConjunction2 == null) {
        uniqueConjunction2 = disjunction
      }
      else {
        uniqueConjunction2 = BinaryOp(OrOr, uniqueConjunction2, disjunction, CodeLoc(0, 0))
      }
    }
    val res = if (sharedConjunction == null) {
      (uniqueConjunction1, uniqueConjunction2) match {
        case (null, null) =>
          throw new Exception("this should never happen")
        case (null, v) =>
          uniqueConjunction2
        case (v, null) =>
          uniqueConjunction1
        case (v1, v2) =>
          BinaryOp(OrOr, uniqueConjunction1, uniqueConjunction2, CodeLoc(0, 0))
      }
    }
    else {
      (uniqueConjunction1, uniqueConjunction2) match {
        case (null, null) =>
          sharedConjunction
        case (null, v) =>
          BinaryOp(AndAnd, sharedConjunction, uniqueConjunction2, CodeLoc(0, 0))
        case (v, null) =>
          BinaryOp(AndAnd, sharedConjunction, uniqueConjunction1, CodeLoc(0, 0))
        case (v1, v2) =>
          BinaryOp(AndAnd, sharedConjunction, BinaryOp(OrOr, uniqueConjunction1, uniqueConjunction2, CodeLoc(0, 0)), CodeLoc(0, 0))
      }
    }
    simplifyArithExpr(res)
  }

  def removeIteVal(e: Expr, state: SymbolicState): Expr = {
    e match {
      case IteVal(trueState, falseState, expr, _) =>
        val e1 = removeIteVal(state.getValOnMemoryLocation(trueState).get.asInstanceOf[Symbolic], state)
        val e2 = removeIteVal(state.getValOnMemoryLocation(falseState).get.asInstanceOf[Symbolic], state)
        BinaryOp(OrOr, BinaryOp(AndAnd, e1, expr, CodeLoc(0, 0)), BinaryOp(AndAnd, e2, Not(expr, CodeLoc(0, 0)), CodeLoc(0, 0)), CodeLoc(0, 0))
      case BinaryOp(operator, left, right, loc) =>
        BinaryOp(operator, removeIteVal(left, state), removeIteVal(right, state), loc)
      case Not(expr, loc) =>
        Not(removeIteVal(expr, state), loc)
      case _ => e
    }
  }

  def applyToVarsFromStartingProgram(expr: Expr, idMapping: mutable.HashMap[Identifier, Expr]): Expr = {
    expr match {
      case id@Identifier(name, _) if Utility.varIsFromOriginalProgram(name) => id
      case id@Identifier(_, _) =>
        if (!idMapping.contains(id)) {
          println("fds")
        }
        applyToVarsFromStartingProgram(idMapping(id), idMapping)
      case BinaryOp(operator, left, right, loc) =>
        BinaryOp(operator, applyToVarsFromStartingProgram(left, idMapping), applyToVarsFromStartingProgram(right, idMapping), loc)
      case Not(expr, loc) =>
        Not(applyToVarsFromStartingProgram(expr, idMapping), loc)
      case Deref(pointer, loc) =>
        Deref(applyToVarsFromStartingProgram(pointer, idMapping), loc)
      case ArrayAccess(array, index, loc) =>
        ArrayAccess(applyToVarsFromStartingProgram(array, idMapping), index, loc)
      case FieldAccess(record, field, loc) =>
        FieldAccess(applyToVarsFromStartingProgram(record, idMapping), field, loc)
      case other => other
    }
  }

  def applyPointers(expr: Expr, state: SymbolicState): Expr = {
    expr match {
      case BinaryOp(operator, left, right, loc) => BinaryOp(operator, applyPointers(left, state), applyPointers(right, state), loc)
      case Not(expr, loc) => Not(applyPointers(expr, state), loc)
      case d@Deref(_, _) => state.getValAtMemoryLoc(d).asInstanceOf[Symbolic]
      case a@ArrayAccess(array, _, _) =>
        array match {
          case arr: ArrayNode =>//Hardcoded arrays in code
            a
          case _ =>
            state.getValAtMemoryLoc(a).asInstanceOf[Symbolic]
        }
      case f@FieldAccess(record, _, _) =>
        record match {
          case r: Record => //Hardcoded records in code
            f
          case _ =>
            state.getValAtMemoryLoc(f).asInstanceOf[Symbolic]
        }
      case other => other
    }
  }


  def getTrueBranch(node: CfgNode): CfgNode = {
    val ast = node.ast
    ast match {
      case WhileStmt(_, thenBranch, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          node.succ.find(s => s.ast == ast).get
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          node.succ.find(s => s.ast == firstThenStatement).get
        }
        next
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          node.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          node.succ.find(s => s.ast == firstThenStatement).get
        }
        next
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            node.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
              node.succ.find(s => s.ast == firstThenStatement).get
            }
          return next
        }
        node.succ.find(s => s.ast != elseBranch.head).get
    }
  }


  def getFalseBranch(node: CfgNode): CfgNode = {
    val ast = node.ast;
    ast match {
      case WhileStmt(guard, thenBranch, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          node.succ.find(s => s.ast != ast).get
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          node.succ.find(s => s.ast != firstThenStatement).get
        }
        next
      case IfStmt(guard, thenBranch, None, loc) =>
        val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
          node.succ.head
        }
        else {
          val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
          node.succ.find(s => s.ast != firstThenStatement).get
        }
        next
      case IfStmt(guard, thenBranch, Some(NestedBlockStmt(elseBranch, loc)), _) =>
        if (elseBranch.isEmpty) {
          val next = if (thenBranch.asInstanceOf[NestedBlockStmt].body.isEmpty) {
            node.succ.head
          }
          else {
            val firstThenStatement = thenBranch.asInstanceOf[NestedBlockStmt].body.head
            node.succ.find(s => s.ast != firstThenStatement).get
          }
          return next
        }
        node.succ.find(s => s.ast == elseBranch.head).get
    }
  }


  def getIdentifiers(expr: Expr): mutable.HashSet[Identifier] = {
    expr match {
      case BinaryOp(_, left, right, _) =>
        val res = getIdentifiers(left).addAll(getIdentifiers(right))
        res
      case Not(expr, _) =>
        getIdentifiers(expr)
      case id@Identifier(_, _) =>
        val res = mutable.HashSet[Identifier]()
        res.add(id)
        res
      case _ => mutable.HashSet[Identifier]()
    }
  }

  def isComparisonOperator(binaryOp: BinaryOp): Boolean = {
    binaryOp.operator match {
      case Plus => false
      case Minus => false
      case Times => false
      case Divide => false
      case _ => true
    }
  }

  def containsOneOfTheIdentifiers(expr: Expr, ids: mutable.HashSet[Expr]): Boolean = {
    expr match {
      case BinaryOp(_, left, right, _) => containsOneOfTheIdentifiers(left, ids) || containsOneOfTheIdentifiers(right, ids)
      case Not(expr, _) => containsOneOfTheIdentifiers(expr, ids)
      case id@Identifier(_, _) =>
        ids.exists(i => i.equals(id))
      case _ =>
        false
    }
  }

  def isLoopAnnotation(expr: Expr): Boolean = {
    expr match {
      case BinaryOp(operator, left, right, loc) =>
        (left, right) match {
          case (Identifier("_l1", CodeLoc(0, 0)), Number(0, CodeLoc(0, 0))) =>
            true
          case _ => false
        }
      case _ => false
    }
  }
}
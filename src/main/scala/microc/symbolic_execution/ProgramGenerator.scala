package microc.symbolic_execution

import microc.ast.{Alloc, AndAnd, ArrayAccess, ArrayNode, AssignStmt, AstPrinter, BinaryOp, BinaryOperator, CallFuncExpr, CodeLoc, Deref, Divide, Equal, Expr, FieldAccess, FunBlockStmt, FunDecl, GreaterEqual, GreaterThan, Identifier, IdentifierDecl, IfStmt, Input, Loc, LowerEqual, LowerThan, Minus, NestedBlockStmt, Not, NotEqual, Null, Number, OrOr, OutputStmt, Plus, Program, Record, RecordField, ReturnStmt, Stmt, StmtInNestedBlock, Times, VarRef, VarStmt, WhileStmt}

import scala.collection.mutable
import scala.util.Random


abstract class VarType {
  def toString(): String

  def getInner(field: String): VarType
}

case class NumType() extends VarType {
  override def toString: String = "number"

  override def getInner(field: String): VarType = throw new UnsupportedOperationException()
}


case class PtrType(inner: VarType) extends VarType {
  override def toString: String = "pointer -> " + inner.toString

  override def getInner(field: String): VarType = inner
}


case class ArrayType(innerType: VarType) extends VarType {
  override def toString: String = "array -> " + innerType.toString

  override def getInner(field: String): VarType = innerType
}


case class RecType(fields: mutable.HashMap[String, VarType]) extends VarType {

  override def toString(): String = "rec -> " + fields.map(field => "( " + field._1 + " " + field._2.toString + " )")

  override def getInner(field: String): VarType = fields(field)
}



object ProgramGenerator {
  val random = new Random()

  val existingTypes: mutable.HashSet[VarType] = mutable.HashSet[VarType]()

  var functionNames: List[String] = List.empty

  var recFields: mutable.HashMap[VarType, mutable.HashSet[(String, VarType)]] = mutable.HashMap()

  var arraySizes: mutable.HashMap[String, Int] = mutable.HashMap()

  var generatedAnArray = false

  def randomLoc(): CodeLoc = CodeLoc(random.nextInt(100), random.nextInt(100))


  def randomBinaryOperator(isPointer: Boolean = false): BinaryOperator = {
    if (isPointer) {
      if (random.nextBoolean()) Equal else NotEqual
    } else {
      val operators = List(Plus, Minus, Times)
      operators(random.nextInt(operators.size))
    }
  }

  def randomIdentifier(declaredIdentifiers: Map[String, VarType]): Identifier = {
    Identifier(declaredIdentifiers.keys.toList(random.nextInt(declaredIdentifiers.size)), randomLoc())
  }

  def randomArrayIdentifier(declaredIdentifiers: Map[String, VarType]): Identifier = {
    val filteredIdentifiers = declaredIdentifiers.filter(id => {
      id._2 match {
        case ArrayType(_) => true
        case _ => false
      }
    }).keys.toList
    if (filteredIdentifiers.nonEmpty) {
      return Identifier(filteredIdentifiers(random.nextInt(filteredIdentifiers.size)), randomLoc())
    }
    throw new Exception("")
  }

  def randomIdentifierOfType(expectedType: VarType, declaredIdentifiers: Map[String, VarType]): Identifier = {
    val filteredIdentifiers = declaredIdentifiers.filter(_._2 == expectedType).keys.toList
    if (filteredIdentifiers.nonEmpty) {
      return Identifier(filteredIdentifiers(random.nextInt(filteredIdentifiers.size)), randomLoc())
    }
    throw new Exception("")
  }

  def randomFunctionName(expectedType: String): Identifier = {
    Identifier(functionNames(random.nextInt(functionNames.size)), randomLoc())
  }

  def randomExpr(expectedType: VarType, depth: Int = 0, declaredIdentifiers: Map[String, VarType]): Expr = {
    if (depth > 5) {
      getRandomValueOfType(expectedType)
    }
    else {
      expectedType match {
        case NumType() =>
          random.nextInt(7) match {
            case 0 => Input(randomLoc())
            case 1 => BinaryOp(randomBinaryOperator(), randomExpr(expectedType, depth + 1, declaredIdentifiers), randomExpr(expectedType, depth + 1, declaredIdentifiers), randomLoc())
            //case 2 => BinaryOp(randomBinaryOperator(), randomExpr("pointer", depth + 1, declaredIdentifiers), randomExpr("pointer", depth + 1, declaredIdentifiers), randomLoc())
            case 2 => randomIdentifierOfType(expectedType, declaredIdentifiers)
            case 3 => Not(randomExpr(expectedType, depth + 1, declaredIdentifiers), randomLoc())
            case 4 => Input(randomLoc())
            case 5 if existingTypes.contains(ArrayType(expectedType)) =>
              val id = randomExpr(ArrayType(expectedType), depth + 1, declaredIdentifiers)
              id match {
                case Identifier(name, loc) =>
                  ArrayAccess(
                    id,
                    Number(random.nextInt(arraySizes(name)), randomLoc()),
                    randomLoc()
                  )
                case ArrayNode(elems, _) =>
                  ArrayAccess(
                    id,
                    Number(random.nextInt(elems.size), randomLoc()),
                    randomLoc()
                  )
              }

            case 6 if recFields.contains(expectedType) =>
              val field = recFields(expectedType).toList(random.nextInt(recFields(expectedType).size))
              FieldAccess(
                randomIdentifierOfType(field._2, declaredIdentifiers),
                field._1,
                randomLoc()
              )
            case _ =>
              Number(random.nextInt(10), randomLoc())
            //case 6 => CallFuncExpr(randomFunctionName(expectedType), List.empty, randomLoc())
          }
        case PtrType(inner) =>
          random.nextInt(3) match {
            case 0 => randomIdentifierOfType(expectedType, declaredIdentifiers)
            case 1 => Alloc(randomExpr(inner, depth + 1, declaredIdentifiers), randomLoc())
            case 2 => VarRef(randomIdentifierOfType(inner, declaredIdentifiers), randomLoc())
            case 3 => Null(randomLoc())
          }
        case ArrayType(inner) =>
          randomIdentifierOfType(expectedType, declaredIdentifiers)
        case RecType(fields) =>
          randomIdentifierOfType(expectedType, declaredIdentifiers)
      }
    }
  }

  def randomStmt(depth: Int = 0, declaredIdentifiers: Map[String, VarType]): StmtInNestedBlock = {
    if (depth > 3) {
      random.nextInt(2) match {
        case 0 =>
          OutputStmt (randomExpr (NumType (), declaredIdentifiers = declaredIdentifiers), randomLoc () )
        case 1 =>
          val identifier = randomIdentifier(declaredIdentifiers)
          AssignStmt(identifier, randomExpr(declaredIdentifiers(identifier.name), depth + 1, declaredIdentifiers), randomLoc())
      }
    }
    else {
      random.nextInt(5) match {
        case 0 => {
          val identifier = randomIdentifier(declaredIdentifiers)
          AssignStmt(identifier, randomExpr(declaredIdentifiers(identifier.name), depth + 1, declaredIdentifiers), randomLoc())
        }
        case 1 if generatedAnArray => {
          val identifier = randomArrayIdentifier(declaredIdentifiers)
          val innerType = declaredIdentifiers(identifier.name).getInner("")
          AssignStmt(
            identifier match {
              case Identifier(name, loc) =>
                ArrayAccess(
                  identifier,
                  Number(random.nextInt(arraySizes(name)), randomLoc()),
                  randomLoc()
                )
//              case ArrayNode(elems, _) =>
//                ArrayAccess(
//                  identifier,
//                  Number(random.nextInt(elems.size), randomLoc()),
//                  randomLoc()
//                )
            },
            randomExpr(innerType, depth + 1, declaredIdentifiers),
            randomLoc()
          )
        }
        case 1 => {
          val identifier = randomIdentifier(declaredIdentifiers)
          AssignStmt(identifier, randomExpr(declaredIdentifiers(identifier.name), depth + 1, declaredIdentifiers), randomLoc())
        }
        case 2 => IfStmt(
          randomExpr(NumType(), depth + 1, declaredIdentifiers),
          NestedBlockStmt((1 to random.nextInt(5) + 5).map(_ => randomStmt(depth + 1, declaredIdentifiers)).toList, randomLoc()),
          Some(NestedBlockStmt((1 to random.nextInt(5) + 5).map(_ => randomStmt(depth + 1, declaredIdentifiers)).toList, randomLoc())),
          randomLoc()
        )
        case 3 => WhileStmt(
          randomExpr(NumType(), depth + 1, declaredIdentifiers),
          NestedBlockStmt((1 to random.nextInt(5) + 5).map(_ => randomStmt(depth + 1, declaredIdentifiers)).toList, randomLoc()),
          randomLoc()
        )
        case 4 =>
          OutputStmt(randomExpr(NumType(), depth + 1, declaredIdentifiers), randomLoc())
      }
    }
  }

  private def getRandomTypeWithHardcodedProbabilities(): VarType = {
    val res = getRandomTypeWithHardcodedProbabilitiesInner(false)
    existingTypes.add(res)
    res
  }
  private def getRandomTypeWithHardcodedProbabilitiesInner(inRecord: Boolean): VarType = {
    if (random.nextBoolean())
      NumType()
    else {
      if (random.nextInt(5) != 0 || inRecord) {
        val inner = getRandomTypeWithHardcodedProbabilitiesInner(inRecord)
        if (!existingTypes.contains(inner)) {
          inner
        }
        else {
          if (random.nextInt(5) == 0) {
            generatedAnArray = true
            ArrayType(inner)
          }
          else {
            PtrType(inner)
          }
        }
      }
      else {
        val fields = mutable.HashMap[String, VarType]()
        val res = RecType(fields)
        for (i <- 0 until random.nextInt(5) + 1){
          val inner = getRandomTypeWithHardcodedProbabilitiesInner(true)
          if (!existingTypes.contains(inner)) {
            NumType()
          }
          val name = Utility.generateRandomString()
          fields.put(name, inner)
          val tmp = recFields.getOrElse(inner, new mutable.HashSet[(String, VarType)]())
          tmp.add((name, res))
          recFields.put(inner, tmp)
        }
        res
      }
    }
  }

  def randomFunDecl(name: String): FunDecl = {

    // 'main' function has zero parameters
    val params = List.empty[IdentifierDecl]

    var declaredIdentifiers = Map[String, VarType]()


    // Variable declarations
    val varDecls = (0 to random.nextInt(15) + 15  ).map { i =>
      val varName = s"var${i}"
      val varType = getRandomTypeWithHardcodedProbabilities()
      //println(varName, varType)
      declaredIdentifiers += (varName -> varType)
      IdentifierDecl(varName, randomLoc())
    }.toList

    val varsStmt = VarStmt(varDecls, randomLoc())

    // Initializations immediately after declarations
    val initAssignments = varDecls.map { decl =>
      val varType = declaredIdentifiers(decl.name)
      generateInitAssignment(decl.name, varType)
    }

    // Collecting all statements including initializations and random statements
    val bodyStatements = initAssignments ++ List.fill(random.nextInt(5) + 5)(randomStmt(declaredIdentifiers = declaredIdentifiers))
    val ret = ReturnStmt(randomExpr(NumType(), 3, declaredIdentifiers), randomLoc())
    val block = FunBlockStmt(List(varsStmt), bodyStatements, ret, randomLoc())

    FunDecl(name, params, block, randomLoc())
  }


  def getRandomValueOfType(varType: VarType): Expr = {
    varType match {
      case NumType() => Number(random.nextInt(10) - 1, randomLoc())
      case PtrType(inner) => Alloc(getRandomValueOfType(inner), randomLoc())
      case ArrayType(inner) =>
        ArrayNode((1 to random.nextInt(5) + 5).map(_ => getRandomValueOfType(inner)).toList, randomLoc())
      case RecType(fields) =>
        Record(fields.map(field => RecordField(field._1, getRandomValueOfType(field._2), randomLoc())).toList, randomLoc())
    }
  }

  def generateInitAssignment(varName: String, varType: VarType): AssignStmt = {
    val expr = getRandomValueOfType(varType)
    expr match {
      case ArrayNode(elems, _) => arraySizes.put(varName, elems.size)
      case _ =>
    }
    AssignStmt(Identifier(varName, randomLoc()), expr, randomLoc())
  }

  def generateRandomProgram(): Program = {
    val additionalFuns = List.fill(random.nextInt(3) + 1) {
      val funName = s"fun${random.nextInt(100)}"
      functionNames ::= funName
    }
    var funDecls = List[FunDecl]()
//    for (func <- functionNames) {
//      funDecls = funDecls :+ (randomFunDecl(func))
//    }
    funDecls = funDecls :+ (randomFunDecl("main"))
    funDecls.foreach(fce => println(new AstPrinter().print(fce)))
    Program(funDecls, randomLoc())
  }


}

package microc.generation

import microc.ast.{Alloc, ArrayAccess, ArrayNode, AssignStmt, AstPrinter, BinaryOp, BinaryOperator, Block, CodeLoc, Divide, Equal, Expr, FieldAccess, FunBlockStmt, FunDecl, Identifier, IdentifierDecl, IfStmt, Input, LowerThan, Minus, NestedBlockStmt, Not, NotEqual, Null, Number, OutputStmt, Plus, Program, Record, RecordField, ReturnStmt, StmtInNestedBlock, Times, VarRef, VarStmt, WhileStmt}
import microc.symbolic_execution.Utility

import scala.collection.mutable
import scala.util.Random

class ProgramGenerator(loopGenerationProbability: Double = 1.0 / 6.0, forLoopGenerationProbability: Double = 1.0 / 6.0,
                       maxStmtDepth: Int = 2, maxTopLvlStmtsCount: Int = 15, maxStmtsWithinABlock: Int = 7,
                       guaranteedError: Boolean = false, tryNotToGenerateRandomError: Boolean = true) {
  val random = new Random()

  val existingTypes: mutable.HashSet[VarType] = mutable.HashSet[VarType]()

  var functionNames: List[String] = List.empty

  var recFields: mutable.HashMap[VarType, mutable.HashSet[(String, VarType)]] = mutable.HashMap()

  var arraySizes: mutable.HashMap[String, Int] = mutable.HashMap()

  var generatedAnArray = false

  val remainingProbability = 1.0 - loopGenerationProbability - forLoopGenerationProbability

  val uniformProbability = remainingProbability / 4

  def randomLoc(): CodeLoc = CodeLoc(random.nextInt(100), random.nextInt(100))


  def randomBinaryOperator(isPointer: Boolean = false): BinaryOperator = {
    if (isPointer) {
      if (random.nextBoolean()) Equal else NotEqual
    } else {
      val operators = if (tryNotToGenerateRandomError) {
        List(Plus, Minus, Times)
      }
      else {
        List(Plus, Minus, Times, Divide)
      }
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

  def randomArrayOfSize(expectedType: ArrayType, declaredIdentifiers: Map[String, VarType], size: Int): Expr = {
    val filteredIdentifiers = declaredIdentifiers.filter(_._2 == expectedType).filter(id => arraySizes(id._1) == size).keys.toList
    if (filteredIdentifiers.nonEmpty) {
      return Identifier(filteredIdentifiers(random.nextInt(filteredIdentifiers.size)), randomLoc())
    }
    ArrayNode((1 to size).map(_ => randomExpr(expectedType.innerType, 1, declaredIdentifiers)).toList, randomLoc())
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

  def randomExpr(expectedType: VarType, depth: Int = 0, declaredIdentifiers: Map[String, VarType], arrSize: Int = 0): Expr = {
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
        case a@ArrayType(inner) if arrSize == 0 =>
          randomIdentifierOfType(expectedType, declaredIdentifiers)
        case a@ArrayType(inner) =>
          randomArrayOfSize(a, declaredIdentifiers, arrSize)
        case RecType(fields) =>
          randomIdentifierOfType(expectedType, declaredIdentifiers)
      }
    }
  }

  def randomStmt(depth: Int = 0, declaredIdentifiers: Map[String, VarType]): StmtInNestedBlock = {
    if (depth > maxStmtDepth) {
      random.nextInt(2) match {
        case 0 =>
          OutputStmt(randomExpr(NumType(), declaredIdentifiers = declaredIdentifiers), randomLoc())
        case 1 =>
          val identifier = randomIdentifier(declaredIdentifiers)
          val size = declaredIdentifiers(identifier.name) match {
            case ArrayType(_) => arraySizes(identifier.name)
            case _ => 0
          }
          AssignStmt(identifier, randomExpr(declaredIdentifiers(identifier.name), depth + 1, declaredIdentifiers, size), randomLoc())
      }
    }
    else {
      val randomValue = scala.util.Random.nextDouble()
      val caseNumber = randomValue match {
        case x if x < uniformProbability => 0
        case x if x < 2 * uniformProbability => 1
        case x if x < 3 * uniformProbability => 2
        case x if x < 4 * uniformProbability => 5
        case x if x < 4 * uniformProbability + loopGenerationProbability => 3
        case x if x < 4 * uniformProbability + loopGenerationProbability + forLoopGenerationProbability => 4
        case _ =>
          throw new Exception("this should never happen")
      }
      caseNumber match {
        case 0 => {
          val identifier = randomIdentifier(declaredIdentifiers)
          val size = declaredIdentifiers(identifier.name) match {
            case ArrayType(_) => arraySizes(identifier.name)
            case _ => 0
          }
          AssignStmt(identifier, randomExpr(declaredIdentifiers(identifier.name), depth + 1, declaredIdentifiers, size), randomLoc())
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
          NestedBlockStmt((1 to random.nextInt(maxStmtsWithinABlock)).map(_ => randomStmt(depth + 1, declaredIdentifiers)).toList, randomLoc()),
          Some(NestedBlockStmt((1 to random.nextInt(maxStmtsWithinABlock)).map(_ => randomStmt(depth + 1, declaredIdentifiers)).toList, randomLoc())),
          randomLoc()
        )
        case 3 => WhileStmt(
          randomExpr(NumType(), depth + 1, declaredIdentifiers),
          NestedBlockStmt((1 to random.nextInt(maxStmtsWithinABlock)).map(_ => randomStmt(depth + 1, declaredIdentifiers)).toList, randomLoc()),
          randomLoc()
        )
        case 4 =>
          var block = NestedBlockStmt((1 to random.nextInt(maxStmtsWithinABlock)).map(_ => randomStmt(depth + 1, declaredIdentifiers)).toList, randomLoc())
          val it = randomIdentifierOfType(NumType(), declaredIdentifiers)
          block = NestedBlockStmt(block.body.appended(AssignStmt(it, BinaryOp(Plus, it, Number(1, randomLoc()), randomLoc()), randomLoc())), randomLoc())
          WhileStmt(
            BinaryOp(LowerThan, it, randomIdentifierOfType(NumType(), declaredIdentifiers), randomLoc()),
            block,
            randomLoc()
          )
        case 5 =>
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
        for (i <- 0 until random.nextInt(5) + 1) {
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

  def randomFunDecl(name: String): (FunDecl, Map[String, VarType]) = {

    // 'main' function has zero parameters
    val params = List.empty[IdentifierDecl]

    var declaredIdentifiers = Map[String, VarType]()


    // Variable declarations
    var varDecls = (0 to random.nextInt(15) + 15).map { i =>
      val varName = s"var${i}"
      val varType = getRandomTypeWithHardcodedProbabilities()
      //println(varName, varType)
      declaredIdentifiers += (varName -> varType)
      IdentifierDecl(varName, randomLoc())
    }.toList
    val guaranteedArray = (s"var${varDecls.size}" -> ArrayType(NumType()))
    declaredIdentifiers += guaranteedArray
    varDecls = varDecls.appended(IdentifierDecl(s"var${varDecls.size}", randomLoc()))

    val varsStmt = VarStmt(varDecls, randomLoc())

    // Initializations immediately after declarations
    val initAssignments = varDecls.map { decl =>
      val varType = declaredIdentifiers(decl.name)
      generateInitAssignment(decl.name, varType)
    }

    // Collecting all statements including initializations and random statements
    val bodyStatements = initAssignments ++ List.fill(random.nextInt(maxTopLvlStmtsCount))(randomStmt(declaredIdentifiers = declaredIdentifiers))
    val ret = ReturnStmt(randomExpr(NumType(), 3, declaredIdentifiers), randomLoc())
    val block = FunBlockStmt(List(varsStmt), bodyStatements, ret, randomLoc())

    (FunDecl(name, params, block, randomLoc()), declaredIdentifiers)
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

  def plugAnError(fun: FunDecl, declaredIdentifiers: Map[String, VarType]): FunDecl = {
    val newStmt = AssignStmt(randomIdentifierOfType(NumType(), declaredIdentifiers), BinaryOp(Divide, Number(1, randomLoc()), Number(0, randomLoc()), randomLoc()), randomLoc())

    val block = getABlocktoPlugAnError(fun.block)
    val randomIndex = Random.nextInt(block.body.length)
    val (before, after) = fun.block.stmts.splitAt(randomIndex)
    FunDecl(fun.name, fun.params, FunBlockStmt(fun.block.vars, before ++ (newStmt :: after), fun.block.ret, fun.block.loc), fun.loc)
  }

  def getABlocktoPlugAnError(block: Block): Block = {
    val randomIndex = Random.nextInt(block.body.length)
    block.body(randomIndex) match {
      case IfStmt(_, thenBlock, _, _) if thenBlock.asInstanceOf[NestedBlockStmt].body.nonEmpty && (random.nextInt(1) == 0) =>
        getABlocktoPlugAnError(thenBlock.asInstanceOf[Block])
      case IfStmt(_, _, Some(elseBlock), _) if elseBlock.asInstanceOf[NestedBlockStmt].body.nonEmpty =>
        getABlocktoPlugAnError(elseBlock.asInstanceOf[Block])
      case WhileStmt(_, block, _) if block.asInstanceOf[NestedBlockStmt].body.nonEmpty =>
        getABlocktoPlugAnError(block.asInstanceOf[Block])
      case _ =>
        block
    }
  }

  def generateRandomProgram(printProgram: Boolean = true): Program = {
    val additionalFuns = List.fill(random.nextInt(3) + 1) {
      val funName = s"fun${random.nextInt(100)}"
      functionNames ::= funName
    }
    var funDecls = List[FunDecl]()
    //    for (func <- functionNames) {
    //      funDecls = funDecls :+ (randomFunDecl(func))
    //    }
    var (main, declaredIdentifier) = randomFunDecl("main")
    if (guaranteedError) {
      main = plugAnError(main, declaredIdentifier)
    }
    funDecls = funDecls :+ main
    if (printProgram) {
      funDecls.foreach(fce => println(new AstPrinter().print(fce)))
    }
    Program(funDecls, randomLoc())
  }


}

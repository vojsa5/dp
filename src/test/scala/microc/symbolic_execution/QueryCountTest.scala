package microc.symbolic_execution

import microc.analysis.{QueryCountAnalyses, SemanticAnalysis}
import microc.ast.IdentifierDecl
import microc.cfg.IntraproceduralCfgFactory
import microc.symbolic_execution.optimizations.merging.RecursionBasedAnalyses
import microc.{Examples, MicrocSupport}
import munit.FunSuite

class QueryCountTest extends FunSuite with MicrocSupport with Examples {

    test("basic for paper 3") {

        val code =
            """
              |main() {
              |  var r, arg, argc, argv, i;
              |
              |  r = 1;
              |  arg = 1;
              |  argc = input;
              |  argv = [];
              |  if (arg < argc) {
              |     if (argv[input]) {
              |        r = 0;
              |        arg = arg + 1;
              |     }
              |  }
              |  while (arg < argc) {
              |     i = 0;
              |     while (argv[arg][i] != 0) {
              |        i = i + 1;
              |        output argv[arg][i];
              |     }
              |     arg = arg + 1;
              |  }
              |  if (r) {
              |     output 10;
              |  }
              |
              |  return 0;
              |}
              |
              |""".stripMargin;

        val program = parseUnsafe(code)
        val cfg = new IntraproceduralCfgFactory().fromProgram(program)

        implicit val declarations = new SemanticAnalysis().analyze(program)

        val analyses = new QueryCountAnalyses(cfg)(declarations)
        val res = analyses.analyze()

        assert(res.find(_._1.id == 33).get._2.isEmpty)
        assert(res.find(_._1.id == 32).get._2.isEmpty)
        assert(res.find(_._1.id == 31).get._2.isEmpty)

        assert(res.find(_._1.id == 30).get._2.size >= 1)
        assert(res.find(_._1.id == 30).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 30).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)


        assert(res.find(_._1.id == 29).get._2.size >= 4)
        assert(res.find(_._1.id == 29).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 29).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 29).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 29).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 29).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 29).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 29).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 29).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 28).get._2.size >= 4)
        assert(res.find(_._1.id == 28).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 28).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 28).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 28).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 28).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 28).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 28).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 28).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 27).get._2.size >= 5)
        assert(res.find(_._1.id == 27).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 27).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 27).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 27).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 27).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 27).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 27).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 27).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 27).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 27).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)

        assert(res.find(_._1.id == 26).get._2.size >= 5)
        assert(res.find(_._1.id == 26).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 26).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 26).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 26).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 26).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 26).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 26).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 26).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 26).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 26).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)

        assert(res.find(_._1.id == 25).get._2.size >= 5)
        assert(res.find(_._1.id == 25).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 25).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 25).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 25).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 25).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 25).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 25).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 25).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 25).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 25).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)

        assert(res.find(_._1.id == 24).get._2.size >= 5)
        assert(res.find(_._1.id == 24).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 24).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 24).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 24).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 24).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 24).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 24).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 24).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 24).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 24).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)

        assert(res.find(_._1.id == 23).get._2.size >= 5)
        assert(res.find(_._1.id == 23).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 23).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 23).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 23).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 23).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 23).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 23).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 23).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 23).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 23).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)

        assert(res.find(_._1.id == 22).get._2.size >= 5)
        assert(res.find(_._1.id == 22).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 22).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 22).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 22).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 22).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 22).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 22).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 22).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 22).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 22).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)

        assert(res.find(_._1.id == 21).get._2.size >= 5)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)


        assert(res.find(_._1.id == 21).get._2.size >= 5)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 21).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 21).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)


        assert(res.find(_._1.id == 20).get._2.size >= 5)
        assert(res.find(_._1.id == 20).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 20).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 20).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 20).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 20).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 20).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 20).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 20).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 20).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 20).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)


        assert(res.find(_._1.id == 19).get._2.size >= 5)
        assert(res.find(_._1.id == 19).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 19).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 19).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 19).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 19).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 19).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 19).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 19).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 19).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 19).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)


        assert(res.find(_._1.id == 18).get._2.size >= 5)
        assert(res.find(_._1.id == 18).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 18).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 18).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 18).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 18).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 18).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 18).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 18).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 18).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 18).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)


        assert(res.find(_._1.id == 17).get._2.size >= 5)
        assert(res.find(_._1.id == 17).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 17).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 17).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 17).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 17).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 17).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 17).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 17).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)
        assert(res.find(_._1.id == 17).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 17).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 0.0)


        assert(res.find(_._1.id == 16).get._2.size >= 4)
        assert(res.find(_._1.id == 16).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 16).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 16).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 16).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 16).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 16).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 16).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 16).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 15).get._2.size >= 4)
        assert(res.find(_._1.id == 15).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 15).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 15).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 15).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 15).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 15).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 15).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 15).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 14).get._2.size >= 4)
        assert(res.find(_._1.id == 14).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 14).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 14).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 14).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 14).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 14).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 14).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 14).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 13).get._2.size >= 4)
        assert(res.find(_._1.id == 13).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 13).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 13).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 13).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 13).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 13).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 13).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 13).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 12).get._2.size >= 3)
        assert(res.find(_._1.id == 12).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 12).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 12).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 12).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 12).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 12).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 11).get._2.size >= 4)
        assert(res.find(_._1.id == 11).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 11).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 11).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 11).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 11).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 11).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 11).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 11).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 10).get._2.size >= 4)
        assert(res.find(_._1.id == 10).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 10).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 10).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 10).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 10).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 10).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 10).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 10).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 9).get._2.size >= 4)
        assert(res.find(_._1.id == 9).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 9).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 9).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 9).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 9).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 9).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 9).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 9).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 8).get._2.size >= 4)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 7).get._2.size >= 4)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 6).get._2.size >= 3)
        assert(res.find(_._1.id == 6).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 6).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 6).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 6).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)
        assert(res.find(_._1.id == 6).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 6).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 5).get._2.size >= 2)
        assert(res.find(_._1.id == 5).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 5).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 5).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 5).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)


        assert(res.find(_._1.id == 4).get._2.size >= 1)
        assert(res.find(_._1.id == 4).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 4).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)


        assert(res.find(_._1.id == 3).get._2.isEmpty)
        assert(res.find(_._1.id == 2).get._2.isEmpty)
        assert(res.find(_._1.id == 1).get._2.isEmpty)
        assert(res.find(_._1.id == 0).get._2.isEmpty)

        res
    }


    test("basic for paper 1") {
        val code =
            """
              |main() {
              |  var r, arg, argc, argv, i;
              |
              |  r = 1;
              |  arg = 1;
              |  argc = input;
              |  argv = [];
              |  if (r) {
              |     output 10;
              |  }
              |
              |  return 0;
              |}
              |
              |""".stripMargin;

        val program = parseUnsafe(code)
        val cfg = new IntraproceduralCfgFactory().fromProgram(program)

        implicit val declarations = new SemanticAnalysis().analyze(program)

        val analyses = new QueryCountAnalyses(cfg)(declarations)
        val res = analyses.analyze()

        assert(res.find(_._1.id == 9).get._2.isEmpty)
        assert(res.find(_._1.id == 8).get._2.isEmpty)
        assert(res.find(_._1.id == 7).get._2.isEmpty)

        assert(res.find(_._1.id == 6).get._2.size >= 1)
        assert(res.find(_._1.id == 6).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 6).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 5).get._2.size >= 1)
        assert(res.find(_._1.id == 5).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 5).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 4).get._2.size >= 1)
        assert(res.find(_._1.id == 4).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 4).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)


        assert(res.find(_._1.id == 3).get._2.size >= 1)
        assert(res.find(_._1.id == 3).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 3).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 2).get._2.isEmpty)
        assert(res.find(_._1.id == 1).get._2.isEmpty)
        assert(res.find(_._1.id == 0).get._2.isEmpty)

        res
    }



    test("basic for paper 1 strategy 2") {
        val code =
            """
              |main() {
              |  var r, arg, argc, argv, i;
              |
              |  r = 1;
              |  arg = 1;
              |  argc = input;
              |  argv = [];
              |  if (r) {
              |     output 10;
              |  }
              |
              |  return 0;
              |}
              |
              |""".stripMargin;


        val program = parseUnsafe(code)
        val cfg = new IntraproceduralCfgFactory().fromProgram(program);
        val tmp = new RecursionBasedAnalyses()(new SemanticAnalysis().analyze(program))

        tmp.tmp2(cfg)

        val res = tmp.mapping

        assert(res.find(_._1.id == 8).get._2.isEmpty)
        assert(res.find(_._1.id == 7).get._2.isEmpty)

        assert(res.find(_._1.id == 6).get._2.size >= 1)
        assert(res.find(_._1.id == 6).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 6).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 5).get._2.size >= 1)
        assert(res.find(_._1.id == 5).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 5).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 4).get._2.size >= 1)
        assert(res.find(_._1.id == 4).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 4).get._2.find(_._1 == "r").get._2 == 1.0)


        assert(res.find(_._1.id == 3).get._2.size >= 1)
        assert(res.find(_._1.id == 3).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 3).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 2).get._2.isEmpty)
        assert(res.find(_._1.id == 1).get._2.isEmpty)
        assert(res.find(_._1.id == 0).get._2.isEmpty)

        res
    }


    test("basic for paper 2") {

        val code =
            """
              |main() {
              |  var r, arg, argc, argv, i;
              |
              |  r = 1;
              |  arg = 1;
              |  argc = input;
              |  argv = [];
              |  if (arg < argc) {
              |     if (argv[input]) {
              |        r = 0;
              |        arg = arg + 1;
              |     }
              |  }
              |  if (r) {
              |     output 10;
              |  }
              |
              |  return 0;
              |}
              |
              |""".stripMargin;

        val program = parseUnsafe(code)
        val cfg = new IntraproceduralCfgFactory().fromProgram(program)

        implicit val declarations = new SemanticAnalysis().analyze(program)

        val analyses = new QueryCountAnalyses(cfg)(declarations)
        val res = analyses.analyze()

        assert(res.find(_._1.id == 17).get._2.isEmpty)
        assert(res.find(_._1.id == 16).get._2.isEmpty)
        assert(res.find(_._1.id == 15).get._2.isEmpty)

        assert(res.find(_._1.id == 14).get._2.size >= 1)
        assert(res.find(_._1.id == 14).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 14).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 13).get._2.size >= 1)
        assert(res.find(_._1.id == 13).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 13).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 12).get._2.size >= 0)

        assert(res.find(_._1.id == 11).get._2.size >= 1)
        assert(res.find(_._1.id == 11).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 11).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 10).get._2.size >= 2)
        assert(res.find(_._1.id == 10).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 10).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 10).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 10).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)

        assert(res.find(_._1.id == 9).get._2.size >= 2)
        assert(res.find(_._1.id == 9).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 9).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 9).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 9).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)

        assert(res.find(_._1.id == 8).get._2.size >= 2)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)

        assert(res.find(_._1.id == 7).get._2.size >= 3)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)

        assert(res.find(_._1.id == 6).get._2.size >= 2)
        assert(res.find(_._1.id == 6).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 6).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 6).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argc"))
        assert(res.find(_._1.id == 6).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argc").get._2 == 1.0)

        assert(res.find(_._1.id == 5).get._2.size >= 1)
        assert(res.find(_._1.id == 5).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 5).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)


        assert(res.find(_._1.id == 4).get._2.size >= 1)
        assert(res.find(_._1.id == 4).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 4).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 3).get._2.isEmpty)
        assert(res.find(_._1.id == 2).get._2.isEmpty)
        assert(res.find(_._1.id == 1).get._2.isEmpty)
        assert(res.find(_._1.id == 0).get._2.isEmpty)

        res

    }



    test("basic for paper 2 strategy 2") {

        val code =
            """
              |main() {
              |  var r, arg, argc, argv, i;
              |
              |  r = 1;
              |  arg = 1;
              |  argc = input;
              |  argv = [];
              |  if (arg < argc) {
              |     if (argv[input]) {
              |        r = 0;
              |        arg = arg + 1;
              |     }
              |  }
              |  if (r) {
              |     output 10;
              |  }
              |
              |  return 0;
              |}
              |
              |""".stripMargin;

        val program = parseUnsafe(code)
        val cfg = new IntraproceduralCfgFactory().fromProgram(program);
        val tmp = new RecursionBasedAnalyses()(new SemanticAnalysis().analyze(program), 1.0, 1.0)

        tmp.tmp2(cfg)

        val res = tmp.mapping

        assert(res.find(_._1.id == 16).get._2.isEmpty)
        assert(res.find(_._1.id == 15).get._2.isEmpty)

        assert(res.find(_._1.id == 14).get._2.size >= 1)
        assert(res.find(_._1.id == 14).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 14).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 13).get._2.size >= 1)
        assert(res.find(_._1.id == 13).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 13).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 12).get._2.size >= 0)

        assert(res.find(_._1.id == 11).get._2.size >= 1)
        assert(res.find(_._1.id == 11).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 11).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 10).get._2.size >= 2)
        assert(res.find(_._1.id == 10).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 10).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 10).get._2.exists(_._1 == "argv"))
        assert(res.find(_._1.id == 10).get._2.find(_._1 == "argv").get._2 == 2.0)

        assert(res.find(_._1.id == 9).get._2.size >= 2)
        assert(res.find(_._1.id == 9).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 9).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 9).get._2.exists(_._1 == "argv"))
        assert(res.find(_._1.id == 9).get._2.find(_._1 == "argv").get._2 == 2.0)

        assert(res.find(_._1.id == 8).get._2.size >= 2)
        assert(res.find(_._1.id == 8).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 8).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1 == "argv"))
        assert(res.find(_._1.id == 8).get._2.find(_._1 == "argv").get._2 == 2.0)

        assert(res.find(_._1.id == 7).get._2.size >= 3)
        assert(res.find(_._1.id == 7).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 7).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1 == "argv"))
        assert(res.find(_._1.id == 7).get._2.find(_._1 == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1 == "argc"))
        assert(res.find(_._1.id == 7).get._2.find(_._1 == "argc").get._2 == 1.0)

        assert(res.find(_._1.id == 6).get._2.size >= 2)
        assert(res.find(_._1.id == 6).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 6).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 6).get._2.exists(_._1 == "argc"))
        assert(res.find(_._1.id == 6).get._2.find(_._1 == "argc").get._2 == 1.0)

        assert(res.find(_._1.id == 5).get._2.size >= 1)
        assert(res.find(_._1.id == 5).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 5).get._2.find(_._1 == "r").get._2 == 1.0)


        assert(res.find(_._1.id == 4).get._2.size >= 1)
        assert(res.find(_._1.id == 4).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 4).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 3).get._2.isEmpty)
        assert(res.find(_._1.id == 2).get._2.isEmpty)
        assert(res.find(_._1.id == 1).get._2.isEmpty)
        assert(res.find(_._1.id == 0).get._2.isEmpty)

        res

    }


    test("basic for paper 4") {

        val code =
            """
              |main() {
              |  var r, arg, argc, argv, i;
              |
              |  r = 1;
              |  arg = 1;
              |  argc = input;
              |  argv = [];
              |  i = 0;
              |  output argv[arg][i];
              |  if (r) {
              |     output 10;
              |  }
              |
              |  return 0;
              |}
              |
              |""".stripMargin;

        val program = parseUnsafe(code)
        val cfg = new IntraproceduralCfgFactory().fromProgram(program)

        implicit val declarations = new SemanticAnalysis().analyze(program)

        val analyses = new QueryCountAnalyses(cfg)(declarations)
        val res = analyses.analyze()

        assert(res.find(_._1.id == 14).get._2.isEmpty)
        assert(res.find(_._1.id == 13).get._2.isEmpty)
        assert(res.find(_._1.id == 12).get._2.isEmpty)

        assert(res.find(_._1.id == 11).get._2.size >= 1)
        assert(res.find(_._1.id == 11).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 11).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 10).get._2.size >= 1)
        assert(res.find(_._1.id == 10).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 10).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 9).get._2.size >= 2)
        assert(res.find(_._1.id == 9).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 9).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 9).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 9).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 1.0)

        assert(res.find(_._1.id == 8).get._2.size >= 4)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "i"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "i").get._2 == 1.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 8).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)

        assert(res.find(_._1.id == 7).get._2.size >= 3)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "argv"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 7).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)

        assert(res.find(_._1.id == 6).get._2.size >= 2)
        assert(res.find(_._1.id == 6).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 6).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 6).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 6).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)

        assert(res.find(_._1.id == 5).get._2.size >= 2)
        assert(res.find(_._1.id == 5).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 5).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 5).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "arg"))
        assert(res.find(_._1.id == 5).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "arg").get._2 == 2.0)

        assert(res.find(_._1.id == 4).get._2.size >= 1)
        assert(res.find(_._1.id == 4).get._2.exists(_._1.asInstanceOf[IdentifierDecl].name == "r"))
        assert(res.find(_._1.id == 4).get._2.find(_._1.asInstanceOf[IdentifierDecl].name == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 3).get._2.isEmpty)
        assert(res.find(_._1.id == 2).get._2.isEmpty)
        assert(res.find(_._1.id == 1).get._2.isEmpty)
        assert(res.find(_._1.id == 0).get._2.isEmpty)

    }



    test("basic for paper 4 strategy 2") {

        val code =
            """
              |main() {
              |  var r, arg, argc, argv, i;
              |
              |  r = 1;
              |  arg = 1;
              |  argc = input;
              |  argv = [];
              |  i = 0;
              |  output argv[arg][i];
              |  if (r) {
              |     output 10;
              |  }
              |
              |  return 0;
              |}
              |
              |""".stripMargin;

        val program = parseUnsafe(code)
        val cfg = new IntraproceduralCfgFactory().fromProgram(program);
        val tmp = new RecursionBasedAnalyses()(new SemanticAnalysis().analyze(program))

        tmp.tmp2(cfg)

        val res = tmp.mapping

        assert(res.find(_._1.id == 13).get._2.isEmpty)
        assert(res.find(_._1.id == 12).get._2.isEmpty)

        assert(res.find(_._1.id == 11).get._2.size >= 1)
        assert(res.find(_._1.id == 11).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 11).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 10).get._2.size >= 1)
        assert(res.find(_._1.id == 10).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 10).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 9).get._2.size >= 2)
        assert(res.find(_._1.id == 9).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 9).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 9).get._2.exists(_._1 == "i"))
        assert(res.find(_._1.id == 9).get._2.find(_._1 == "i").get._2 == 1.0)

        assert(res.find(_._1.id == 8).get._2.size >= 4)
        assert(res.find(_._1.id == 8).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 8).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1 == "i"))
        assert(res.find(_._1.id == 8).get._2.find(_._1 == "i").get._2 == 1.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1 == "argv"))
        assert(res.find(_._1.id == 8).get._2.find(_._1 == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 8).get._2.exists(_._1 == "arg"))
        assert(res.find(_._1.id == 8).get._2.find(_._1 == "arg").get._2 == 2.0)

        assert(res.find(_._1.id == 7).get._2.size >= 3)
        assert(res.find(_._1.id == 7).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 7).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1 == "argv"))
        assert(res.find(_._1.id == 7).get._2.find(_._1 == "argv").get._2 == 2.0)
        assert(res.find(_._1.id == 7).get._2.exists(_._1 == "arg"))
        assert(res.find(_._1.id == 7).get._2.find(_._1 == "arg").get._2 == 2.0)

        assert(res.find(_._1.id == 6).get._2.size >= 2)
        assert(res.find(_._1.id == 6).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 6).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 6).get._2.exists(_._1 == "arg"))
        assert(res.find(_._1.id == 6).get._2.find(_._1 == "arg").get._2 == 2.0)

        assert(res.find(_._1.id == 5).get._2.size >= 2)
        assert(res.find(_._1.id == 5).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 5).get._2.find(_._1 == "r").get._2 == 1.0)
        assert(res.find(_._1.id == 5).get._2.exists(_._1 == "arg"))
        assert(res.find(_._1.id == 5).get._2.find(_._1 == "arg").get._2 == 2.0)

        assert(res.find(_._1.id == 4).get._2.size >= 1)
        assert(res.find(_._1.id == 4).get._2.exists(_._1 == "r"))
        assert(res.find(_._1.id == 4).get._2.find(_._1 == "r").get._2 == 1.0)

        assert(res.find(_._1.id == 3).get._2.isEmpty)
        assert(res.find(_._1.id == 2).get._2.isEmpty)
        assert(res.find(_._1.id == 1).get._2.isEmpty)
        assert(res.find(_._1.id == 0).get._2.isEmpty)

    }


    test("basic for paper 6") {

        val code =
            """
              |main() {
              |  var r, arg, argc, argv, i;
              |
              |  r = 1;
              |  arg = 1;
              |  argc = input;
              |  argv = [];
              |  i = 0;
              |  while (argv[arg][i] != 0) {
              |     i = i + 1;
              |     output argv[arg][i];
              |  }
              |  arg = arg + 1;
              |
              |  return 0;
              |}
              |
              |""".stripMargin;


        val program = parseUnsafe(code)
        val cfg = new IntraproceduralCfgFactory().fromProgram(program)

        implicit val declarations = new SemanticAnalysis().analyze(program)

        val analyses = new QueryCountAnalyses(cfg)(declarations)
        val res = analyses.analyze()

        null
    }


    test("basic for paper 5") {

        val code =
            """
              |main() {
              |  var r, arg, argc, argv, i;
              |
              |  r = 1;
              |  arg = 1;
              |  argc = input;
              |  argv = [];
              |  while (arg < argc) {
              |     i = 0;
              |     while (argv[arg][i] != 0) {
              |        i = i + 1;
              |        output argv[arg][i];
              |     }
              |     arg = arg + 1;
              |  }
              |
              |  return 0;
              |}
              |
              |""".stripMargin;


        val program = parseUnsafe(code)
        val cfg = new IntraproceduralCfgFactory().fromProgram(program)

        implicit val declarations = new SemanticAnalysis().analyze(program)

        val analyses = new QueryCountAnalyses(cfg)(declarations)
        val res = analyses.analyze()

        null
    }
}

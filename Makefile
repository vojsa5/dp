.PHONY: all
all: assembly

.PHONY: assembly
assembly:
	sbt assembly

.PHONY: test
test:
	sbt "testOnly microc.symbolic_execution.BfTest"
	sbt "testOnly microc.symbolic_execution.CFGfactoryTest"
	sbt "testOnly microc.symbolic_execution.ConstraintSolverTest"
	sbt "testOnly microc.symbolic_execution.LoopSummarizationTest"
	sbt "testOnly microc.symbolic_execution.PathSubsumptionTest"
	sbt "testOnly microc.symbolic_execution.QueryCountTest"
	sbt "testOnly microc.symbolic_execution.SpecialCasesTest"
	sbt "testOnly microc.symbolic_execution.SymbolicExecutorBasicTest"
	sbt "testOnly microc.symbolic_execution.SymbolicExecutorTest"
	sbt "testOnly microc.symbolic_execution.SymbolicExecutorTest2"
	sbt "testOnly microc.symbolic_execution.SymbolicExecutorTest3"
	sbt "testOnly microc.symbolic_execution.SymbolicStoreTest"

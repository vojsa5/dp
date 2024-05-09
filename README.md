# dp


run tests with: 

`make test`

generate a random program with:

`sbt "runMain microc.cli.Main generateProgram --program example.uc "`

read the generated program:

`cat example.uc`

symbolically execute a program:

`sbt "runMain microc.cli.Main symbolicallyExecute --program example.uc --output ."`

read the path coverage:

`cat coverage.txt`

read the time to execute in ms:

`cat time.txt`

read the number of errors:

`cat error.txt`

find out how long the precomputation of query count analyses is:

`sbt "runMain microc.cli.Main precomputeVariableCosts --program example.uc --merging-strategy lattice-based --output output.txt"`

read the time to execute in ms:

`cat output.txt`

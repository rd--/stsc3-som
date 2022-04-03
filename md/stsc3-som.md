# stsc3-som

Command line stsc3-som.

## repl

Repl for a simple implementation of the Simple Object Model.
It reads the location of class library files from the environment variable `SOM_CLASS_PATH`.

~~~~
# echo $SOM_CLASS_PATH
./SOM-st/SOM/Smalltalk:./SOM-st/SOM/TestSuite:./are-we-fast-yet/benchmarks/SOM
$ stsc3-som repl
> TestHarness new run: #('TestHarness.som')
...
Total number of tests:           201
Number of unsupported optionals: 3
Number of successful tests:      201
Number of assertions tested:     1072
> Harness new run: #('Harness' 'Bounce')
...
Total Runtime: 329669us
^D
$ stsc3-som run TestHarness
...
$
~~~~

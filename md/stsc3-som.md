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
Number of assertions tested:     1074
> Harness new run: #('Harness' 'Bounce')
...
Total Runtime: 329669us
^D
$ stsc3-som run TestHarness
...
$
~~~~

There is a Som interpreter written in Som.

To load, the class path should be set to:

> Smalltalk:TestSuite:SomSom/src/compiler:SomSom/src/vm:SomSom/src/vmobjects:SomSom/src/interpreter:SomSom/src/primitives

To run type:

> stsc3-som run Main -cp Smalltalk ./Examples/Hello.som

It currently fails for the test suite, the error after _Double class>>fromString:_ fails (indicated by returning _NaN_).

> stsc3-som run Main -cp Smalltalk ./TestSuite/TestHarness.som

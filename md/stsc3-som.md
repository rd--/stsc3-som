# stsc3-som

Command line stsc3-som.

## repl

Repl for a simple implementation of the Simple Object Model.
It reads the location of class library files from the environment variable `SOM_CLASS_PATH`.

~~~~
$ export SOM_CLASS_PATH=./SOM-st/SOM/Smalltalk:./SOM-st/SOM/TestSuite:./smarr/are-we-fast-yet/benchmarks/SOM
$ stsc3-som -cp $SOM_CLASS_PATH som repl
> 3 + 4
result<pc=0>: 7
> TestHarness new run: #('TestHarness.som')
...
> Harness new run: #('Harness' 'Bounce')
...
^D
$ time stsc3-som -cp $SOM_CLASS_PATH run TestHarness
Total number of tests:           208
Number of unsupported optionals: 3
Number of successful tests:      208
Number of assertions tested:     1096
$
~~~~

There is a Som interpreter written in Som.

To load, the class path should be set to:

> Smalltalk:TestSuite:SomSom/src/compiler:SomSom/src/vm:SomSom/src/vmobjects:SomSom/src/interpreter:SomSom/src/primitives

To run type:

> stsc3-som run Main -cp Smalltalk ./Examples/Hello.som

It currently fails for the test suite, the error after _Double class>>fromString:_ fails (indicated by returning _NaN_).

> stsc3-som run Main -cp Smalltalk ./TestSuite/TestHarness.som

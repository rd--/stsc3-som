# stsc3-som

Command line stsc3-som.

## repl

Repl for a simple implementation of the Simple Object Model.
It reads the location of class library files from the environment variable `SOM_CLASS_PATH`.

~~~~
$ stsc3-som repl
> TestHarness new run: #('TestHarness.som')
...
Total number of tests:           122
Number of unsupported optionals: 3
Number of successful tests:      122
Number of assertions tested:     640
> Harness new run: #('Harness' 'Bounce')
...
Total Runtime: 1924501us
^D
$
~~~~

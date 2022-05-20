"Som"
TestHarness new run: #('TestHarness.som'). "=> 201, 1074"
TestHarness new run: #('TestHarness.som' 'ArrayTest').
TestHarness new run: #('TestHarness.som' 'BlockTest').
TestHarness new run: #('TestHarness.som' 'ClassLoadingTest').
TestHarness new run: #('TestHarness.som' 'ClassStructureTest').
TestHarness new run: #('TestHarness.som' 'ClosureTest').
TestHarness new run: #('TestHarness.som' 'CoercionTest').
TestHarness new run: #('TestHarness.som' 'CompilerReturnTest').
TestHarness new run: #('TestHarness.som' 'DoesNotUnderstandTest').
TestHarness new run: #('TestHarness.som' 'DoubleTest').
TestHarness new run: #('TestHarness.som' 'EmptyTest').
TestHarness new run: #('TestHarness.som' 'GlobalTest').
TestHarness new run: #('TestHarness.som' 'HashTest').
TestHarness new run: #('TestHarness.som' 'IntegerTest').
TestHarness new run: #('TestHarness.som' 'PreliminaryTest').
TestHarness new run: #('TestHarness.som' 'ReflectionTest').
TestHarness new run: #('TestHarness.som' 'SelfBlockTest').
TestHarness new run: #('TestHarness.som' 'SetTest').
TestHarness new run: #('TestHarness.som' 'SpecialSelectorsTest').
TestHarness new run: #('TestHarness.som' 'StringTest').
TestHarness new run: #('TestHarness.som' 'SuperTest').
TestHarness new run: #('TestHarness.som' 'SymbolTest').
TestHarness new run: #('TestHarness.som' 'SystemTest').
TestHarness new run: #('TestHarness.som' 'VectorTest').

"Micro Benchmarks"
Harness new run: #('Harness' 'Bounce').
Harness new run: #('Harness' 'List').
Harness new run: #('Harness' 'Permute').
Harness new run: #('Harness' 'Queens').
Harness new run: #('Harness' 'Sieve').
Harness new run: #('Harness' 'Storage').
Harness new run: #('Harness' 'Towers').

"Benchmarks"
Harness new run: #('Harness' 'CD' '1' '2'). "? Method cos not found in class Integer"
Harness new run: #('Harness' 'DeltaBlue' '1' '15').
Harness new run: #('Harness' 'Havlak' '1' '1')
Harness new run: #('Harness' 'Json'). "=> 32446672us"
Harness new run: #('Harness' 'Mandelbrot' '1' '1') "=> 2865us"
Harness new run: #('Harness' 'NBody' '1' '1') "=> 15594us"
Harness new run: #('Harness' 'NBody' '1' '250000')
Harness new run: #('Harness' 'Richards').

(system load: #Array) = Array "=> true"
(system load: #UnknownClass) = nil "=> true"
(1 perform: #class inSuperclass: Object) = Integer "=> true"
(1 perform: #class) = Integer "=> true"
(perform: #+ withArguments: #(2) inSuperclass: Object)
(1 perform: #+ withArguments: #(2)) = 3 "=> true"
0 class = Integer "=> true"
0 class class = Integer class "=> true"
0 class class class = Metaclass "=> true"
Metaclass class class = Metaclass "=> true"
(system global: #Nil) = Nil "=> true"
(system global: #UnknownObject) = nil "=> true"
system loadFile: '/etc/passwd'

"Emacs"
(setq stsc3-interpreter (list "stsc3-som" "som" "repl"))
(setq stsc3-interpreter (list "gst"))

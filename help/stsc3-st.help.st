
ArrayTest run: #testAtWrap
ArrayTest run: #testEmpty
ArrayTest run: #testIsArray
ArrayTest run: #testIsLiteral
ArrayTest run: #testLiteralEqual
ArrayTest run: #testNewWithSize
ArrayTest run: #testPremultiply

CollectionTest suite run

CollectionTest run: #testAny "Block escapes"
CollectionTest run: #testAnyAs "Block escapes"
CollectionTest run: #testCollectAs
CollectionTest run: #testDetectIfFound
CollectionTest run: #testHistogramOf
CollectionTest run: #testIfEmpty
CollectionTest run: #testIfEmptyifNotEmpty
CollectionTest run: #testIfEmptyifNotEmptyDo
CollectionTest run: #testIfNotEmpty
CollectionTest run: #testIfNotEmptyDo
CollectionTest run: #testIfNotEmptyDoifEmpty
CollectionTest run: #testIfEmptyifNotEmpty
CollectionTest run: #testMinMax
CollectionTest run: #testPrintOnDelimiterLast
CollectionTest run: #testReduce
CollectionTest run: #testTake

FalseTest suite run
FalseTest run: #testAND
FalseTest run: #testAnd
FalseTest run: #testAsBit
FalseTest run: #testIfFalse
FalseTest run: #testIfFalseIfTrue
FalseTest run: #testIfTrue
FalseTest run: #testIfTrueIfFalse
FalseTest run: #testNot
FalseTest run: #testOR
FalseTest run: #testOr
FalseTest run: #testPrintOn
FalseTest run: #testXor

SequenceableCollectionTest run: #testAfterIfAbsent
SequenceableCollectionTest run: #testAtAllPut
SequenceableCollectionTest run: #testBeforeIfAbsent
SequenceableCollectionTest run: #testBeginsWith
SequenceableCollectionTest run: #testBeginsWithAnyOf
SequenceableCollectionTest run: #testConcatenation
SequenceableCollectionTest run: #testCopyWith
SequenceableCollectionTest run: #testEndsWith
SequenceableCollectionTest run: #testEndsWithAnyOf
SequenceableCollectionTest run: #testFlatten
SequenceableCollectionTest run: #testFlatten2 "Generator"
SequenceableCollectionTest run: #testFlattened
SequenceableCollectionTest run: #testGroupsDo
SequenceableCollectionTest run: #testIndexOfSubCollectionStartingAt
SequenceableCollectionTest run: #testJoin
SequenceableCollectionTest run: #testPreMultiplyByArray
SequenceableCollectionTest run: #testReplaceFromToWithStartingAt
SequenceableCollectionTest run: #testSplitAndJoin
SequenceableCollectionTest run: #testSplitBy
SequenceableCollectionTest run: #testWithCollect
SequenceableCollectionTest run: #testWithDo

t := CollectionTest new
t setUp
t testDetectIfFound

"Emacs"
(setq stsc3-interpreter (list "stsc3-st"))

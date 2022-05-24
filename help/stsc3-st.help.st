CollectionTest suite run

CollectionTest run: #testAny "Block escapes"
CollectionTest run: #testAnyAs "Block escapes"
CollectionTest run: #testCollectAs
CollectionTest run: #testDetectIfFound
CollectionTest run: #testIfEmpty
CollectionTest run: #testIfEmptyifNotEmpty
CollectionTest run: #testMinMax
CollectionTest run: #testReduce
CollectionTest run: #testTake

ArrayTest run: #testAtWrap
ArrayTest run: #testEmpty
ArrayTest run: #testIsArray
ArrayTest run: #testIsLiteral
ArrayTest run: #testLiteralEqual
ArrayTest run: #testNewWithSize
ArrayTest run: #testPremultiply

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

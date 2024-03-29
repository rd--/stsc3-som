"Since classes are loaded lazily, asking for TestCase subclasses initially gives an empty set"
allTests := {ArrayTest. AssociationTest. BagTest. BitSetTest. BlockClosureTest. ByteArrayTest. ChainedSortFunctionTest. CharacterTest. CollectionTest. ComplexTest. DateAndTimeTest. DateTest. DictionaryTest. DurationTest. FalseTest. FloatTest. FractionTest. GeneratorTest. HeapTest. IdentityBagTest. IntegerTest. IntegerDigitLogicTest. IntervalTest. JsonTest. KeyedSetTest. LinkedListTest. LRUCacheTest. MatrixTest. MessageSendTest. MonthTest. NumberTest. NumberParsingTest. ObjectTest. OrderedCollectionTest. OrderedDictionaryTest. RandomTest. ReadStreamTest. ReadWriteStreamTest. RunArrayTest. RxMatcherTest. RxParserTest. ScaledDecimalTest. SequenceableCollectionTest. SetTest. SetWithNilTest. SmallIntegerTest. SortFunctionTest. SortedCollectionTest. SqNumberParserTest. StackTest. StringTest. SymbolTest. TimeTest. TimespanTest. TimeStampTest. TrueTest. UndefinedObjectTest. WeekTest. WriteStreamTest. YearTest. "Non-class tests: " HexTest. TestSpaceshipOperator. }

"Run all tests"
allTests do: [ :each | each suite run printOn: Transcript ]

allTests size = 62
TestCase subclasses size = 62

"Individual tests"
ArrayTest testSelectors do: [ :each | Transcript show: each; cr. ArrayTest run: each ]
ArrayTest suite run printOn: Transcript

AssociationTest testSelectors do: [ :each | Transcript show: each; cr. AssociationTest run: each ]
AssociationTest suite run printOn: Transcript

BagTest testSelectors do: [ :each | Transcript show: each; cr. BagTest run: each ]
BagTest suite run printOn: Transcript

BitSetTest testSelectors do: [ :each | Transcript show: each; cr. BitSetTest run: each ]
BitSetTest suite run printOn: Transcript

BlockClosureTest testSelectors do: [ :each | Transcript show: each; cr. BlockClosureTest run: each ]
BlockClosureTest suite run printOn: Transcript

ByteArrayTest testSelectors do: [ :each | Transcript show: each; cr. ByteArrayTest run: each ]
ByteArrayTest suite run printOn: Transcript

ChainedSortFunctionTest testSelectors do: [ :each | Transcript show: each; cr. ChainedSortFunctionTest run: each ]
ChainedSortFunctionTest suite run printOn: Transcript

CharacterTest testSelectors do: [ :each | Transcript show: each; cr. CharacterTest run: each ]
CharacterTest suite run printOn: Transcript

CollectionTest testSelectors do: [ :each | Transcript show: each; cr. CollectionTest run: each ]
CollectionTest suite run printOn: Transcript

ComplexTest testSelectors do: [ :each | Transcript show: each; cr. ComplexTest run: each ]
ComplexTest suite run printOn: Transcript

DateAndTimeTest testSelectors do: [ :each | Transcript show: each; cr. DateAndTimeTest run: each ]
DateAndTimeTest suite run printOn: Transcript

DateTest testSelectors do: [ :each | Transcript show: each; cr. DateTest run: each ]
DateTest suite run printOn: Transcript

DictionaryTest testSelectors do: [ :each | Transcript show: each; cr. DictionaryTest run: each ]
DictionaryTest suite run printOn: Transcript

DurationTest testSelectors do: [ :each | Transcript show: each; cr. DurationTest run: each ]
DurationTest suite run printOn: Transcript

ExtendedNumberParserTest testSelectors do: [ :each | Transcript show: each; cr. ExtendedNumberParserTest run: each ]
ExtendedNumberParserTest suite run printOn: Transcript

FalseTest testSelectors do: [ :each | Transcript show: each; cr. FalseTest run: each ]
FalseTest suite run printOn: Transcript

FloatTest testSelectors do: [ :each | Transcript show: each; cr. FloatTest run: each ]
FloatTest suite run printOn: Transcript

FractionTest testSelectors do: [ :each | Transcript show: each; cr. FractionTest run: each ]
FractionTest suite run printOn: Transcript

GeneratorTest testSelectors do: [ :each | Transcript show: each; cr. GeneratorTest run: each ]
GeneratorTest suite run printOn: Transcript

HeapTest testSelectors do: [ :each | Transcript show: each; cr. HeapTest run: each ]
HeapTest suite run printOn: Transcript

IdentityBagTest testSelectors do: [ :each | Transcript show: each; cr. IdentityBagTest run: each ]
IdentityBagTest suite run printOn: Transcript

IntegerTest testSelectors do: [ :each | Transcript show: each; cr. IntegerTest run: each ]
IntegerTest suite run printOn: Transcript

IntegerDigitLogicTest testSelectors do: [ :each | Transcript show: each; cr. IntegerDigitLogicTest run: each ]
IntegerDigitLogicTest suite run printOn: Transcript

IntervalTest testSelectors do: [ :each | Transcript show: each; cr. IntervalTest run: each ]
IntervalTest suite run printOn: Transcript

KeyedSetTest testSelectors do: [ :each | Transcript show: each; cr. KeyedSetTest run: each ]
KeyedSetTest suite run printOn: Transcript

JsonTest testSelectors do: [ :each | Transcript show: each; cr. JsonTest run: each ]
JsonTest suite run printOn: Transcript

LinkedListTest testSelectors do: [ :each | Transcript show: each; cr. LinkedListTest run: each ]
LinkedListTest suite run printOn: Transcript

LRUCacheTest testSelectors do: [ :each | Transcript show: each; cr. LRUCacheTest run: each ]
LRUCacheTest suite run printOn: Transcript

MatrixTest testSelectors do: [ :each | Transcript show: each; cr. MatrixTest run: each ]
MatrixTest suite run printOn: Transcript

MessageSendTest testSelectors do: [ :each | Transcript show: each; cr. MessageSendTest run: each ]
MessageSendTest suite run printOn: Transcript

MonthTest testSelectors do: [ :each | Transcript show: each; cr. MonthTest run: each ]
MonthTest suite run printOn: Transcript

NumberTest testSelectors do: [ :each | Transcript show: each; cr. NumberTest run: each ]
NumberTest suite run printOn: Transcript

NumberParsingTest testSelectors do: [ :each | Transcript show: each; cr. NumberParsingTest run: each ]
NumberParsingTest suite run printOn: Transcript

ObjectTest testSelectors do: [ :each | Transcript show: each; cr. ObjectTest run: each ]
ObjectTest suite run printOn: Transcript

OrderedCollectionTest testSelectors do: [ :each | Transcript show: each; cr. OrderedCollectionTest run: each ]
OrderedCollectionTest suite run printOn: Transcript

OrderedDictionaryTest testSelectors do: [ :each | Transcript show: each; cr. OrderedDictionaryTest run: each ]
OrderedDictionaryTest suite run printOn: Transcript

RandomTest testSelectors do: [ :each | Transcript show: each; cr. RandomTest run: each ]
RandomTest suite run printOn: Transcript

ReadStreamTest testSelectors do: [ :each | Transcript show: each; cr. ReadStreamTest run: each ]
ReadStreamTest suite run printOn: Transcript

ReadWriteStreamTest testSelectors do: [ :each | Transcript show: each; cr. ReadWriteStreamTest run: each ]
ReadWriteStreamTest suite run printOn: Transcript

RunArrayTest testSelectors do: [ :each | Transcript show: each; cr. RunArrayTest run: each ]
RunArrayTest suite run printOn: Transcript

RxMatcherTest testSelectors do: [ :each | Transcript show: each; cr. RxMatcherTest run: each ]
RxMatcherTest suite run printOn: Transcript

RxParserTest testSelectors do: [ :each | Transcript show: each; cr. RxParserTest run: each ]
RxParserTest suite run printOn: Transcript

ScaledDecimalTest testSelectors do: [ :each | Transcript show: each; cr. ScaledDecimalTest run: each ]
ScaledDecimalTest suite run printOn: Transcript

SequenceableCollectionTest testSelectors do: [ :each | Transcript show: each; cr. SequenceableCollectionTest run: each ]
SequenceableCollectionTest suite run printOn: Transcript

SetTest testSelectors do: [ :each | Transcript show: each; cr. SetTest run: each ]
SetTest suite run printOn: Transcript

SetWithNilTest testSelectors do: [ :each | Transcript show: each; cr. SetWithNilTest run: each ]
SetWithNilTest suite run printOn: Transcript

SmallIntegerTest testSelectors do: [ :each | Transcript show: each; cr. SmallIntegerTest run: each ]
SmallIntegerTest suite run printOn: Transcript

SortedCollectionTest testSelectors do: [ :each | Transcript show: each; cr. SortedCollectionTest run: each ]
SortedCollectionTest suite run printOn: Transcript

SortFunctionTest testSelectors do: [ :each | Transcript show: each; cr. SortFunctionTest run: each ]
SortFunctionTest suite run printOn: Transcript

SqNumberParserTest testSelectors do: [ :each | Transcript show: each; cr. SqNumberParserTest run: each ]
SqNumberParserTest suite run printOn: Transcript

StackTest testSelectors do: [ :each | Transcript show: each; cr. StackTest run: each ]
StackTest suite run printOn: Transcript

StringTest testSelectors do: [ :each | Transcript show: each; cr. StringTest run: each ]
StringTest suite run printOn: Transcript

SymbolTest testSelectors do: [ :each | Transcript show: each; cr. SymbolTest run: each ]
SymbolTest suite run printOn: Transcript

TimeTest testSelectors do: [ :each | Transcript show: each; cr. TimeTest run: each ]
TimeTest suite run printOn: Transcript

TimespanTest testSelectors do: [ :each | Transcript show: each; cr. TimespanTest run: each ]
TimespanTest suite run printOn: Transcript

TimeStampTest testSelectors do: [ :each | Transcript show: each; cr. TimeStampTest run: each ]
TimeStampTest suite run printOn: Transcript

TrueTest testSelectors do: [ :each | Transcript show: each; cr. TrueTest run: each ]
TrueTest suite run printOn: Transcript

UndefinedObjectTest testSelectors do: [ :each | Transcript show: each; cr. UndefinedObjectTest run: each ]
UndefinedObjectTest suite run printOn: Transcript

WeekTest testSelectors do: [ :each | Transcript show: each; cr. WeekTest run: each ]
WeekTest suite run printOn: Transcript

WriteStreamTest testSelectors do: [ :each | Transcript show: each; cr. WriteStreamTest run: each ]
WriteStreamTest suite run printOn: Transcript

YearTest testSelectors do: [ :each | Transcript show: each; cr. YearTest run: each ]
YearTest suite run printOn: Transcript

"Non-class tests"
HexTest testSelectors do: [ :each | Transcript show: each; cr. HexTest run: each ]
HexTest suite run printOn: Transcript

TestSpaceshipOperator testSelectors do: [ :each | Transcript show: each; cr. TestSpaceshipOperator run: each ]
TestSpaceshipOperator suite run printOn: Transcript

Smalltalk globalKeys
Smalltalk globals
Smalltalk utcTime
Smalltalk utcOffset
{Smalltalk utcTime. Smalltalk utcOffset}

'Thread'

[ [ (Delay forSeconds: 3) wait. Transcript nextPutAll: 'thread'; cr ] fork. Transcript nextPutAll: 'main'; cr ] value "prints main then thread"
[ | thread | thread := [ (Delay forSeconds: 1) wait. Transcript nextPutAll: 'thread'; cr ] fork. thread kill. ] value "won't print anything..."
[ | mvar | mvar := MVar new. [ (Delay forSeconds: 3) wait. mvar nextPut: 'delayed' ] fork. Transcript nextPutAll: mvar next; cr ] value "print after delay"

"These classes currently don't work because Som has no notation for declaring a variableSubclass:"
SparseLargeArrayTest testSelectors do: [ :each | Transcript show: each; cr. SparseLargeArrayTest run: each ]
SparseLargeArrayTest suite run printOn: Transcript

SparseLargeTableTest testSelectors do: [ :each | Transcript show: each; cr. SparseLargeTableTest run: each ]
SparseLargeTableTest suite run printOn: Transcript

"Emacs"
(setq stsc3-interpreter (list "stsc3-st"))
(setq stsc3-interpreter (list "gst"))

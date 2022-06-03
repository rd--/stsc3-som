ArrayTest testSelectors do: [ :each | Transcript show: each; cr. ArrayTest run: each ]
ArrayTest suite run printOn: Transcript

AssociationTest testSelectors do: [ :each | Transcript show: each; cr. AssociationTest run: each ]
AssociationTest suite run printOn: Transcript

BagTest testSelectors do: [ :each | Transcript show: each; cr. BagTest run: each ]
BagTest suite run printOn: Transcript

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

DateAndTimeTest testSelectors do: [ :each | Transcript show: each; cr. DateAndTimeTest run: each ]
DateAndTimeTest suite run printOn: Transcript

DateTest testSelectors do: [ :each | Transcript show: each; cr. DateTest run: each ]
DateTest suite run printOn: Transcript

DictionaryTest testSelectors do: [ :each | Transcript show: each; cr. DictionaryTest run: each ]
DictionaryTest suite run printOn: Transcript

DurationTest testSelectors do: [ :each | Transcript show: each; cr. DurationTest run: each ]
DurationTest suite run printOn: Transcript

FalseTest testSelectors do: [ :each | Transcript show: each; cr. FalseTest run: each ]
FalseTest suite run printOn: Transcript

FloatTest testSelectors do: [ :each | Transcript show: each; cr. FloatTest run: each ]
FloatTest suite run printOn: Transcript

FractionTest testSelectors do: [ :each | Transcript show: each; cr. FractionTest run: each ]
FractionTest suite run printOn: Transcript

HeapTest testSelectors do: [ :each | Transcript show: each; cr. HeapTest run: each ]
HeapTest suite run printOn: Transcript

IdentityBagTest testSelectors do: [ :each | Transcript show: each; cr. IdentityBagTest run: each ]
IdentityBagTest suite run printOn: Transcript

IntegerTest testSelectors do: [ :each | Transcript show: each; cr. IntegerTest run: each ]
IntegerTest suite run printOn: Transcript

IntervalTest testSelectors do: [ :each | Transcript show: each; cr. IntervalTest run: each ]
IntervalTest suite run printOn: Transcript

LinkedListTest testSelectors do: [ :each | Transcript show: each; cr. LinkedListTest run: each ]
LinkedListTest suite run printOn: Transcript

MatrixTest testSelectors do: [ :each | Transcript show: each; cr. MatrixTest run: each ]
MatrixTest suite run printOn: Transcript

MonthTest testSelectors do: [ :each | Transcript show: each; cr. MonthTest run: each ]
MonthTest suite run printOn: Transcript

NumberTest testSelectors do: [ :each | Transcript show: each; cr. NumberTest run: each ]
NumberTest suite run printOn: Transcript

ObjectTest testSelectors do: [ :each | Transcript show: each; cr. ObjectTest run: each ]
ObjectTest suite run printOn: Transcript

OrderedCollectionTest testSelectors do: [ :each | Transcript show: each; cr. OrderedCollectionTest run: each ]
OrderedCollectionTest suite run printOn: Transcript

ReadStreamTest testSelectors do: [ :each | Transcript show: each; cr. ReadStreamTest run: each ]
ReadStreamTest suite run printOn: Transcript

ReadWriteStreamTest testSelectors do: [ :each | Transcript show: each; cr. ReadWriteStreamTest run: each ]
ReadWriteStreamTest suite run printOn: Transcript

SequenceableCollectionTest testSelectors do: [ :each | Transcript show: each; cr. SequenceableCollectionTest run: each ]
SequenceableCollectionTest suite run printOn: Transcript

SetTest testSelectors do: [ :each | Transcript show: each; cr. SetTest run: each ]
SetTest suite run printOn: Transcript

SmallIntegerTest testSelectors do: [ :each | Transcript show: each; cr. SmallIntegerTest run: each ]
SmallIntegerTest suite run printOn: Transcript

SortFunctionTest testSelectors do: [ :each | Transcript show: each; cr. SortFunctionTest run: each ]
SortFunctionTest suite run printOn: Transcript

SortedCollectionTest testSelectors do: [ :each | Transcript show: each; cr. SortedCollectionTest run: each ]
SortedCollectionTest suite run printOn: Transcript

SpaceshipOperatorTest testSelectors do: [ :each | Transcript show: each; cr. SpaceshipOperatorTest run: each ]
SpaceshipOperatorTest suite run printOn: Transcript

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

Smalltalk utcTime
Smalltalk utcOffset
{Smalltalk utcTime. Smalltalk utcOffset}

'Thread'

[ [ (Delay forSeconds: 3) wait. Transcript nextPutAll: 'thread'; cr ] fork. Transcript nextPutAll: 'main'; cr ] value "prints main then thread"
[ | thread | thread := [ (Delay forSeconds: 1) wait. Transcript nextPutAll: 'thread'; cr ] fork. thread kill. ] value "won't print anything..."
[ | mvar | mvar := MVar new. [ (Delay forSeconds: 3) wait. mvar nextPut: 'delayed' ] fork. Transcript nextPutAll: mvar next; cr ] value "print after delay"

"Emacs"
(setq stsc3-interpreter (list "stsc3-st"))

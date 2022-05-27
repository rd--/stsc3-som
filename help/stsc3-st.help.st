ArrayTest testSelectors do: [ :each | Transcript show: each; cr. ArrayTest run: each ]
ArrayTest suite run printOn: Transcript

CollectionTest testSelectors do: [ :each | Transcript show: each; cr. CollectionTest run: each ]
CollectionTest suite run printOn: Transcript

FalseTest testSelectors do: [ :each | Transcript show: each; cr. FalseTest run: each ]
FalseTest suite run printOn: Transcript

FloatTest testSelectors do: [ :each | Transcript show: each; cr. FloatTest run: each ]
FloatTest suite run printOn: Transcript

IntegerTest testSelectors do: [ :each | Transcript show: each; cr. IntegerTest run: each ]
IntegerTest suite run printOn: Transcript

IntervalTest testSelectors do: [ :each | Transcript show: each; cr. IntervalTest run: each ]
IntervalTest suite run printOn: Transcript

NumberTest testSelectors do: [ :each | Transcript show: each; cr. NumberTest run: each ]
NumberTest suite run printOn: Transcript

OrderedCollectionTest testSelectors do: [ :each | Transcript show: each; cr. OrderedCollectionTest run: each ]
OrderedCollectionTest suite run printOn: Transcript

ReadStreamTest testSelectors do: [ :each | Transcript show: each; cr. ReadStreamTest run: each ]
ReadStreamTest suite run printOn: Transcript

ReadWriteStreamTest testSelectors do: [ :each | Transcript show: each; cr. ReadWriteStreamTest run: each ]
ReadWriteStreamTest suite run printOn: Transcript

SequenceableCollectionTest testSelectors do: [ :each | Transcript show: each; cr. SequenceableCollectionTest run: each ]
SequenceableCollectionTest suite run printOn: Transcript

SmallIntegerTest testSelectors do: [ :each | Transcript show: each; cr. SmallIntegerTest run: each ]
SmallIntegerTest suite run printOn: Transcript

SortedCollectionTest testSelectors do: [ :each | Transcript show: each; cr. SortedCollectionTest run: each ]
SortedCollectionTest suite run printOn: Transcript

TrueTest testSelectors do: [ :each | Transcript show: each; cr. TrueTest run: each ]
TrueTest suite run printOn: Transcript

WriteStreamTest testSelectors do: [ :each | Transcript show: each; cr. WriteStreamTest run: each ]
WriteStreamTest suite run printOn: Transcript

"Emacs"
(setq stsc3-interpreter (list "stsc3-st"))

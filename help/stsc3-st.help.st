ArrayTest selectorsDo: [ :each | Transcript show: each; cr. ArrayTest run: each ]
ArrayTest suite run printOn: Transcript

CollectionTest selectorsDo: [ :each | Transcript show: each; cr. CollectionTest run: each ]
CollectionTest suite run printOn: Transcript

FalseTest selectorsDo: [ :each | Transcript show: each; cr. FalseTest run: each ]
FalseTest suite run printOn: Transcript

IntervalTest selectorsDo: [ :each | Transcript show: each; cr. IntervalTest run: each ]
IntervalTest suite run printOn: Transcript

OrderedCollectionTest selectorsDo: [ :each | Transcript show: each; cr. OrderedCollectionTest run: each ]
OrderedCollectionTest suite run printOn: Transcript

SequenceableCollectionTest selectorsDo: [ :each | Transcript show: each; cr. SequenceableCollectionTest run: each ]
SequenceableCollectionTest suite run printOn: Transcript

SortedCollectionTest selectorsDo: [ :each | Transcript show: each; cr. SortedCollectionTest run: each ]
SortedCollectionTest suite run printOn: Transcript

TrueTest selectorsDo: [ :each | Transcript show: each; cr. TrueTest run: each ]
TrueTest suite run printOn: Transcript

"Emacs"
(setq stsc3-interpreter (list "stsc3-st"))

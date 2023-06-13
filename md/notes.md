# Remainder

Som departs from Smalltalk syntax in two important regards, escape characters in strings and primitive notation.

In Smalltalk the single quote character is escaped by itself, so _''''_ is a string consisting of a single quote character.

In Som this is written _'\'''_, which in Smalltalk is an unterminated string.

This is handled in a somewhat fragile way, see rewriteSomQuotingToSmalltalk and somEscapedString.

In St-80 primitives are written as _<primitive: integerCode>_ at the beggining of a method.
In Som they are written as _primitive_ in place of a method.

Som interpreters, and hence I guess _stsc3-som_, parse _-cp x:y:z_ to set the class path.

# ifTrue:

Some methods may be short-circuited at some types, however they should be allowed at other types.

```
T = ( ifTrue: x = ( ^2 ) )
```

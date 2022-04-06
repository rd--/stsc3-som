# Remainder

Som departs from Smalltalk syntax in one important regard, escape characters in strings.

In Smalltalk the single quote character is escaped by itself, so _''''_ is a string consisting of a single quote character.

In Som this is written _'\'''_, which in Smalltalk is an unterminated string.

This is handled in a somewhat fragile way, see rewriteSomQuotingToSmalltalk and somEscapedString.

Som interpreters, and hence I guess _stsc3-som_, parse _-cp x:y:z_ to set the class path.

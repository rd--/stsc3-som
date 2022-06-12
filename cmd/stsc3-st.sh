#!/bin/sh

libdir=$HOME/sw/stsc3-som/lib/
stcdir=$HOME/sw/stsc3/som/
cp=$libdir:$stcdir
stsc3-som -cp $cp st repl

#!/bin/sh

libdir=$HOME/sw/stsc3-som/lib/
oscdir=$HOME/sw/stsc3/som/Osc
sc3dir=$HOME/sw/stsc3/som/Sc3
cp=$libdir:$oscdir:$sc3dir
stsc3-som -cp $cp st repl

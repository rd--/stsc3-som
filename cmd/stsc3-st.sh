#!/bin/sh

lib=$HOME/sw/stsc3-som/lib
stsc3=$HOME/sw/stsc3/som/
osc=$stsc3/Osc
sc3=$stsc3/Sc3
cp=$lib:$osc:$sc3
stsc3-som -cp $cp st repl

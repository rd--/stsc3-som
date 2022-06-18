#!/bin/sh

lib=$HOME/sw/stsc3-som/lib/
stsc3=$HOME/sw/stsc3/som/
osc=$stsc3/Osc-Kernel
sc3=$stsc3/Sc3-Kernel:$stsc3/Sc3-Ugen:$stsc3/Sc3-Pseudo:$stsc3/Sc3-Help
cp=$lib:$osc:$sc3
stsc3-som -cp $cp st repl

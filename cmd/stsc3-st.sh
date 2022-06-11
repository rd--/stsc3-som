#!/bin/sh

dir=/home/rohan/sw/stsc3-som/lib/
cp=$dir/Smalltalk/:$dir/SUnit/:$dir/Tests/
stsc3-som -cp $cp st repl

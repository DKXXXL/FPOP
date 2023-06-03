#!/bin/bash
set -x #echo on

time coqc showcase_test/Analysis_showcase.v -R _build/default/theories Fampoly -I _build/default/src &> output1.txt
time coqc showcase_test/Analysis_showcase2.v -R _build/default/theories Fampoly -I _build/default/src &>output2.txt 
time coqc showcase_test/Grammar_test6.v -R _build/default/theories Fampoly -I _build/default/src &> output3.txt
time coqc showcase_test/mixin2.v -R _build/default/theories Fampoly -I _build/default/src &> output4.txt 
time coqc showcase_test/STLC_families.v -R _build/default/theories Fampoly -I _build/default/src &> output5.txt 
time coqc showcase_test/test34.v -R _build/default/theories Fampoly -I _build/default/src &> output6.txt
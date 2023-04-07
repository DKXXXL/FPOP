#!/bin/bash
# make sure things are maked
# use this like ./make_test.sh [test_path]
if [ "$#" -eq  "1" ]; then
  "coqc"   -q   "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" -I _build/default/src  -R _build/default/theories Fampoly $1
else
  echo "Please Pass Exactly One Argument for the path to the test"
  exit 1
fi
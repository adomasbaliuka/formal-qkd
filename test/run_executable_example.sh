#!/usr/bin/env bash

printf "8875913 1124087 165048 20902 185856 26055 3456 484\n1776924" | .lake/build/bin/formalqkd > output.txt

if cat output.txt | grep -q 'SKL = 1464719'; then
    echo "Expected result."
else
    echo "Unexpected result"
    exit -1
fi

#!/bin/sh
set +x
echo coq_makefile -R . StructPoly -install none FSetList.v Lib*.v Metatheory*.v ML_SP*.v -o Makefile

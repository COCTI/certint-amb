#!/bin/sh
set -e
wait="$1"
args="-R . StructPoly"
makeit() {
 for i in "$@"; do
   if test "$wait" = "$i"; then wait=""; fi
   if test -z "$wait"; then echo coqc $args "$i.v" ; coqc $args "$i.v" ; fi
 done; }
makeit FSetList Lib_Tactic Lib_MyFSetInterface Lib_FinSet Lib_ListFacts
makeit Lib_FinSetImpl Lib_ListFactsMore
makeit Metatheory_Var Metatheory_Fresh Metatheory_Env
makeit Metatheory_SP Metatheory
makeit ML_SP_Definitions ML_SP_Infrastructure
makeit ML_SP_Soundness

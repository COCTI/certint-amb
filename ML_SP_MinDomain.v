(***************************************************************************
* Preservation and Progress for mini-ML with structural polymorphism       *
* Jacques Garrigue, May 2008                                               *
***************************************************************************)

Set Implicit Arguments.
Require Import Lib_FinSet Lib_FinSetImpl Metatheory List ListSet Arith.
Require Import ML_SP_Definitions ML_SP_Soundness.
Require Import Omega.

Module Cstr <: CstrIntf.
  Definition attr := nat.
  Definition eq_dec := eq_nat_dec.
  Inductive cstr_impl := Arrow.
  Definition cstr := cstr_impl.
  Definition arrow := Arrow.
  Definition valid (c : cstr) := True.
  Definition unique_dom := 0.
  Definition unique_cod := 1.
  Definition unique (a : attr) := true.
End Cstr.

(* Subject Reduction *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions Uniqueness.

Theorem subj_red :
  forall {Σ Γ t u T},
    fst Σ |-i t ▷ u ->
    Σ ;;; Γ |-i t : T ->
    Σ ;;; Γ |-i u : T.
Proof.
  intros Σ Γ t u T hr ht. revert Γ T ht.
  (* induction hr. *)
Abort.

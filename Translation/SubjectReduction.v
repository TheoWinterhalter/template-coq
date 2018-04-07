(* Subject Reduction *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata Uniqueness.

Theorem subj_red :
  forall {Σ Γ t u T},
    type_glob Σ ->
    fst Σ |-i t ▷ u ->
    Σ ;;; Γ |-i t : T ->
    Σ ;;; Γ |-i u : T.
Proof.
  intros Σ Γ t u T hg hr ht. revert Γ T ht.
  induction hr.
  - intros Γ T ht. dependent destruction ht.
    + ttinv ht3. destruct (prod_inv h1).
      eapply typing_subst.
      * assumption.
      * eapply type_conv ; try eassumption.
        admit.
      * eapply type_conv ; try eassumption.
        eapply conv_sym. assumption.


Abort.

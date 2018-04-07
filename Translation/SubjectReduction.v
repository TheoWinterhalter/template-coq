(* Subject Reduction *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata Uniqueness.

Inductive ctxconv Σ : scontext -> scontext -> Type :=
| ctxconv_nil : ctxconv Σ [] []
| ctxconv_cons Γ Δ A B:
    ctxconv Σ Γ Δ ->
    Σ |-i A = B ->
    ctxconv Σ (Γ,, A) (Δ,, B).

Fact ctxconv_refl :
  forall {Σ Γ}, ctxconv Σ Γ Γ.
Proof.
  intros Σ Γ. induction Γ.
  - constructor.
  - constructor.
    + assumption.
    + apply conv_refl.
Defined.

Lemma type_ctxconv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-i t : A ->
    ctxconv Σ Γ Δ ->
    Σ ;;; Δ |-i t : A.
Proof.
  intros Σ Γ Δ t A ht hc. revert Δ hc.
  induction ht ; intros Δ hc.
  - admit.
  - admit.
  - eapply type_Prod.
    + eapply IHht1. assumption.
    + eapply IHht2. econstructor.
      * assumption.
      * apply conv_refl.
  - eapply type_Lambda.
    + eapply IHht1. assumption.
    + eapply IHht2. econstructor ; try assumption.
      apply conv_refl.
    + eapply IHht3. econstructor ; try assumption.
      apply conv_refl.
  - eapply type_App.
    + eapply IHht1. assumption.
    + eapply IHht2. econstructor ; try assumption.
      apply conv_refl.
    + eapply IHht3. assumption.
    + eapply IHht4. assumption.
  - (* Seems we can automate it. *)
Admitted.

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
      eapply typing_subst ; try eassumption.
      eapply type_conv ; try eassumption.
      eapply type_ctxconv ; try eassumption.
      econstructor ; try eassumption.
      apply ctxconv_refl.
    + ttinv ht1. ttinv h3. destruct (prod_inv h6).
Admitted.

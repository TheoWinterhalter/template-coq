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

Derive Signature for ctxconv.

Fact ctxconv_refl :
  forall {Σ Γ}, ctxconv Σ Γ Γ.
Proof.
  intros Σ Γ. induction Γ.
  - constructor.
  - constructor.
    + assumption.
    + apply conv_refl.
Defined.

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := apply cheating.

(* ALTERNATIVE *)
(* Section ctxconv. *)

(*   Ltac tih type_ctxconv := *)
(*     match goal with *)
(*     | |- _ ;;; _ |-i _ : _ => *)
(*       eapply type_ctxconv ; eassumption *)
(*     | |- _ ;;; ?Δ,, ?A |-i _ : _ => *)
(*       eapply type_ctxconv ; [ *)
(*         eassumption *)
(*       | econstructor ; [ assumption | tih type_ctxconv ] *)
(*       | econstructor ; [ assumption | apply conv_refl ] *)
(*       ] *)
(*     | |- _ ;;; (?Δ,, ?A),, ?B |-i _ : _ => *)
(*       eapply type_ctxconv ; [ *)
(*         eassumption *)
(*       | econstructor ; [ *)
(*           econstructor ; [ assumption | apply conv_refl ] *)
(*         | apply conv_refl *)
(*         ] *)
(*       ] *)
(*     end. *)

(*   Ltac ih := *)
(*     match goal with *)
(*     | type_ctxconv : *)
(*         forall (Σ : sglobal_context) (Γ Δ : scontext) (t A : sterm), *)
(*           Σ;;; Γ |-i t : A -> wf Σ Δ -> ctxconv Σ Γ Δ -> Σ;;; Δ |-i t : A *)
(*       |- _ => tih type_ctxconv *)
(*     end. *)

(* Fixpoint type_ctxconv {Σ Γ Δ t A} (ht : Σ ;;; Γ |-i t : A) {struct ht} : *)
(*   wf Σ Δ -> *)
(*   ctxconv Σ Γ Δ -> *)
(*   Σ ;;; Δ |-i t : A. *)
(* Proof. *)
(*   intros hw hc. destruct ht. *)
(*   all: try (econstructor ; ih). *)
(*   - cheat. *)
(*   - econstructor. assumption. *)

Section ctxconv.

  Ltac tih type_ctxconv :=
    match goal with
    | |- _ ;;; _ |-i _ : _ =>
      eapply type_ctxconv ; eassumption
    | |- _ ;;; ?Δ,, ?A |-i _ : _ =>
      eapply type_ctxconv ; [
        eassumption
      | econstructor ; [ assumption | apply conv_refl ]
      ]
    | |- _ ;;; (?Δ,, ?A),, ?B |-i _ : _ =>
      eapply type_ctxconv ; [
        eassumption
      | econstructor ; [
          econstructor ; [ assumption | apply conv_refl ]
        | apply conv_refl
        ]
      ]
    end.

  Ltac ih :=
    match goal with
    | type_ctxconv :
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A : sterm),
          Σ;;; Γ |-i t : A -> ctxconv Σ Γ Δ -> Σ;;; Δ |-i t : A
      |- _ => tih type_ctxconv
    end.

Fixpoint type_ctxconv {Σ Γ Δ t A} (ht : Σ ;;; Γ |-i t : A) {struct ht} :
  ctxconv Σ Γ Δ ->
  Σ ;;; Δ |-i t : A

with wf_ctxconv {Σ Γ Δ} (ht : wf Σ Γ) {struct ht} :
  ctxconv Σ Γ Δ ->
  wf Σ Δ
.
Proof.
  - { intro hc. destruct ht.
      all: try (econstructor ; ih).
      - cheat.
      - econstructor. eapply wf_ctxconv ; eassumption.
      - eapply type_HeqTrans with (B := B) ; ih.
      - eapply type_ProjT2 with (A1 := A1) ; ih.
      - econstructor.
        + eapply wf_ctxconv ; eassumption.
        + eassumption.
      - econstructor. eapply wf_ctxconv ; eassumption.
      - econstructor.
        + ih.
        + ih.
        + assumption.
    }

  - { intro hc. destruct ht.
      - dependent destruction hc. constructor.
      - dependent destruction hc. econstructor.
        + eapply wf_ctxconv ; eassumption.
        + eapply type_ctxconv ; try eassumption.
          admit.
    }
Admitted.

End ctxconv.

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

Theorem subj_conv :
  forall {Σ Γ t u T U},
    type_glob Σ ->
    Σ |-i t = u ->
    Σ ;;; Γ |-i t : T ->
    Σ ;;; Γ |-i u : U ->
    Σ |-i T = U.
Proof.
  intros Σ Γ t u T U hg hr ht hu. revert Γ T U ht hu.
  induction hr ; intros Γ T U ht hu.
  - (* Need yet another result here about nl... *)
    admit.
  - eapply IHhr.
    + eapply subj_red ; eassumption.
    + assumption.
  - eapply IHhr.
    + eassumption.
    + eapply subj_red ; eassumption.
Admitted.

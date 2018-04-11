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

Section ctxconv.

  Ltac lift_sort :=
    match goal with
    | |- _ ;;; _ |-i lift ?n ?k ?t : ?S => change S with (lift n k S)
    | |- _ ;;; _ |-i ?t { ?n := ?u } : ?S => change S with (S {n := u})
    | |- _ |-i sSort ?s = lift ?n ?k ?t =>
      change (sSort s) with (lift n k (sSort s))
    | |- _ |-i sSort ?s = ?t{ ?n := ?u } =>
      change (sSort s) with ((sSort s){ n := u })
    | |- _ |-i lift ?n ?k ?t = sSort ?s =>
      change (sSort s) with (lift n k (sSort s))
    | |- _ |-i ?t{ ?n := ?u } = sSort ?s =>
      change (sSort s) with ((sSort s){ n := u })
    end.

  Ltac tih type_ctxconv :=
    lazymatch goal with
    | |- _ ;;; (?Δ,, ?A),, ?B |-i _ : _ =>
      eapply type_ctxconv ; [
        eassumption
      | assumption
      | econstructor ; [
          econstructor ; [ assumption | tih type_ctxconv ]
        | idtac
        ]
      | econstructor ; [
          econstructor ; [ assumption | apply conv_refl ]
        | apply conv_refl
        ]
      ]
    | |- _ ;;; ?Δ,, ?A |-i _ : _ =>
      eapply type_ctxconv ; [
        eassumption
      | assumption
      | econstructor ; [ assumption | tih type_ctxconv ]
      | econstructor ; [ assumption | apply conv_refl ]
      ]
    | |- _ ;;; _ |-i _ : _ =>
      eapply type_ctxconv ; eassumption
    | _ => fail "Not applicable tih"
    end.

  Ltac ih :=
    lazymatch goal with
    | type_ctxconv :
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A : sterm),
          Σ;;; Γ |-i t : A -> type_glob Σ -> wf Σ Δ -> ctxconv Σ Γ Δ -> Σ;;; Δ |-i t : A
      |- _ => tih type_ctxconv
    | _ => fail "Cannot find type_ctxconv"
    end.

Fixpoint type_ctxconv {Σ Γ Δ t A} (ht : Σ ;;; Γ |-i t : A) {struct ht} :
  type_glob Σ ->
  wf Σ Δ ->
  ctxconv Σ Γ Δ ->
  Σ ;;; Δ |-i t : A.
Proof.
  intros hg hw hc. destruct ht.
  all: try (econstructor ; ih).
  - cheat.
  - econstructor. assumption.
  - econstructor.
    + eapply type_ctxconv.
      * lift_sort. eapply typing_lift01 ; try eassumption.
      * assumption.
      * econstructor.
        -- assumption.
        -- ih.
      * econstructor.
        -- assumption.
        -- apply conv_refl.
    + eapply type_ctxconv.
      * eapply typing_lift01 ; try eassumption.
      * assumption.
      * econstructor.
        -- assumption.
        -- ih.
      * econstructor.
        -- assumption.
        -- apply conv_refl.
    + refine (type_Rel _ _ _ _ _).
      * econstructor ; try assumption. ih.
      * cbn. omega.
  - eapply type_HeqTrans with (B := B) ; ih.
  - econstructor ; try ih.
    eapply type_ctxconv.
    + eassumption.
    + assumption.
    + econstructor ; try assumption.
      econstructor ; ih.
    + econstructor ; try assumption.
      apply conv_refl.
  - econstructor ; try ih.
    + eapply type_ctxconv.
      * eassumption.
      * assumption.
      * econstructor ; try assumption.
        econstructor ; ih.
      * econstructor ; try assumption.
        apply conv_refl.
    + eapply type_ctxconv.
      * eassumption.
      * assumption.
      * econstructor ; try assumption.
        econstructor ; ih.
      * econstructor ; try assumption.
        apply conv_refl.
  - econstructor ; try ih.
    eapply type_ctxconv.
    + eassumption.
    + assumption.
    + econstructor ; try assumption.
      econstructor ; ih.
    + econstructor ; try assumption.
      apply conv_refl.
  - eapply type_ProjT2 with (A1 := A1) ; ih.
  - econstructor.
    + assumption.
    + eassumption.
  - econstructor. assumption.
  - econstructor.
    + ih.
    + ih.
    + assumption.
Defined.

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

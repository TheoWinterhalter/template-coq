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
    + lift_sort. eapply typing_lift01 ; try eassumption ; ih.
    + eapply typing_lift01 ; try eassumption ; ih.
    + refine (type_Rel _ _ _ _ _) ; [| cbn ; omega ].
      econstructor ; try eassumption. ih.
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

Section subjred.

  Ltac sr' hg hr IHhr :=
    intros Γ ? ht ;
    ttinv ht ; destruct (istype_type hg ht) ;
    specialize (IHhr _ _ ltac:(eassumption)) ;
    pose proof (conv_red_l _ _ _ _ hr (conv_refl _ _)) as heq ;
    (eapply type_conv ; try eassumption) ;
    eapply type_conv ; [
      (econstructor ; try eassumption) ;
      econstructor ; eassumption
    | econstructor ; eassumption
    | try conv rewrite heq ; apply conv_refl
    ].

  Ltac sr :=
    lazymatch goal with
    | [ hg : type_glob ?Σ,
        hr : _ |-i _ ▷ _,
        ih : forall _ _, _ ;;; _ |-i _ : _ -> _ ;;; _ |-i _ : _
      |- _ ] => sr' hg hr ih
    | _ => fail "Failed to collect assumptions"
    end.

  Theorem subj_red :
    forall {Σ Γ t u T},
      type_glob Σ ->
      fst Σ |-i t ▷ u ->
      Σ ;;; Γ |-i t : T ->
      Σ ;;; Γ |-i u : T.
  Proof.
    intros Σ Γ t u T hg hr ht. revert Γ T ht.
    induction hr.
    all: try sr.
    - intros Γ T ht.
      destruct (istype_type hg ht).
      ttinv ht. ttinv h3.
      destruct (prod_inv h6).
      eapply type_conv ; try eassumption.
      eapply typing_subst ; try eassumption.
      eapply type_conv ; try eassumption.
      eapply type_ctxconv ; try eassumption.
      + econstructor ; try eassumption.
        eapply typing_wf. eassumption.
      + constructor ; try assumption.
        apply ctxconv_refl.
    - intros Γ T ht.
      destruct (istype_type hg ht).
      ttinv ht. ttinv h3.
      destruct (eq_conv_inv h8) as [[? ?] ?].
      eapply type_conv ; try eassumption.
      eapply conv_trans ; try eassumption.
      apply cong_subst.
      + apply conv_sym.
        apply cong_Refl ; assumption.
      + apply substs_conv. eapply conv_trans ; try eassumption.
        apply conv_sym. assumption.
    - intros Γ T' ht.
      destruct (istype_type hg ht).
      ttinv ht. ttinv h.
      destruct (eq_conv_inv h6) as [[? ?] ?].
      eapply type_conv ; try eassumption.
      eapply conv_trans.
      + eapply conv_sym. eassumption.
      + eapply conv_trans ; [| eassumption ]. assumption.
    - intros Γ T ht.
      ttinv ht. destruct (istype_type hg ht).
      specialize (IHhr _ _ ltac:(eassumption)).
      pose proof (conv_red_l _ _ _ _ hr (conv_refl _ _)).
      eapply type_conv ; try eassumption.
      eapply type_conv.
      + econstructor ; try eassumption.
        * eapply type_ctxconv ; try eassumption.
          -- econstructor ; try eassumption.
             eapply typing_wf. eassumption.
          -- constructor ; try assumption.
             apply ctxconv_refl.
        * eapply type_ctxconv ; try eassumption.
          -- econstructor ; try eassumption.
             eapply typing_wf. eassumption.
          -- constructor ; try assumption.
             apply ctxconv_refl.
      + econstructor ; eassumption.
      + eapply cong_Prod ;
          try (apply conv_refl) ;
          try assumption ;
          try (apply conv_sym ; assumption).
    - (* intros Γ ? ht. *)
      (* ttinv ht. destruct (istype_type hg ht). *)
      (* specialize (IHhr _ _ ltac:(eassumption)). *)
      (* pose proof (conv_red_l _ _ _ _ hr (conv_refl _ _)) as heq. *)
      (* eapply type_conv ; try eassumption. *)
      (* eapply type_conv. *)
      (* + econstructor ; try eassumption. *)
      (*   econstructor ; eassumption. *)
      (* + econstructor ; eassumption. *)
      (* + try conv rewrite heq. apply conv_refl. *)
  Admitted.

End subjred.

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

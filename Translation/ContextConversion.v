(* Context Conversion  *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata.

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
Qed.

Fact ctxconv_length :
  forall {Σ Γ Δ},
    ctxconv Σ Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  intros Σ Γ Δ h. induction h.
  - reflexivity.
  - cbn. f_equal. assumption.
Qed.

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := apply cheating.

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

Section ctxconv.

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

  Fact safe_nth_conv :
    forall {Σ Γ Δ},
      ctxconv Σ Γ Δ ->
      forall n is1 is2,
        Σ |-i safe_nth Γ (exist _ n is1) = safe_nth Δ (exist _ n is2).
  Proof.
    intros Σ Γ Δ h. induction h ; intros n is1 is2.
    - cbn. bang.
    - destruct n.
      + cbn. assumption.
      + cbn. apply IHh.
  Qed.

  Fixpoint type_ctxconv {Σ Γ Δ t A} (ht : Σ ;;; Γ |-i t : A) {struct ht} :
    type_glob Σ ->
    wf Σ Δ ->
    ctxconv Σ Γ Δ ->
    Σ ;;; Δ |-i t : A.
  Proof.
    intros hg hw hc. destruct ht.
    all: try (econstructor ; ih).
    - eapply type_conv.
      + econstructor. assumption.
      + (* I have no idea how to deal with this.
           Basically I need to be able to convert context for the types in the
           context.
           Maybe if I add an extra assumption stating this.
         *)
        cheat.
      + apply lift_conv. apply conv_sym. apply safe_nth_conv. assumption.
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

        Unshelve. exact 0. rewrite <- ctxconv_length by eassumption. assumption.
  Qed.

End ctxconv.
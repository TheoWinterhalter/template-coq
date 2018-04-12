(* Subject Reduction *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions ITypingLemmata ContextConversion Uniqueness.

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
    | first [
        econstructor ; eassumption
      | try lift_sort ; eapply typing_subst ; eassumption
      ]
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
    - intros Γ ? ht.
      ttinv ht.
    - intros Γ ? ht.
      ttinv ht.
    - intros Γ ? ht.
      ttinv ht.
    - (* Like the case above, context conversion is involved.
         We'll deal with that later, once we're done with the rest.
       *)
      admit.
    - intros Γ ? ht.
      ttinv ht. destruct (istype_type hg ht).
      specialize (IHhr _ _ ltac:(eassumption)).
      pose proof (conv_red_l _ _ _ _ hr (conv_refl _ _)) as heq.
      eapply type_conv ; try eassumption.
      eapply type_conv.
      + econstructor ; try eassumption ;
        econstructor ; try eassumption.
        * econstructor ; eassumption.
        * conv rewrite heq. apply conv_refl.
      + first [
          econstructor ; eassumption
        | try lift_sort ; eapply typing_subst ; eassumption
        ].
      + eapply subst_conv. apply conv_sym. assumption.
    -
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

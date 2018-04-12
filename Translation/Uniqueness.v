(* Uniqueness of Typing *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SLiftSubst Equality SCommon Conversion ITyping
               ITypingInversions.

Ltac unitac h1 h2 :=
  ttinv h1 ; ttinv h2 ;
  eapply conv_trans ; [
    eapply conv_sym ; eassumption
  | idtac
  ].

Lemma uniqueness :
  forall {Σ Γ A B u},
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u : B ->
    Σ |-i A = B.
Proof.
  intros Σ Γ A B u h1 h2.
  revert Γ A B h1 h2.
  induction u ; intros Γ A B h1 h2.
  all: try unitac h1 h2. all: try assumption.
  - cbn in *. erewrite @safe_nth_irr with (isdecl' := is) in h0. assumption.
  - specialize (IHu1 _ _ _ h h0).
    specialize (IHu2 _ _ _ h4 h7).
    eapply conv_trans ; try eapply h6.
    pose proof (sort_conv_inv IHu1) as e1.
    pose proof (sort_conv_inv IHu2) as e2.
    subst. apply conv_refl.
  - eapply nl_conv ; try eassumption ; reflexivity.
  - specialize (IHu1 _ _ _ h0 h6).
    pose proof (sort_conv_inv IHu1) as e. subst. assumption.
  - specialize (IHu1 _ _ _ h h0).
    pose proof (sort_conv_inv IHu1) as e. subst. assumption.
  - specialize (IHu _ _ _ h h0).
    pose proof (heq_conv_inv IHu) as e. split_hyps.
    eapply conv_trans ; try exact h8.
    apply cong_Eq ; assumption.
  - specialize (IHu _ _ _ h4 h10).
    pose proof (heq_conv_inv IHu) as e. split_hyps.
    eapply conv_trans ; [ | exact h9 ].
    apply cong_Heq ; assumption.
  - specialize (IHu1 _ _ _ h5 h14).
    specialize (IHu2 _ _ _ h4 h13).
    pose proof (heq_conv_inv IHu1) as e1.
    pose proof (heq_conv_inv IHu2) as e2. split_hyps.
    eapply conv_trans ; [ | exact h12 ].
    apply cong_Heq ; assumption.
  - specialize (IHu1 _ _ _ h4 h9).
    specialize (IHu2 _ _ _ h5 h10).
    pose proof (eq_conv_inv IHu1) as e1. split_hyps.
    eapply conv_trans ; [| exact h8 ].
    apply cong_Heq ; try assumption.
    + apply conv_refl.
    + apply cong_Transport ; try assumption.
      all: apply conv_refl.
  - specialize (IHu3 _ _ _ h h0).
    pose proof (heq_conv_inv IHu3) as e3. split_hyps.
    pose proof (sort_conv_inv pi1_). subst.
    eapply conv_trans ; [| exact h10 ].
    apply cong_Heq.
    + (* apply conv_refl. *) admit.
    + apply cong_Prod ; try assumption.
      apply conv_refl.
    + (* apply conv_refl. *) admit.
    + apply cong_Prod ; try assumption. apply conv_refl.
  - specialize (IHu5 _ _ _ h0 h12).
    pose proof (heq_conv_inv IHu5) as e5. split_hyps.
    pose proof (sort_conv_inv pi1_). subst.
    eapply conv_trans ; [| exact h13 ].
    apply cong_Heq ; try assumption.
    + apply cong_Prod ; try assumption. apply conv_refl.
    + apply cong_Lambda ; try assumption. all: apply conv_refl.
    + apply cong_Prod ; try assumption. apply conv_refl.
    + apply cong_Lambda ; try assumption. all: apply conv_refl.
  - specialize (IHu3 _ _ _ h13 h26).
    specialize (IHu4 _ _ _ h h0).
    specialize (IHu6 _ _ _ h12 h25).
    pose proof (heq_conv_inv IHu3).
    pose proof (heq_conv_inv IHu4).
    pose proof (heq_conv_inv IHu6).
    split_hyps.
    eapply conv_trans ; [| exact h16 ].
    apply cong_Heq ; try assumption.
    + apply substs_conv. assumption.
    + apply cong_App ; try assumption. apply conv_refl.
    + apply substs_conv. assumption.
    + apply cong_App ; try assumption. apply conv_refl.
  - specialize (IHu1 _ _ _ h0 h12).
    specialize (IHu2 _ _ _ h11 h21).
    specialize (IHu3 _ _ _ h10 h20).
    pose proof (heq_conv_inv IHu1).
    pose proof (heq_conv_inv IHu2).
    pose proof (heq_conv_inv IHu3).
    split_hyps. subst.
    eapply conv_trans ; [| exact h13 ].
    apply cong_Heq ; try assumption.
    + apply cong_Eq ; assumption.
    + apply cong_Eq ; assumption.
  - specialize (IHu1 _ _ _ h h0).
    specialize (IHu2 _ _ _ h8 h15).
    pose proof (heq_conv_inv IHu1).
    pose proof (heq_conv_inv IHu2).
    split_hyps.
    pose proof (sort_conv_inv pi1_0). subst.
    eapply conv_trans ; [| exact h10 ].
    apply cong_Heq.
    + apply cong_Eq ; assumption.
    + apply cong_Refl ; assumption.
    + apply cong_Eq ; assumption.
    + apply cong_Refl ; assumption.
  - specialize (IHu _ _ _ h h0).
    pose proof (eq_conv_inv IHu). split_hyps.
    eapply conv_trans ; [| exact h8 ].
    apply cong_Heq ; assumption.
  - specialize (IHu1 _ _ _ h7 h13).
    specialize (IHu3 _ _ _ h0 h8).
    apply conv_sym in IHu1. pose proof (sort_conv_inv IHu1). subst.
    pose proof (heq_conv_inv IHu3). split_hyps.
    eapply conv_trans ; [| exact h9 ].
    apply cong_Eq ; assumption.
  - specialize (IHu1 _ _ _ h h0).
    eapply conv_trans ; [| exact h6 ].
    assumption.
  - specialize (IHu _ _ _ h4 h8).
    pose proof (pack_conv_inv IHu).
    split_hyps.
    eapply conv_trans ; [| exact h7 ].
    assumption.
  - specialize (IHu _ _ _ h4 h8).
    pose proof (pack_conv_inv IHu).
    split_hyps.
    eapply conv_trans ; [| exact h7 ].
    assumption.
  - specialize (IHu _ _ _ h4 h8).
    pose proof (pack_conv_inv IHu).
    split_hyps.
    eapply conv_trans ; [| exact h7 ].
    apply cong_Heq ; try assumption ; apply conv_refl.
  - eapply conv_trans ; [| exact h0 ].
    destruct isdecl as [d1 [[hd1 ?] hn1]].
    destruct isdecl0 as [d2 [[hd2 ?] hn2]].
    unfold sdeclared_minductive in *.
    rewrite hd1 in hd2. inversion hd2. subst.
    rewrite hn1 in hn2. inversion hn2. subst.
    apply conv_refl.
  - eapply conv_trans ; [| exact h0 ].
    erewrite stype_of_constructor_eq. apply conv_refl.
  - pose proof (inversionCase h1). easy.
Admitted.
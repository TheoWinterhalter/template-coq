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

Section nltype.

Ltac resolve :=
  match goal with
  | ih : forall u, nl ?t = nl u -> _ ;;; _ |-i u : ?T |- _ ;;; _ |-i ?v : ?T =>
    eapply ih ; eassumption
  end.

Ltac eresolve :=
  match goal with
  | ih : forall u, nl ?t = nl u -> _ ;;; _ |-i u : _, e : nl ?t = nl ?v
    |- _ ;;; _ |-i ?v : _ =>
    eapply ih ; eassumption
  end.

Ltac resolve2 :=
  match goal with
  | ih : forall u, nl ?t = nl u -> _ ;;; ?Γ |-i u : _, e : nl ?t = nl ?v
    |- _ ;;; ?Γ |-i ?v : _ =>
    eapply ih ; eassumption
  | ih : forall u, nl ?t = nl u -> _ ;;; ?Γ,, ?A |-i u : _, e : nl ?t = nl ?v
    |- _ ;;; ?Γ,, ?B |-i ?v : _ =>
    eapply type_ctxconv ; [
      eapply ih ; eassumption
    | assumption
    | econstructor ; [
        eapply typing_wf ; eassumption
      | eresolve
      ]
    | constructor ; [
        apply ctxconv_refl
      | apply conv_eq ; assumption
      ]
    ]
  end.

Ltac disc uu e :=
  match goal with
  | h : _ |-i _ = _ |- _ => idtac
  | _ => destruct uu ; cbn in e ; try discriminate e ; inversion e ; clear e
  end.

Ltac go :=
  econstructor ; try resolve2 ; try eassumption.

Lemma nl_type :
  forall {Σ Γ t u T},
    type_glob Σ ->
    Σ ;;; Γ |-i t : T ->
    nl t = nl u ->
    Σ ;;; Γ |-i u : T.
Proof.
  intros Σ Γ t u T hg ht e. revert u e.
  induction ht ; intros uu e.
  all: disc uu e.
  all: try (econstructor ; eresolve).
  all: try (econstructor ; resolve2).
  - subst. econstructor. assumption.
  - subst. econstructor. assumption.
  - eapply type_conv.
    + econstructor ; try resolve2.
      eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
    + econstructor ; eassumption.
    + apply conv_eq. symmetry. cbn. f_equal ; assumption.
  - eapply type_conv.
    + econstructor ; try resolve2.
      * eapply type_conv.
        -- resolve2.
        -- econstructor ; resolve2.
        -- apply conv_eq. cbn. f_equal ; assumption.
      * eapply type_conv.
        -- resolve2.
        -- resolve2.
        -- apply conv_eq. assumption.
    + lift_sort. eapply typing_subst ; eassumption.
    + apply cong_subst.
      * apply conv_eq. symmetry. assumption.
      * apply conv_eq. symmetry. assumption.
  - econstructor ; try resolve2.
    + eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
    + eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
  - eapply type_conv.
    + econstructor ; try resolve2.
      eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
    + econstructor ; eassumption.
    + apply conv_eq. symmetry. cbn. f_equal ; assumption.
  - eapply type_conv.
    + econstructor ; try resolve2.
      eapply type_conv.
      * resolve2.
      * resolve2.
      * apply conv_eq. assumption.
      * eapply type_conv.
        -- resolve2.
        -- resolve2.
        -- apply conv_eq. assumption.
      * eapply type_ctxconv ; try eassumption.
        -- eapply IHht4. assumption.
        -- econstructor.
           ++ econstructor.
              ** eapply typing_wf. eassumption.
              ** resolve2.
           ++ econstructor.
              ** lift_sort. eapply typing_lift01 ; try eassumption ; resolve2.
              ** eapply typing_lift01 ; try eassumption ; try resolve2.
                 eapply type_conv ; try resolve2.
                 apply conv_eq. assumption.
              ** eapply type_conv.
                 --- econstructor. econstructor ; try resolve2.
                     eapply typing_wf. eassumption.
                 --- lift_sort.
                     eapply typing_lift01 ; try eassumption ; resolve2.
                 --- apply lift_conv. cbn. apply conv_refl.
        -- repeat constructor.
           ++ apply ctxconv_refl.
           ++ assumption.
           ++ cbn. f_equal ; try assumption.
              all: apply nl_lift ; assumption.
      * eapply type_conv.
        -- resolve2.
        -- econstructor ; try resolve2.
           ++ eapply type_conv ; try resolve2.
              apply conv_eq. assumption.
           ++ eapply type_conv ; try resolve2.
              apply conv_eq. assumption.
        -- apply conv_eq. cbn. f_equal ; assumption.
      * eapply type_conv ; try resolve2.
        -- match goal with
           | |- _ ;;; _ |-i _ : ?S =>
             change S with (S{1 := uu2}{0 := sRefl uu1 uu2})
           end.
           eapply typing_subst2 ; try eassumption ; try resolve2.
           ++ eapply IHht4. assumption.
           ++ eapply type_conv ; try resolve2.
              ** econstructor ; try resolve2.
                 eapply type_conv ; try resolve2.
                 apply conv_eq. assumption.
              ** lift_sort.
                 eapply typing_subst ; try eassumption ; try resolve2.
                 econstructor.
                 --- lift_sort. eapply typing_lift01 ; eassumption.
                 --- eapply typing_lift01 ; eassumption.
                 --- refine (type_Rel _ _ _ _ _) ; try (cbn ; omega).
                     econstructor ; try eassumption.
                     eapply typing_wf. eassumption.
              ** cbn. rewrite !lift_subst, lift00.
                 apply conv_eq. cbn. symmetry. f_equal ; assumption.
        -- apply cong_subst.
           ++ apply conv_eq. cbn. f_equal ; assumption.
           ++ apply cong_subst.
              ** apply conv_eq. assumption.
              ** apply conv_eq. assumption.
    + match goal with
      | |- _ ;;; _ |-i _ : ?S =>
        change S with (S{1 := v}{0 := p})
      end.
      eapply typing_subst2 ; try eassumption.
      cbn. rewrite !lift_subst, lift00. assumption.
    + apply cong_subst.
      * apply conv_eq. symmetry. assumption.
      * apply cong_subst.
        -- apply conv_eq. symmetry. assumption.
        -- apply conv_eq. symmetry. assumption.
  - econstructor ; try resolve2.
    + econstructor ; try resolve2.
      * econstructor ; try resolve2.
        -- econstructor ; try resolve2.
           econstructor. eapply typing_wf. eassumption.
        -- apply conv_eq. cbn. f_equal ; assumption.
      * econstructor ; try resolve2.
        apply conv_eq. assumption.
    + eassumption.
    + apply conv_eq. symmetry. assumption.
  - econstructor ; try resolve2.
    + econstructor ; try resolve2.
      apply conv_eq. assumption.
    + econstructor ; try resolve2.
      apply conv_eq. assumption.
  - econstructor ; try resolve2 ; eassumption.
  - go.
    + go. go. apply conv_eq. assumption.
    + go.
    + apply conv_eq. cbn. symmetry. f_equal ; assumption.
  - go.
  - go.
  - go.
    + go.
    + go. go.
    + go. cbn. symmetry. f_equal ; try assumption.
      f_equal ; assumption.
  - go.
    + go. go.
      * go.
        -- go. econstructor.
           ++ eapply typing_wf. eassumption.
           ++ go.
        -- go. econstructor.
           ++ eapply typing_wf. eassumption.
           ++ go.
        -- lift_sort. eapply typing_subst ; try eassumption.
           ++ lift_sort.
              eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A1 ]) ;
                try eassumption.
              ** go.
                 --- go. eapply typing_wf. eassumption.
                 --- apply conv_refl.
              ** eapply typing_wf. eassumption.
           ++ cbn. eapply type_ProjT1 with (A2 := lift0 1 A2).
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** refine (type_Rel _ _ _ _ _) ; try (cbn ; omega).
                 eapply typing_wf. eassumption.
        -- lift_sort. eapply typing_subst ; try eassumption.
           ++ lift_sort.
              eapply @type_lift with (Δ := [ sPack A1 A2 ]) (Ξ := [ A2 ]) ;
                try eassumption.
              ** go.
                 --- go. eapply typing_wf. eassumption.
                 --- apply conv_refl.
              ** eapply typing_wf. eassumption.
           ++ cbn. eapply type_ProjT2 with (A1 := lift0 1 A1).
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** lift_sort. eapply typing_lift01 ; try eassumption.
                 go.
              ** refine (type_Rel _ _ _ _ _) ; try (cbn ; omega).
                 eapply typing_wf. eassumption.
      * go. cbn. f_equal.
        -- apply nl_subst.
           ++ apply nl_lift. assumption.
           ++ reflexivity.
        -- apply nl_subst.
           ++ apply nl_lift. assumption.
           ++ reflexivity.
    + go.
      * go. eapply typing_wf. eassumption.
      * go. eapply typing_wf. eassumption.
      * go.
      * go.
    + go. cbn. symmetry. f_equal ; f_equal ; assumption.
  - go.
    + go.
      * go.
        -- go.
           ++ go. eapply typing_wf. eassumption.
           ++ go. eapply typing_wf. eassumption.
           ++ lift_sort. admit.
           ++ lift_sort. admit.
        -- go. cbn. f_equal.
           ++ apply nl_subst.
              ** apply nl_lift. assumption.
              ** reflexivity.
           ++ apply nl_subst.
              ** apply nl_lift. assumption.
              ** reflexivity.
      * go.
        -- go.
           ++ admit.
           ++ admit.
           ++ admit.
           ++ admit.
        -- admit.
      * go. go.
      * go. go.
    + go.
      * go.
      * go.
      * go.
      * go.
    + go. cbn. symmetry. f_equal.
      * f_equal ; assumption.
      * f_equal ; assumption.
      * f_equal ; assumption.
      * f_equal ; assumption.
  - admit.
  - go.
  - go.
  - go.
  - admit.
  - go.
  - go.
  - go.
    + go.
    + go.
      * go.
      * eapply type_ProjT2 with (A1 := A1) ; eassumption.
    + go. symmetry. cbn. f_equal ; try assumption.
      * f_equal. assumption.
      * f_equal. assumption.
  - go. admit.
  - admit.
  - go.
  Unshelve. all: auto.
  cbn. omega.
Admitted.

End nltype.

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
  - eapply uniqueness ; try eassumption.
    eapply nl_type ; try eassumption.
    symmetry. assumption.
  - eapply IHhr.
    + eapply subj_red ; eassumption.
    + assumption.
  - eapply IHhr.
    + eassumption.
    + eapply subj_red ; eassumption.
Qed.

(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".
Require Import ssreflect ssrbool.
From Coq Require Import Bool List Utf8 ZArith Lia Morphisms String.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSize
  PCUICLiftSubst PCUICSigmaCalculus PCUICUnivSubst PCUICTyping PCUICReduction
  PCUICSubstitution PCUICReflect PCUICClosed PCUICParallelReduction
  PCUICPattern PCUICInduction.

Require Import monad_utils.
Import MonadNotation.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Equations app_construct_discr (t : term) : bool :=
  app_construct_discr (tConstruct _ _ _) := true ;
  app_construct_discr (tApp t _) := app_construct_discr t ;
  app_construct_discr _ := false.

Transparent app_construct_discr.

Equations discr_app_construct (t : term) : Prop := {
  | tConstruct _ _ _ => False ;
  | tApp t _ => discr_app_construct t ;
  | _ => True
}.
Transparent discr_app_construct.

Lemma discr_app_construct_mkApps :
  forall t l,
    discr_app_construct (mkApps t l) = discr_app_construct t.
Proof.
  intros t l.
  induction l in t |- *.
  - reflexivity.
  - cbn. rewrite IHl. reflexivity.
Qed.

Inductive app_construct_view : term -> Type :=
| is_app_construct c u i l : app_construct_view (mkApps (tConstruct c u i) l)
| app_construct_other t : discr_app_construct t -> app_construct_view t.

Equations? view_app_construct (t : term) : app_construct_view t := {
  | tConstruct ind u i => is_app_construct ind u i [] ;
  | tApp t u with view_app_construct t => {
    | is_app_construct c x i l => _ # is_app_construct c x i (l ++ [ u ]) ;
    | app_construct_other t h => app_construct_other _ _
    } ;
  | t => app_construct_other t I
}.
Proof.
  rewrite <- mkApps_nested. reflexivity.
Qed.

Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

Section list_size.
  Context {A : Type} (f : A → nat).

  Lemma In_list_size:
    forall x xs, In x xs -> f x < S (list_size f xs).
  Proof.
    intros x xs H. induction xs.
    1: destruct H.
    destruct H.
    - simpl. subst. lia.
    - specialize (IHxs H). simpl. lia.
  Qed.

End list_size.

Equations map_In {A B : Type} (l : list A) (f : ∀ (x : A), In x l → B) : list B :=
  map_In nil _ := nil;
  map_In (cons x xs) f := cons (f x _) (map_In xs (fun x H => f x _)).

Lemma map_In_spec {A B : Type} (f : A → B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = List.map f l.
Proof.
  remember (fun (x : A) (_ : In x l) => f x) as g.
  funelim (map_In l g). 1: reflexivity.
  simp map_In. rewrite H. trivial.
Qed.

#[program] Definition map_terms {A} {t} (f : forall x, size x < size t -> A)
  (l : list term)
  (h : list_size size l < size t) :=
  (map_In l (fun t (h : In t l) => f t _)).
Next Obligation.
  eapply (In_list_size size) in h. lia.
Qed.

Lemma size_mkApps f l : size (mkApps f l) = size f + list_size size l.
Proof.
  induction l in f |- *; simpl; try lia.
  rewrite IHl. simpl. lia.
Qed.

(* Equations? pattern_footprint (t : term) : term × list term
  by wf (size t) :=
  pattern_footprint t with view_app_construct t := {
  | is_app_construct ind u i l with inspect (map_terms pattern_footprint l _) := {
    | @exist ml e1 with inspect (
        fold_left
          (fun '(pl, al) '(p,a) => (pl ++ [ lift0 #|al| p ], al ++ a))
          ml
          ([], [])
      ) => {
      | @exist (pl, al) e2 => (mkApps (tConstruct ind u i) pl, al)
      }
    } ;
  | app_construct_other t h => (tRel 0, [ t ])
  }.
Proof.
  rewrite size_mkApps. cbn. auto.
Qed. *)

Equations? pattern_footprint (t : term) : term × list term
  by wf (size t) :=
  pattern_footprint t with view_app_construct t := {
  | is_app_construct ind u i l with inspect (map_terms pattern_footprint l _) := {
    | @exist ml e1 with inspect (
        fold_right
          (fun '(p,a) '(pl, al) => (lift0 #|al| p :: pl, al ++ a))
          ([], [])
          ml
      ) => {
      | @exist (pl, al) e2 => (mkApps (tConstruct ind u i) pl, al)
      }
    } ;
  | app_construct_other t h => (tRel 0, [ t ])
  }.
Proof.
  rewrite size_mkApps. cbn. auto.
Qed.

Lemma map_terms_map t A f l H :
  @map_terms A t (fun x Hx => f x) l H = map f l.
Proof.
  unfold map_terms. now rewrite map_In_spec.
Qed.

Lemma list_size_app (l l' : list term) : list_size size (l ++ l') = list_size size l + list_size size l'.
Proof.
  induction l; simpl; auto.
  rewrite IHl. lia.
Qed.

(* TODO MOVE *)
Lemma closedn_mkApps :
  forall n t l,
    closedn n (mkApps t l) = closedn n t && forallb (closedn n) l.
Proof.
  intros n t l.
  induction l in n, t |- *.
  - cbn. rewrite andb_true_r. reflexivity.
  - cbn. rewrite IHl. cbn. rewrite andb_assoc. reflexivity.
Qed.

Lemma pattern_footprint_closedn_eq :
  forall t,
    let '(p, τ) := pattern_footprint t in
    closedn #|τ| p ×
    t = subst0 τ p.
Proof.
  intros t.
  funelim (pattern_footprint t).
  - cbn. split.
    + reflexivity.
    + rewrite lift0_id. reflexivity.
  - clear H. rewrite map_terms_map in e0.
    rewrite closedn_mkApps. cbn.
    rewrite subst_mkApps. cbn.
    match goal with
    | |- ?h × mkApps _ ?l = mkApps _ ?l' =>
      cut (h × l = l')
    end.
    { intros [? ?]. intuition auto. f_equal. assumption. }
    induction l in l0, l1, e0, Hind |- *.
    + cbn in e0. inversion e0. intuition reflexivity.
    + cbn in e0.
      destruct pattern_footprint eqn:e1.
      destruct fold_right eqn:e2.
      inversion e0. subst. clear e0.
      cbn.
      specialize IHl with (2 := eq_refl).
      forward IHl.
      { intros x hx. eapply Hind. rewrite size_mkApps. cbn.
        rewrite size_mkApps in hx. cbn in hx. lia.
      }
      specialize (Hind a). forward Hind.
      { rewrite size_mkApps. cbn. lia. }
      rewrite e1 in Hind.
      destruct IHl as [hc ?].
      destruct Hind as [? ?].
      split.
      * {
        eapply andb_true_intro. split.
        - rewrite app_length. rewrite plus_comm. eapply closedn_lift. assumption.
        - eapply forallb_impl. 2: eauto.
          intros x ? h.
          rewrite app_length. eapply closed_upwards. 1: eauto.
          lia.
      }
      * subst. rewrite subst_app_decomp.
        rewrite simpl_subst_k.
        1:{ rewrite map_length. reflexivity. }
        f_equal.
        eapply All_map_eq. apply forallb_All in hc.
        eapply All_impl. 1: eauto.
        cbn. intros x hx.
        rewrite subst_app_simpl. cbn.
        eapply subst_closedn in hx. erewrite hx. reflexivity.
Qed.

Lemma pattern_lift :
  forall n m p,
    pattern n p ->
    pattern (m + n) (lift0 m p).
Proof.
  intros n m p hp.
  induction hp as [k hk | ind k ui args ha ih] in m |- * using pattern_all_rect.
  - cbn. constructor. lia.
  - rewrite lift_mkApps. cbn. constructor.
    apply All_map. eapply All_impl. 1: eauto.
    cbn. intros x hx. eapply hx.
Qed.

Lemma pattern_upwards :
  forall n m p,
    pattern n p ->
    m ≥ n ->
    pattern m p.
Proof.
  intros n m p hp h.
  induction hp as [k hk | ind k ui args ha ih]
  in m, h |- * using pattern_all_rect.
  - constructor. lia.
  - constructor.
    eapply All_impl. 1: eauto.
    cbn. intros x hx. eapply hx. assumption.
Qed.

Lemma pattern_footprint_pattern :
  forall t,
    let '(p, τ) := pattern_footprint t in
    pattern #|τ| p.
Proof.
  intros t.
  funelim (pattern_footprint t).
  - cbn. constructor. auto.
  - clear H. rewrite map_terms_map in e0.
    constructor.
    induction l in l0, l1, e0, Hind |- *.
    + cbn in e0. inversion e0. constructor.
    + cbn in e0.
      destruct pattern_footprint eqn:e1.
      destruct fold_right eqn:e2.
      inversion e0. subst. clear e0.
      specialize IHl with (2 := eq_refl).
      forward IHl.
      { intros x hx. eapply Hind. rewrite size_mkApps. cbn.
        rewrite size_mkApps in hx. cbn in hx. lia.
      }
      specialize (Hind a). forward Hind.
      { rewrite size_mkApps. cbn. lia. }
      rewrite e1 in Hind.
      constructor.
      * rewrite app_length. eapply pattern_lift. assumption.
      * eapply All_impl. 1: eauto.
        intros x hx. rewrite app_length.
        eapply pattern_upwards. 1: eauto.
        lia.
Qed.

Ltac eqb_dec :=
  match goal with
  | |- context [ eqb ?x ?y ] =>
    destruct (eqb_spec x y)
  | h : context [ eqb ?x ?y ] |- _ =>
    destruct (eqb_spec x y)
  end.

Tactic Notation "eqb_dec" "in" hyp(h) :=
  match type of h with
  | context [ eqb ?x ?y ] =>
    destruct (eqb_spec x y)
  end.

Lemma fold_right_rev_left :
  forall A B (f : A -> B -> B) l i,
    fold_right f i l = fold_left (fun x y => f y x) (List.rev l) i.
Proof.
  intros A B f l i.
  rewrite <- fold_left_rev_right. rewrite rev_involutive. reflexivity.
Qed.

Definition pattern_list_footprint l :=
  fold_right
    (λ '(p, a) '(pl, al), (lift0 #|al| p :: pl, al ++ a))
    ([], [])
    (map pattern_footprint l).

Lemma pattern_list_footprint_unfold :
  forall l,
    pattern_list_footprint l =
    fold_right
      (λ '(p, a) '(pl, al), (lift0 #|al| p :: pl, al ++ a))
      ([], [])
      (map pattern_footprint l).
Proof.
  reflexivity.
Defined.

Lemma pattern_list_footprint_atend :
  forall l a,
    let '(p, τ) := pattern_footprint a in
    let '(pl, al) := pattern_list_footprint l in
    pattern_list_footprint (l ++ [ a ]) =
    (map (lift0 #|τ|) pl ++ [ p ], τ ++ al).
Proof.
  intros l a.
  destruct pattern_footprint as [p τ] eqn:e1.
  destruct pattern_list_footprint as [pl al] eqn:e2.
  induction l in a, p, τ, e1, pl, al, e2 |- *.
  - cbn. rewrite e1. cbn. rewrite lift0_id.
    cbn in e2. inversion e2.
    cbn. rewrite app_nil_r. reflexivity.
  - cbn in e2. move e2 at top. destruct pattern_footprint eqn:e3.
    rewrite <- pattern_list_footprint_unfold in e2.
    destruct pattern_list_footprint eqn:e4.
    inversion e2. subst. clear e2.
    cbn. rewrite e3. rewrite <- pattern_list_footprint_unfold.
    specialize IHl with (1 := e1) (2 := eq_refl).
    rewrite IHl. rewrite app_length.
    rewrite <- simpl_lift with (i := 0). 2,3: lia.
    f_equal. rewrite app_assoc. reflexivity.
Qed.

(* A version easier to do rewriting *)
Lemma pattern_list_footprint_atend_eq :
  forall l a,
    pattern_list_footprint (l ++ [ a ]) =
    (map (lift0 #|(pattern_footprint a).2|) (pattern_list_footprint l).1 ++ [ (pattern_footprint a).1 ], (pattern_footprint a).2 ++ (pattern_list_footprint l).2).
Proof.
  intros l a.
  pose proof (pattern_list_footprint_atend l a) as h.
  destruct pattern_footprint eqn:e1.
  destruct pattern_list_footprint eqn:e2.
  cbn. assumption.
Qed.

Lemma pattern_footprint_match_pattern :
  forall npat t p σ,
    pattern npat p ->
    match_pattern npat p t = Some σ ->
    let '(q, τ) := pattern_footprint t in
    ∑ θ,
      match_pattern npat p q = Some θ ×
      map (option_map (subst0 τ)) θ = σ.
Proof.
  intros npat t p σ hp e.
  pose proof (pattern_footprint_closedn_eq t) as ef. revert ef.
  funelim (pattern_footprint t). all: intros [_ ef].
  - clear Heq.
    cbn. destruct hp.
    2:{
      eapply match_pattern_sound in e. 2: constructor ; auto.
      2: eapply subs_flatten_default_complete.
      subst. rewrite subst_mkApps in d. cbn in d.
      rewrite discr_app_construct_mkApps in d. cbn in d.
      contradiction.
    }
    cbn in e. cbn.
    unfold subs_init in *. unfold subs_add in *.
    destruct nth_error as [[]|] eqn:e1. 1,3: discriminate.
    apply some_inj in e. subst.
    eexists. intuition eauto.
    rewrite map_app. cbn. rewrite <- firstn_map. rewrite map_skipn.
    unfold subs_empty. rewrite map_list_init. cbn.
    rewrite lift0_id. reflexivity.
  - clear H Heq.
    rewrite map_terms_map in e0.
    rewrite <- pattern_list_footprint_unfold in e0.
    destruct hp as [n hn | ind n ui args ha].
    + cbn in e. cbn.
      unfold subs_init in *. unfold subs_add in *.
      destruct nth_error as [[]|] eqn:e1. 1,3: discriminate.
      apply some_inj in e. subst.
      eexists. intuition eauto.
      rewrite map_app. cbn. rewrite <- firstn_map. rewrite map_skipn.
      unfold subs_empty. rewrite map_list_init. cbn. f_equal. f_equal. f_equal.
      auto.
    + induction ha in l, l0, l1, Hind, σ, e, ef, e0 |- * using All_rev_rect.
      * cbn - [eqb] in e. cbn - [eqb]. unfold assert_eq in *.
        eqb_dec in e. 2: discriminate.
        cbn in e. apply some_inj in e. subst.
        destruct l using list_rect_rev.
        2:{ rewrite <- mkApps_nested in e1. discriminate. }
        cbn in e1. inversion e1. subst. clear e1.
        cbn in ef. rewrite subst_mkApps in ef. cbn in ef.
        destruct l0 using list_rect_rev.
        2:{
          rewrite map_app in ef. rewrite <- mkApps_nested in ef. discriminate.
        }
        clear ef. cbn - [eqb].
        eqb_dec. 2: contradiction.
        cbn.
        eexists. intuition eauto.
        unfold subs_empty. rewrite map_list_init. reflexivity.
      * rewrite <- mkApps_nested in e. cbn in e.
        destruct l using list_rect_rev. 1: discriminate.
        clear IHl.
        rewrite pattern_list_footprint_atend_eq in e0.
        destruct pattern_footprint eqn:e1.
        destruct pattern_list_footprint eqn:e2.
        cbn in e0. inversion e0. subst. clear e0.
        symmetry in e2.
        specialize IHha with (4 := e2).
        rewrite <- mkApps_nested. cbn.
        rewrite <- mkApps_nested in e. cbn in e.
        destruct match_pattern eqn:e3. 2: discriminate.
        move e at top.
        destruct match_pattern eqn:e4. 2: discriminate.
        rewrite <- 2!mkApps_nested in ef. cbn in ef.
        inversion ef. subst.
        rewrite <- mkApps_nested. cbn.
        forward IHha.
        { intros v hv. intros. subst.
          eapply Hind. all: eauto.
          rewrite size_mkApps. rewrite size_mkApps in hv.
          rewrite list_size_app. lia.
        }
        specialize IHha with (1 := eq_refl).
        forward IHha.
        { rewrite H0. rewrite subst_app_decomp. f_equal.
          rewrite subst_mkApps. cbn. f_equal.
          rewrite map_map_compose. eapply map_id_f.
          intros v. eapply simpl_subst_k. rewrite map_length. reflexivity.
        }
        destruct IHha as [θ [h1 h2]].
        (* Somehow the induction hypothesis isn't strong enough?
          Or is it just a question of match_pattern_lift?
        *)
        (* rewrite h1. *)
        specialize Hind with (3 := e4) (4 := eq_refl).
        forward Hind.
        { rewrite size_mkApps. rewrite list_size_app. cbn. lia. }
        forward Hind by auto.
        forward Hind.
        { apply pattern_footprint_closedn_eq. }
        rewrite e1 in Hind.
        destruct Hind as [θ' [h1' h2']].
        rewrite h1'.
Admitted.
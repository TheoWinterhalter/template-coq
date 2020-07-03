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

Lemma match_pattern_lift :
  forall npat p t k σ,
    pattern npat p ->
    match_pattern npat p t = Some σ ->
    match_pattern npat p (lift0 k t) = Some (map (option_map (lift0 k)) σ).
Proof.
  intros npat p t k σ hp e.
  induction hp
  as [n hn | ind n ui args ha ih]
  in t, σ, e, k |- *
  using pattern_all_rect.
  - cbn in *. unfold subs_init in *. unfold subs_add in *.
    destruct nth_error as [[]|] eqn:e1. 1,3: discriminate.
    apply some_inj in e. subst.
    rewrite map_app. cbn. rewrite <- firstn_map. rewrite map_skipn.
    unfold subs_empty. rewrite map_list_init. cbn.
    reflexivity.
  - eapply All_prod in ih. 2: exact ha.
    clear ha.
    induction ih
    as [| p args [hp ihp] _ ih]
    in t, σ, e, k |- *
    using All_rev_rect.
    + cbn - [eqb] in *. unfold assert_eq in *. eqb_dec in e. 2: discriminate.
      subst. cbn - [eqb] in *.
      eqb_dec. 2: contradiction.
      cbn. apply some_inj in e. subst.
      unfold subs_empty. rewrite map_list_init. reflexivity.
    + rewrite <- mkApps_nested. cbn.
      rewrite <- mkApps_nested in e. cbn in e.
      destruct t. all: try discriminate.
      destruct match_pattern eqn:e1. 2: discriminate.
      move e at top.
      destruct match_pattern eqn:e2. 2: discriminate.
      cbn.
      eapply ih in e1. eapply ihp in e2.
      erewrite e1. erewrite e2.
      eapply subs_merge_map. assumption.
Qed.

Lemma subs_merge_map_inv :
  forall σ θ ρ f,
    subs_merge (map (option_map f) σ) (map (option_map f) θ) = Some ρ ->
    ∑ ρ', subs_merge σ θ = Some ρ' × ρ = map (option_map f) ρ'.
Proof.
  intros σ θ ρ f e.
  induction σ as [| [] σ ih] in θ, ρ, f, e |- *.
  - destruct θ. 2: discriminate.
    cbn in e. apply some_inj in e. subst.
    cbn. eexists. intuition eauto.
  - destruct θ as [| [] θ]. 1,2: discriminate.
    cbn in e. destruct subs_merge eqn:e1. 2: discriminate.
    apply some_inj in e. subst.
    eapply ih in e1. destruct e1 as [ρ [e1 ?]]. subst.
    cbn. rewrite e1.
    intuition eauto.
  - destruct θ as [| x θ]. 1: discriminate.
    cbn in e. destruct subs_merge eqn:e1. 2: discriminate.
    apply some_inj in e. subst.
    eapply ih in e1. destruct e1 as [ρ [e1 ?]]. subst.
    cbn. rewrite e1.
    intuition eauto.
Qed.

Lemma match_pattern_closedn :
  forall npat p t σ k,
    pattern npat p ->
    closedn k t ->
    match_pattern npat p t = Some σ ->
    All (on_Some (closedn k)) σ.
Proof.
  intros npat p t σ k hp hc e.
  induction hp
  as [n hn | ind n ui args ha ih]
  in t, σ, e, k, hc |- *
  using pattern_all_rect.
  - cbn in e. unfold subs_init in e. unfold subs_add in e.
    destruct nth_error as [[]|] eqn:e1. 1,3: discriminate.
    apply some_inj in e. subst. apply All_app_inv.
    1:{ apply All_firstn. apply All_on_Some_subs_empty. }
    constructor.
    2:{ apply All_skipn. apply All_on_Some_subs_empty. }
    cbn. assumption.
  - eapply All_prod in ih. 2: exact ha.
    clear ha.
    induction ih
    as [| p args [hp ihp] _ ih]
    in t, σ, e, k, hc |- *
    using All_rev_rect.
    + cbn - [eqb] in e. unfold assert_eq in e. eqb_dec in e. 2: discriminate.
      subst. cbn in e. apply some_inj in e. subst.
      apply All_on_Some_subs_empty.
    + rewrite <- mkApps_nested in e. cbn in e.
      destruct t. all: try discriminate.
      destruct match_pattern eqn:e1. 2: discriminate.
      move e at top.
      destruct match_pattern eqn:e2. 2: discriminate.
      cbn in hc. apply andP in hc as [hc1 hc2].
      eapply ih in e1. 2: eauto.
      eapply ihp in e2. 2: eauto.
      eapply All_on_Some_subs_merge. all: eauto.
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
        eapply match_pattern_lift in h1.
        2:{ constructor. assumption. }
        erewrite lift_mkApps in h1. cbn in h1. erewrite h1.
        specialize Hind with (3 := e4) (4 := eq_refl).
        forward Hind.
        { rewrite size_mkApps. rewrite list_size_app. cbn. lia. }
        forward Hind by auto.
        forward Hind.
        { apply pattern_footprint_closedn_eq. }
        rewrite e1 in Hind.
        destruct Hind as [θ' [h1' h2']].
        rewrite h1'.
        subst.
        match goal with
        | e : subs_merge _ _ = ?z
          |- context [ subs_merge ?x ?y = _ × map  ?f _ = _ ] =>
          assert (h : subs_merge (map f x) (map f y) = z)
        end.
        { rewrite <- e. f_equal.
          - rewrite map_map_compose. eapply map_ext.
            intros o. rewrite option_map_two.
            eapply option_map_ext.
            intros v.
            rewrite subst_app_decomp. f_equal.
            eapply simpl_subst_k. rewrite map_length. reflexivity.
          - epose proof (pattern_footprint_closedn_eq _) as h.
            erewrite e1 in h. destruct h as [hc _].
            eapply match_pattern_closedn in h1'. 2,3: eauto.
            eapply All_map_eq. eapply All_impl. 1: eauto.
            intros [] h. 2: reflexivity.
            cbn in h. cbn. f_equal.
            rewrite subst_app_simpl. cbn.
            eapply subst_closedn in h. erewrite h. reflexivity.
        }
        eapply subs_merge_map_inv in h as [ρ [e5 ?]]. subst.
        rewrite e5. intuition eauto.
Qed.

Lemma map_subst_nil :
  forall l k,
    map (subst [] k) l = l.
Proof.
  intros l k. eapply map_id_f.
  intros t. apply subst_empty.
Qed.

Fixpoint elim_footprint t :=
  match t with
  | tSymb k n ui =>
      ret (k, n, ui, [], [])

  | tApp u v =>
    '(k,n,ui,l,τ) <- elim_footprint u ;;
    let '(p,σ) := pattern_footprint v in
    ret (k, n, ui, eApp (lift0 #|τ| p) :: l, τ ++ σ)

  | tCase ind p c brs =>
    '(k,n,ui,l,τ) <- elim_footprint c ;;
    let '(p', θ) := pattern_footprint p in
    let '(brs', σ) :=
      fold_right
        (λ '(n, (p, a)) '(pl, al),
          ((n, lift0 (#|τ| + #|θ| + #|al|) p) :: pl, al ++ a)
        )
        ([], [])
        (map (on_snd pattern_footprint) brs)
    in
    ret (k, n, ui, eCase ind (lift0 #|τ| p') brs' :: l, τ ++ θ ++ σ)

  | tProj p u =>
    '(k,n,ui,l,τ) <- elim_footprint u ;;
    ret (k, n, ui, eProj p :: l, τ)

  | _ => None
  end.

Definition on_elim (P : term -> Type) e : Type :=
  match e with
  | eApp p => P p
  | eCase ind p brs => P p × All (fun b => P b.2) brs
  | eProj p => True
  end.

Lemma on_elim_impl :
  forall P Q e,
    on_elim P e ->
    (forall x, P x -> Q x) ->
    on_elim Q e.
Proof.
  intros P Q e he h.
  destruct e.
  - cbn in *. eapply h. assumption.
  - cbn in *. destruct he. split.
    + eapply h. assumption.
    + eapply All_impl. 1: eauto.
      intros [? ?]. cbn. intros ?.
      eapply h. assumption.
  - cbn in *. constructor.
Qed.

Lemma left_apply :
  forall {A B C} (f : A -> B),
    A × C ->
    B × C.
Proof.
  intros A B C f [? ?]. intuition auto.
Qed.

Lemma right_apply :
  forall {A B C} (f : A -> B),
    C × A ->
    C × B.
Proof.
  intros A B C f [? ?]. intuition auto.
Qed.

Lemma unfold_map :
  forall {A B} (f : A -> B) l,
    map f l =
    (fix map (l : list A) : list B :=
      match l with
      | [] => []
      | a :: t => f a :: map t
      end) l.
Proof.
  reflexivity.
Qed.

Lemma closedn_mkElim :
  forall n t e,
    closedn n t ->
    on_elim (closedn n) e ->
    closedn n (mkElim t e).
Proof.
  intros n t e ht he.
  destruct e.
  - cbn in *. rewrite ht he. reflexivity.
  - cbn in *. destruct he as [hp hl].
    rewrite ht hp. cbn.
    eapply All_forallb. eapply All_impl. 1: eauto.
    intros [? ?]. cbn. auto.
  - cbn. assumption.
Qed.

Lemma elim_footprint_closedn_eq :
  ∀ t k n ui l τ,
    elim_footprint t = Some (k,n,ui,l,τ) →
    All (on_elim (closedn #|τ|)) l ×
    t = subst0 τ (fold_right (fun e t => mkElim t e) (tSymb k n ui) l).
Proof.
  intros t k n ui l τ e.
  induction t in k, n, ui, l, τ, e |- * using term_forall_list_ind.
  all: try solve [ cbn in e ; discriminate ].
  - cbn in e.
    destruct elim_footprint as [[[[[? ?] ?] l1] τ1]|] eqn:e1. 2: discriminate.
    destruct pattern_footprint eqn:e2.
    inversion e. subst. clear e.
    epose proof (pattern_footprint_closedn_eq _) as h.
    erewrite e2 in h. destruct h as [hc ?].
    specialize IHt1 with (1 := eq_refl).
    destruct IHt1 as [hl ?]. clear IHt2.
    subst. split.
    + rewrite app_length. rewrite plus_comm. constructor.
      * cbn. apply closedn_lift. assumption.
      * eapply All_impl. 1: eauto.
        intros e he. eapply on_elim_impl. 1: eauto.
        cbn. intros. eapply closed_upwards. 1: eauto.
        lia.
    + cbn. f_equal.
      * clear - hl. induction hl as [| e l he hl ih]. 1: reflexivity.
        cbn. rewrite 2!mkElim_subst. f_equal. 1: auto.
        { destruct e.
          - cbn in *. f_equal. rewrite subst_app_simpl. cbn.
            f_equal. symmetry. apply subst_closedn. assumption.
          - cbn in *. destruct he as [? ?]. f_equal.
            + rewrite subst_app_simpl. cbn.
              f_equal. symmetry. apply subst_closedn. assumption.
            + eapply All_map_eq. eapply All_impl. 1: eauto.
              intros [? ?]. cbn. unfold on_snd. cbn. intros.
              f_equal. rewrite subst_app_simpl. cbn.
              f_equal. symmetry. apply subst_closedn. assumption.
          - reflexivity.
        }
      * rewrite subst_app_decomp. f_equal. symmetry.
        eapply simpl_subst_k. rewrite map_length. reflexivity.
  - cbn in e. inversion e. subst. clear e.
    cbn. intuition constructor.
  - cbn in e.
    destruct elim_footprint as [[[[[? ?] ?] l1] τ1]|] eqn:e1. 2: discriminate.
    destruct pattern_footprint eqn:e2.
    destruct fold_right eqn:e3.
    inversion e. subst. clear e.
    clear IHt1.
    specialize IHt2 with (1 := eq_refl).
    destruct IHt2 as [hl ?]. subst.
    epose proof (pattern_footprint_closedn_eq _) as h.
    erewrite e2 in h. destruct h as [hc ?]. subst.
    cbn. rewrite subst_app_decomp. rewrite simpl_subst_k.
    { rewrite map_length. reflexivity. }
    rewrite subst_app_simpl. cbn. eapply subst_closedn in hc as sc.
    erewrite sc.
    unshelve eapply (left_apply (fun x => All_cons x _)).
    1:{
      eapply All_impl. 1: eauto.
      intros [] hy.
      - cbn in hy. cbn. rewrite app_length. eapply closed_upwards. 1: eauto.
        lia.
      - cbn in hy. destruct hy as [? ?].
        cbn. split.
        + rewrite app_length. eapply closed_upwards. 1: eauto.
          lia.
        + eapply All_impl. 1: eauto.
          intros [? ?]. cbn. rewrite app_length. intro h.
          eapply closed_upwards. 1: eauto.
          lia.
      - constructor.
    }
    cbn. rewrite app_length. rewrite plus_comm.
    unshelve eapply (left_apply (fun x => (_,x))).
    1:{
      eapply closedn_lift. rewrite app_length. eapply closed_upwards. 1: eauto.
      lia.
    }
    unshelve eapply (right_apply (fun (x : (_,_) = (_,_)) => f_equal (fun y => tCase _ _ y.1 y.2) x)).
    rewrite -/subst. rewrite <- unfold_map.
    clear - l3 l4 e3 l1 hl.
    induction l0 in l3, l4, e3, l1, hl |- *.
    + cbn in e3. inversion e3. subst. clear e3.
      cbn. intuition auto. f_equal.
      rewrite app_nil_r. rewrite subst_app_simpl. cbn. f_equal.
      symmetry. eapply subst_closedn.
      induction hl. 1: reflexivity.
      cbn. apply closedn_mkElim. all: auto.
    + cbn in e3. destruct pattern_footprint eqn:e1.
      destruct fold_right eqn:e2.
      inversion e3. subst. clear e3.
      specialize IHl0 with (1 := eq_refl) (2 := hl).
      destruct IHl0 as [? ?].
      split.
      * {
        constructor.
        - cbn. rewrite !app_length.
          match goal with
          | |- context [ ?x + (?y + ?z) + ?t ] =>
            replace (x + (y + z) + t) with (z + (t + x + y)) by lia
          end.
          apply closedn_lift.
          epose proof (pattern_footprint_closedn_eq _) as hc.
          erewrite e1 in hc. intuition auto.
        - eapply All_impl. 1: eauto.
          intros [? ?]. cbn. rewrite !app_length. intro h.
          eapply closed_upwards. 1: eauto.
          lia.
      }
      * {
        f_equal.
        - rewrite subst_app_simpl. cbn. f_equal.
          symmetry. eapply subst_closedn.
          clear - hl.
          induction hl. 1: reflexivity.
          cbn. apply closedn_mkElim. all: auto.
        - cbn.
          match goal with
          | |- ?a :: _ = _ =>
            destruct a
          end.
          cbn. unfold on_snd at 1. cbn.
          match goal with
          | |- context [ ?x ++ ?y ++ ?z ++ ?t ] =>
            replace (x ++ y ++ z ++ t) with ((x ++ y ++ z) ++ t)
          end.
          2:{ rewrite !app_assoc. reflexivity. }
          rewrite subst_app_decomp. rewrite simpl_subst_k.
          { rewrite map_length. rewrite !app_length. lia. }
          epose proof (pattern_footprint_closedn_eq _) as hc.
          erewrite e1 in hc. cbn in hc. destruct hc as [hc ?]. subst.
          f_equal. inversion e.
          eapply All_map_eq. eapply All_impl. 1: eauto.
          intros [? ?]. unfold on_snd. cbn. intros h.
          f_equal.
          rewrite [RHS]subst_app_simpl. cbn. f_equal.
          symmetry. eapply subst_closedn.
          rewrite !app_length. rewrite app_length in h.
          rewrite plus_comm. assumption.
      }
  - cbn in e.
    destruct elim_footprint as [[[[[? ?] ?] l1] τ1]|] eqn:e1. 2: discriminate.
    inversion e. subst. clear e.
    specialize IHt with (1 := eq_refl).
    destruct IHt as [hl ?]. subst. cbn.
    intuition eauto.
    constructor. 2: auto.
    cbn. constructor.
Qed.

Local Notation prelhs k n ui l :=
  (fold_right (fun e t => mkElim t e) (tSymb k n ui) l).

Lemma match_prelhs_closedn :
  ∀ npat t k n l ui σ m,
    All (elim_pattern npat) l →
    closedn m t →
    match_prelhs npat k n l t = Some (ui, σ) →
    All (on_Some (closedn m)) σ.
Proof.
  intros npat t k n l ui σ m hl hc e.
  induction hl as [| ? l [] hl ih ] in t, σ, m, hc, e |- *.
  - cbn in e. destruct t. all: try discriminate.
    assert_eq e. assert_eq e. subst. cbn in e.
    inversion e. subst. clear e.
    apply All_on_Some_subs_empty.
  - cbn in e. destruct t. all: try discriminate.
    destruct match_pattern eqn:e1. 2: discriminate.
    destruct match_prelhs as [[? ?]|] eqn:e2. 2: discriminate.
    destruct subs_merge eqn:e3. 2: discriminate.
    inversion e. subst. clear e.
    cbn in hc. apply andP in hc. destruct hc.
    eapply match_pattern_closedn in e1. 2,3: eauto.
    eapply ih in e2. 2: eauto.
    eapply All_on_Some_subs_merge. all: eauto.
  - cbn in e. destruct t. all: try discriminate.
    assert_eq e. subst. cbn in e.
    destruct match_pattern eqn:e1. 2: discriminate.
    destruct option_map2 as [l1|] eqn:e2. 2: discriminate.
    destruct PCUICPattern.monad_fold_right as [l2|] eqn:e3. 2: discriminate.
    destruct match_prelhs as [[]|] eqn:e4. 2: discriminate.
    destruct subs_merge eqn:e5. 2: discriminate.
    move e at top.
    destruct subs_merge eqn:e6. 2: discriminate.
    inversion e. subst. clear e.
    cbn in hc. apply andP in hc. destruct hc as [hc cl].
    apply andP in hc. destruct hc as [? ?].
    eapply ih in e4. 2: eauto.
    eapply match_pattern_closedn in e1. 2,3: eauto.
    eapply All_on_Some_subs_merge. 1,3: eauto.
    eapply All_on_Some_subs_merge. 1,2: eauto.
    clear - a brs0 l1 e2 l2 e3 cl.
    induction a in brs0, l1, e2, l2, e3, cl |- *.
    + destruct brs0. 2: discriminate.
      cbn in e2. apply some_inj in e2. subst.
      cbn in e3. apply some_inj in e3. subst.
      apply All_on_Some_subs_empty.
    + destruct brs0. 1: discriminate.
      cbn in e2. assert_eq e2. cbn in e2.
      destruct match_pattern eqn:e1. 2: discriminate.
      destruct option_map2 eqn:e4. 2: discriminate.
      apply some_inj in e2. subst.
      cbn in e3. destruct PCUICPattern.monad_fold_right eqn:e5. 2: discriminate.
      cbn in cl. apply andP in cl. unfold test_snd in cl. destruct cl as [? ?].
      eapply IHa in e4. 2,3: eauto.
      eapply All_on_Some_subs_merge. 1,2: eauto.
      eapply match_pattern_closedn. all: eauto.
  - cbn in e. destruct t. all: try discriminate.
    assert_eq e. subst. cbn in e.
    cbn in hc.
    eapply ih in e. 2: eauto.
    assumption.
Qed.

Lemma prelhs_closedn :
  ∀ k n ui l m,
    All (on_elim (closedn m)) l →
    closedn m (prelhs k n ui l).
Proof.
  intros k n ui l m h.
  induction h as [| [] l h hl ih ].
  - cbn. reflexivity.
  - cbn in *. rewrite ih. assumption.
  - cbn in *. destruct h as [h1 h2]. rewrite h1 ih. cbn.
    eapply All_forallb. assumption.
  - cbn in *. assumption.
Qed.

Definition pattern_brs_footprint k1 k2 (brs : list (nat × term)) :=
  fold_right
    (λ '(n, (p, a)) '(pl, al),
        ((n, lift0 (k1 + k2 + #|al|) p) :: pl, al ++ a)
    )
    ([], [])
    (map (on_snd pattern_footprint) brs).

Lemma pattern_brs_footprint_unfold :
  forall k1 k2 brs,
    pattern_brs_footprint k1 k2 brs =
    fold_right
      (λ '(n, (p, a)) '(pl, al),
          ((n, lift0 (k1 + k2 + #|al|) p) :: pl, al ++ a)
      )
      ([], [])
      (map (on_snd pattern_footprint) brs).
Proof.
  reflexivity.
Defined.

Lemma elim_footprint_match_prelhs :
  ∀ npat t k n l ui σ,
    All (elim_pattern npat) l →
    match_prelhs npat k n l t = Some (ui, σ) →
    ∑ l' τ θ,
      elim_footprint t = Some (k, n, ui, l', τ) ×
      match_prelhs npat k n l (prelhs k n ui l') = Some (ui, θ) ×
      map (option_map (subst0 τ)) θ = σ.
Proof.
  intros npat t k n l ui σ h e.
  induction h as [| ? l [] hl ih ] in t, σ, e |- *.
  - cbn in e. destruct t. all: try discriminate.
    cbn. assert_eq e. assert_eq e. subst.
    cbn in e. inversion e. subst. clear e.
    eexists _, _, _. intuition eauto.
    + cbn. rewrite assert_eq_refl. rewrite assert_eq_refl. reflexivity.
    + unfold subs_empty. rewrite map_list_init. reflexivity.
  - cbn in e. destruct t. all: try discriminate.
    destruct match_pattern eqn:e1. 2: discriminate.
    destruct match_prelhs as [[? ?]|] eqn:e2. 2: discriminate.
    destruct subs_merge eqn:e3. 2: discriminate.
    inversion e. subst. clear e.
    eapply ih in e2 as e4. destruct e4 as [l' [τ1 [θ1 [e4 [e5 e6]]]]]. clear ih.
    eapply pattern_footprint_match_pattern in e1 as e7. 2: auto.
    destruct pattern_footprint eqn:e8.
    destruct e7 as [θ2 [e9 e10]].
    cbn. rewrite e4. rewrite e8.
    match goal with
    | |- context [ Some (_,_,_, ?l, ?t) = _ ] =>
      exists l, t
    end.
    cbn.
    eapply match_pattern_lift in e9 as e11. 2: auto.
    erewrite e11.
    rewrite e5.
    subst.
    match goal with
    | e : subs_merge _ _ = ?z
      |- context [ subs_merge ?x ?y ] =>
      match goal with
      | |- context [ map  ?f _ = _ ] =>
        assert (h : subs_merge (map f x) (map f y) = z)
      end
    end.
    { rewrite <- e3. f_equal.
      - rewrite map_map_compose. eapply map_ext.
        intros o. rewrite option_map_two.
        eapply option_map_ext.
        intros v.
        rewrite subst_app_decomp. f_equal.
        eapply simpl_subst_k. rewrite map_length. reflexivity.
      - eapply elim_footprint_closedn_eq in e4 as h. destruct h as [hc _].
        eapply match_prelhs_closedn in e5. 2: auto.
        2:{ eapply prelhs_closedn. eassumption. }
        eapply All_map_eq. eapply All_impl. 1: eauto.
        intros [] h. 2: reflexivity.
        cbn in h. cbn. f_equal.
        rewrite subst_app_simpl. cbn.
        eapply subst_closedn in h. erewrite h. reflexivity.
    }
    eapply subs_merge_map_inv in h as [ρ [e12 ?]]. subst.
    rewrite e12.
    eexists. intuition eauto.
  - cbn in e. destruct t. all: try discriminate.
    assert_eq e. subst. cbn in e.
    destruct match_pattern eqn:e1. 2: discriminate.
    destruct option_map2 eqn:e2. 2: discriminate.
    destruct PCUICPattern.monad_fold_right eqn:e3. 2: discriminate.
    destruct match_prelhs as [[]|] eqn:e4. 2: discriminate.
    destruct subs_merge eqn:e5. 2: discriminate.
    move e at top.
    destruct subs_merge eqn:e6. 2: discriminate.
    inversion e. subst. clear e.
    eapply ih in e4 as e7. destruct e7 as [l' [τ1 [θ1 [e7 [e8 e9]]]]]. clear ih.
    eapply pattern_footprint_match_pattern in e1 as e10. 2: auto.
    destruct pattern_footprint eqn:e11.
    destruct e10 as [θ2 [e10 e12]].
    cbn. rewrite e7. rewrite e11.
    destruct (fold_right _ _ (map _ _)) eqn:e13.
    lazymatch goal with
    | |- context [ Some (_,_,_, ?l, ?t) = _ ] =>
      exists l, t
    end.
    cbn. rewrite assert_eq_refl.
    eapply match_pattern_lift in e10 as e14. 2: auto.
    erewrite e14.
    rewrite e8.
    assert (h : ∀ R A (P Q : A -> Type), R → (∑ x, P x × Q x) → ∑ x, R × P x × Q x).
    { clear. intros R A P Q h [x [? ?]].
      exists x. intuition auto.
    }
    eapply h. 1: reflexivity.
    clear h. subst.
    rewrite <- pattern_brs_footprint_unfold in e13.
    (* lazymatch goal with
    | e : option_map2 _ _ _ = Some ?σ,
      w : pattern_brs_footprint ?a ?b _ = (?u, ?v)
      |- context [ option_map2 ?f ?l1 ?l2 ] =>
      assert (h :
        ∑ θ,
          option_map2 f l1 l2 = Some θ ×
          map (map (option_map (subst0 v))) θ =
          map (map (option_map (lift0 (a + b)))) σ
      )
    end.
    { clear - a e2 e13.
      induction a as [| [? ?] brs hp hb ih] in brs0, l1, e2, l6, l7, e13 |- *.
      - destruct brs0. 2: discriminate.
        cbn in e2. apply some_inj in e2. subst.
        cbn in e13. inversion e13. subst.
        cbn. eexists. intuition eauto.
      - destruct brs0 as [| [] brs0]. 1: discriminate.
        cbn in e2. assert_eq e2. subst. cbn in e2.
        destruct match_pattern eqn:e1. 2: discriminate.
        destruct option_map2 eqn:e3. 2: discriminate.
        apply some_inj in e2. subst.
        cbn in e13. destruct pattern_footprint eqn:e4.
        destruct fold_right eqn:e5.
        rewrite <- pattern_brs_footprint_unfold in e5.
        inversion e13. subst. clear e13.
        specialize ih with (1 := e3) (2 := e5).
        destruct ih as [θ [h1 h2]].
        cbn. rewrite assert_eq_refl.
        eapply pattern_footprint_match_pattern in e1 as h. 2: auto.
        rewrite e4 in h.
        destruct h as [τ [e6 ?]]. subst.
        eapply match_pattern_lift in e6 as e7. 2: auto.
        erewrite e7. rewrite h1.
        eexists. intuition eauto.
        cbn. f_equal.
        + rewrite !map_map_compose. eapply map_ext.
          intro o. rewrite !option_map_two. apply option_map_ext.
          intro x.
          match goal with
          | |- context [ ?x + ?y + ?z ] =>
            replace (x + y + z) with (z + (x + y)) by lia
          end.
          erewrite <- simpl_lift with (i := 0). 2,3: lia.
          rewrite subst_app_decomp. rewrite simpl_subst_k.
          { rewrite map_length. reflexivity. }
          (* epose proof (pattern_footprint_closedn_eq _) as h.
          erewrite e4 in h. destruct h as [hc ?]. subst.
          eapply match_pattern_closedn in hc. 2,3: eauto. *)
    } *)


    lazymatch goal with
    | e : option_map2 _ _ _ = Some ?σ,
      w : pattern_brs_footprint _ _ _ = (?u, ?v),
      c : PCUICPattern.monad_fold_right _ _ _ = Some ?ρ
      |- context [ option_map2 ?f ?l1 ?l2 ] =>
      assert (h :
        ∑ θ α,
          option_map2 f l1 l2 = Some θ ×
          PCUICPattern.monad_fold_right subs_merge θ (subs_empty npat) =
          Some α ×
          map (option_map (subst0 v)) α = ρ
      )
    end.
    { clear - a e2 e3 e13.
      induction a as [| [? ?] brs hp hb ih]
      in brs0, l1, e2, l2, e3, l6, l7, e13 |- *.
      - destruct brs0. 2: discriminate.
        cbn in e2. apply some_inj in e2. subst.
        cbn in e13. inversion e13. subst. clear e13.
        cbn in e3. apply some_inj in e3. subst.
        cbn. eexists _,_. intuition eauto.
        unfold subs_empty. rewrite map_list_init. reflexivity.
      - destruct brs0 as [| [] brs0]. 1: discriminate.
        cbn in e2. assert_eq e2. subst. cbn in e2.
        destruct match_pattern eqn:e1. 2: discriminate.
        destruct option_map2 eqn:e4. 2: discriminate.
        apply some_inj in e2. subst.
        cbn in e3.
        destruct PCUICPattern.monad_fold_right eqn:e2. 2: discriminate.
        cbn in e13. destruct pattern_footprint eqn:e5.
        destruct fold_right eqn:e6.
        rewrite <- pattern_brs_footprint_unfold in e6.
        inversion e13. subst. clear e13.
        specialize ih with (1 := e4) (2 := e2) (3 := e6).
        destruct ih as [θ [α [e7 [e8 e11]]]].
        cbn in *. rewrite assert_eq_refl.
        eapply pattern_footprint_match_pattern in e1 as h. 2: auto.
        rewrite e5 in h.
        destruct h as [τ [e9 ?]]. subst.
        eapply match_pattern_lift in e9 as e10. 2: auto.
        erewrite e10.
        rewrite e7.
        match goal with
        | |- context [ Some ?x = Some _ ] =>
          exists x
        end.
        cbn. rewrite e8.
        match goal with
        | e : subs_merge _ _ = ?z
          |- context [ subs_merge ?x ?y ] =>
          match goal with
          | |- context [ map  ?f _ = _ ] =>
            assert (h : subs_merge (map f x) (map f y) = z)
          end
        end.
        { rewrite <- e3. f_equal.
          - (* apply All_map_eq. *)
            eapply map_ext.
            intros o. eapply option_map_ext.
            intros v.
            rewrite subst_app_simpl. cbn. f_equal.
            (* eapply subst_closedn. *)
            admit.
          - rewrite map_map_compose. eapply All_map_eq.
            epose proof (pattern_footprint_closedn_eq _) as e11.
            erewrite e5 in e11. destruct e11 as [? ?].
            eapply match_pattern_closedn in e9 as ?. 2,3: eauto.
            eapply All_impl. 1: eauto.
            intros [] h. 2: reflexivity.
            cbn in h. cbn. f_equal.
            rewrite subst_app_decomp. f_equal.
            match goal with
            | |- context [ ?x + ?y + ?z ] =>
              replace (x + y + z) with (z + (x + y)) by lia
            end.
            erewrite <- simpl_lift with (i := 0). 2,3: lia.
            rewrite simpl_subst_k.
            { rewrite map_length. reflexivity. }
            admit.
        }
        eapply subs_merge_map_inv in h as [ρ [e12 ?]]. subst.
        rewrite e12.
        eexists. intuition eauto.

        (* cbn. f_equal.
        + rewrite -> map_map_compose. eapply map_ext.
          intros o. rewrite option_map_two. apply option_map_ext.
          intros v. rewrite subst_app_decomp. f_equal.
          match goal with
          | |- context [ ?x + ?y + ?z ] =>
            replace (x + y + z) with (z + (x + y)) by lia
          end.
          erewrite <- simpl_lift with (i := 0). 2,3: lia.
          rewrite simpl_subst_k.
          { rewrite map_length. reflexivity. }
          (* TODO Even knowing it comes from τ seems like I won't be able to
            get this...
          *)
          give_up.
        + (* Need to prove that θ is closed under l8 as well! Or l7 *)
          give_up. *)
    }
    destruct h as [θ [α [h1 [h2 h3]]]].
    rewrite h1. rewrite h2. subst.
    match goal with
    | e : subs_merge _ _ = ?z
      |- context [ subs_merge ?x ?y ] =>
      match goal with
      | |- context [ map  ?f _ = _ ] =>
        assert (h : subs_merge (map f x) (map f y) = z)
      end
    end.
    { rewrite <- e5. f_equal.
      - (* rewrite map_map_compose. eapply map_ext.
        intros o. rewrite option_map_two.
        eapply option_map_ext.
        intros v.
        rewrite subst_app_decomp. f_equal.
        eapply simpl_subst_k. rewrite map_length. reflexivity. *)
        admit.
      - (* eapply elim_footprint_closedn_eq in e4 as h. destruct h as [hc _].
        eapply match_prelhs_closedn in e5. 2: auto.
        2:{ eapply prelhs_closedn. eassumption. }
        eapply All_map_eq. eapply All_impl. 1: eauto.
        intros [] h. 2: reflexivity.
        cbn in h. cbn. f_equal.
        rewrite subst_app_simpl. cbn.
        eapply subst_closedn in h. erewrite h. reflexivity. *)
        admit.
    }
    (* destruct h as [θ [e15 ?]]. subst.
    rewrite e15. *)
    (* TODO Maybe I should include monad_fold_right in the assert above as
      well? I did the proof using it, so it seems fair.
      Perhaps it will solve my equality.
      *)
    admit.
  - cbn in e. destruct t. all: try discriminate.
    assert_eq e. subst. cbn in e.
    eapply ih in e as [l' [τ [θ [e1 [e2 e3]]]]].
    cbn. rewrite e1.
    eexists _, _, _. intuition eauto.
    cbn. rewrite assert_eq_refl. assumption.
Admitted.
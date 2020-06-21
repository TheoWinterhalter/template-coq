(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils Universes BasicAst
  AstUtils UnivSubst EnvironmentTyping.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition.

Import MonadNotation.

Set Default Goal Selector "!".

(** Pattern definition

  This definition is relative to the number of pattern variables.

  TODO Can we have an "exact" pattern this way?

  TODO How to guarantee the tConstruct is fully applied?
  Maybe we don't have to.

  TODO Remove symbols for now.
*)
Inductive pattern (npat : nat) : term -> Type :=
| pattern_variable :
    forall n,
      n < npat ->
      pattern npat (tRel n)

| pattern_construct :
    forall ind n ui args,
      All (pattern npat) args ->
      pattern npat (mkApps (tConstruct ind n ui) args)

(* | pattern_symbol :
    forall k n ui args,
      All (pattern npat) args ->
      pattern npat (mkApps (tSymb k n ui) args) *)
.

Inductive elim_pattern (npat : nat) : elimination -> Type :=
| pat_elim_App :
    forall p,
      pattern npat p ->
      elim_pattern npat (eApp p)

| pat_elim_Case :
    forall indn p brs,
      pattern npat p ->
      All (fun br => pattern npat br.2) brs ->
      elim_pattern npat (eCase indn p brs)

| pat_elim_Proj :
    forall p,
      elim_pattern npat (eProj p).

Lemma pattern_all_rect :
  forall npat (P : term -> Type),
    (forall n,
      n < npat ->
      P (tRel n)
    ) ->
    (forall ind n ui args,
      All (pattern npat) args ->
      All P args ->
      P (mkApps (tConstruct ind n ui) args)
    ) ->
    forall p, pattern npat p -> P p.
Proof.
  intros npat P hRel hCons.
  fix aux 2. move aux at top.
  intros p hp. destruct hp.
  - apply hRel. auto.
  - apply hCons. 1: auto.
    revert args a. fix auxa 2.
    intros args h. destruct h. 1: constructor.
    constructor. all: auto.
Qed.

(** Notion of linearity

  We use a notion of linear mask. Similar to partial substitutions.
*)

(* TODO MOVE *)
Fixpoint list_init {A} (x : A) (n : nat) : list A :=
  match n with
  | 0 => []
  | S n => x :: list_init x n
  end.

(* TODO MOVE *)
Lemma list_init_length :
  forall A (x : A) n,
    #|list_init x n| = n.
Proof.
  intros A x n. induction n. 1: reflexivity.
  cbn. f_equal. assumption.
Qed.

Definition linear_mask_init (npat : nat) :=
  list_init false npat.

Fixpoint lin_merge (a b : list bool) : option (list bool) :=
  match a, b with
  | false :: a, x :: b
  | x :: a, false :: b =>
    l <- lin_merge a b ;;
    ret (x :: l)
  | [], [] => ret []
  | _, _ => None
  end.

Fixpoint lin_set (n : nat) (l : list bool) : option (list bool) :=
  match n, l with
  | 0, false :: l => ret (true :: l)
  | S n, b :: l =>
    l' <- lin_set n l ;;
    ret (b :: l')
  | _, _ => None
  end.

(* TODO MOVE *)
Fixpoint monad_fold_right {T} {M : Monad T} {A B} (g : A -> B -> T A)
  (l : list B) (x : A) : T A :=
  match l with
  | [] => ret x
  | y :: l =>
      a <- monad_fold_right g l x ;;
      g a y
  end.

Fixpoint pattern_mask npat p :=
  match p with
  | tRel n => lin_set n (linear_mask_init npat)
  | tConstruct ind n ui => ret (linear_mask_init npat)
  | tApp u v =>
    um <- pattern_mask npat u ;;
    vm <- pattern_mask npat v ;;
    lin_merge um vm
  | _ => None
  end.

Definition elim_mask npat e :=
  match e with
  | eApp p => pattern_mask npat p
  | eCase ind p brs =>
    lp <- pattern_mask npat p ;;
    lb <- monad_map (fun p => pattern_mask npat p.2) brs ;;
    lb <- monad_fold_right lin_merge lb (linear_mask_init npat) ;;
    lin_merge lp lb
  | eProj p => ret (linear_mask_init npat)
  end.

Definition linear_mask npat (el : list elimination) :=
  l <- monad_map (elim_mask npat) el ;;
  monad_fold_right lin_merge l (linear_mask_init npat).

Definition linear npat (el : list elimination) :=
  match linear_mask npat el with
  | Some l => forallb (fun x => x) l
  | None => false
  end.

(** Notion of partial substitutions *)

Notation partial_subst := (list (option term)).

(* Structure to build a substitution *)
Definition subs_empty npat : list (option term) :=
  list_init None npat.

Definition subs_add x t (l : partial_subst) : option (partial_subst) :=
  match nth_error l x with
  | None => None
  | Some None => Some (firstn x l ++ Some t :: skipn (S x) l)
  | Some (Some _) => None
  end.

Definition subs_init npat x t :=
  subs_add x t (subs_empty npat).

Fixpoint subs_merge (s1 s2 : partial_subst) : option (partial_subst) :=
  match s1, s2 with
  | [], [] => ret []
  | None :: s1, d :: s2
  | d :: s1, None :: s2 =>
    s <- subs_merge s1 s2 ;; ret (d :: s)
  | _, _ => None
  end.

Lemma subs_empty_length :
  forall n,
    #|subs_empty n| = n.
Proof.
  intros n. unfold subs_empty. apply list_init_length.
Qed.

Inductive subs_complete : list (option term) -> list term -> Prop :=
| subs_complete_nil : subs_complete [] []
| subs_complete_Some :
    forall a s s',
      subs_complete s s' ->
      subs_complete (Some a :: s) (a :: s')
| subs_complete_None :
    forall a s s',
      subs_complete s s' ->
      subs_complete (None :: s) (a :: s').

Lemma subs_complete_spec :
  forall s s',
    subs_complete s s' <->
    (#|s| = #|s'| /\
     forall n t, nth_error s n = Some (Some t) -> nth_error s' n = Some t).
Proof.
  intros s s'. split.
  - intro h. induction h.
    + split. 1: reflexivity.
      intros [] t e. all: discriminate.
    + cbn. destruct IHh as [el ih].
      split. 1: auto.
      intros [|n] t e.
      * cbn in *. apply some_inj in e. assumption.
      * cbn in *. eapply ih. assumption.
    + cbn. destruct IHh as [el ih].
      split. 1: auto.
      intros [|n] t e.
      * cbn in *. discriminate.
      * cbn in *. eapply ih. assumption.
  - intros [e h]. induction s in s', e, h |- *.
    + destruct s'. 2: discriminate.
      constructor.
    + destruct s'. 1: discriminate.
      cbn in e. destruct a.
      * specialize h with (n := 0) as h'.
        cbn in h'. specialize h' with (1 := eq_refl).
        apply some_inj in h'. subst.
        constructor.
        eapply IHs. 1: lia.
        intros n t hn.
        specialize h with (n := S n). cbn in h.
        eapply h. assumption.
      * constructor. eapply IHs. 1: lia.
        intros n ? hn.
        specialize h with (n := S n). cbn in h.
        eapply h. assumption.
Qed.

Lemma subs_complete_length :
  forall s s',
    subs_complete s s' ->
    #|s| = #|s'|.
Proof.
  intros s s' h.
  apply subs_complete_spec in h. apply h.
Qed.

Lemma subs_merge_complete :
  forall s1 s2 s,
    subs_merge s1 s2 = Some s ->
    forall s',
      subs_complete s s' ->
      subs_complete s1 s' /\ subs_complete s2 s'.
Proof.
  intros s1 s2 s e s' hs. induction hs in s1, s2, e |- *.
  - assert (h : s1 = [] /\ s2 = []).
    { induction s1 as [| [] s1 ih] in s2, e |- *.
      - destruct s2.
        + intuition auto.
        + cbn in e. discriminate.
      - destruct s2 as [| [] s2]. 1-2: discriminate.
        cbn in e. destruct subs_merge eqn:e1. all: discriminate.
      - destruct s2 as [| [] s2]. 1: discriminate.
        + cbn in e. destruct subs_merge eqn:e1. all: discriminate.
        + cbn in e. destruct subs_merge eqn:e1. all: discriminate.
    }
    destruct h. subst. intuition constructor.
  - destruct s1 as [| [] s1], s2 as [| [] s2]. all: try discriminate.
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. 2: discriminate.
      apply some_inj in e. inversion e. subst. clear e.
      eapply IHhs in es as [h1 h2].
      intuition (constructor ; auto).
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. 2: discriminate.
      apply some_inj in e. inversion e. subst. clear e.
      eapply IHhs in es as [h1 h2].
      intuition (constructor ; auto).
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. all: discriminate.
  - destruct s1 as [| [] s1], s2 as [| [] s2]. all: try discriminate.
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. all: discriminate.
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. all: discriminate.
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. 2: discriminate.
      inversion e. subst.
      eapply IHhs in es as [h1 h2].
      intuition (constructor ; auto).
Qed.

Lemma subs_init_nth_error :
  forall npat n t s,
    subs_init npat n t = Some s ->
    nth_error s n = Some (Some t).
Proof.
  intros npat n t s e.
  unfold subs_init in e. unfold subs_add in e.
  destruct nth_error eqn:en. 2: discriminate.
  destruct o. 1: discriminate.
  apply some_inj in e. subst.
  rewrite nth_error_app_ge. 2: apply firstn_le_length.
  rewrite firstn_length.
  apply nth_error_Some_length in en.
  match goal with
  | |- nth_error _ ?n = _ => replace n with 0 by lia
  end.
  cbn. reflexivity.
Qed.

(** Matching *)

Definition assert_true (b : bool) : option () :=
  if b then ret () else None.

Definition assert_eq {A} `{ReflectEq A} (x y : A) : option () :=
  assert_true (eqb x y).

Fixpoint match_pattern npat p t :=
  match p with
  | tRel n => subs_init npat n t
  | tConstruct ind n ui =>
    assert_eq p t ;;
    ret (subs_empty npat)
  | tApp p1 p2 =>
    match t with
    | tApp u v =>
      σ <- match_pattern npat p1 u ;;
      θ <- match_pattern npat p2 v ;;
      subs_merge σ θ
    | _ => None
    end
  | _ => None
  end.

(* We could do it on the proof of pattern *)
(* Fixpoint match_pattern {npat p} (hp : pattern npat p) t :=
  match hp with
  | pattern_variable n hn =>
    subs_init npat n t
  | pattern_construct ind n ui args hargs =>
    let '(u,l) decompose_app t in
    assert_eq (tConstruct ind n ui) u ;;
    ??
  end. *)

(* TODO MOVE *)
Lemma All_rev_rect :
  forall A P (R : list A -> Type),
    R [] ->
    (forall x l,
      P x ->
      All P l ->
      R l ->
      R (l ++ [x])
    ) ->
    forall l, All P l -> R l.
Proof.
  intros A P R Rnil Rcons l h.
  rewrite <- rev_involutive.
  apply All_rev in h. revert h.
  generalize (List.rev l). clear l.
  intros l h. induction h.
  - apply Rnil.
  - cbn. apply Rcons. all: auto.
    apply All_rev. assumption.
Qed.

Ltac assert_eq e :=
  match type of e with
  | context C [ assert_eq ?x ?y ] =>
    let C1 := context C [ assert_true (eqb x y) ] in
    let C2 := context C [ ret () ] in
    change C1 in e ;
    destruct (eqb_spec x y) ; [
      change C2 in e
    | discriminate
    ]
  end.

Lemma match_pattern_sound :
  forall npat p t σ,
    pattern npat p ->
    match_pattern npat p t = Some σ ->
    forall θ,
      subs_complete σ θ ->
      t = subst0 θ p.
Proof.
  intros npat p t σ hp e θ hc.
  induction hp
  as [n hn | ind n ui args ha ih]
  in t, σ, e, θ, hc |- *
  using pattern_all_rect.
  - cbn in e. cbn.
    replace (n - 0) with n by lia.
    eapply subs_init_nth_error in e.
    apply subs_complete_spec in hc as [l h].
    apply h in e. rewrite e.
    rewrite lift0_id. reflexivity.
  - eapply All_prod in ih. 2: exact ha.
    clear ha.
    induction ih
    as [| p args [hp ihp] _ ih]
    in t, σ, e, θ, hc |- *
    using All_rev_rect.
    + cbn. unfold mkApps in e.
      unfold match_pattern in e.
      assert_eq e. auto.
    + rewrite <- mkApps_nested. cbn.
      rewrite <- mkApps_nested in e. cbn in e.
      destruct t. all: try discriminate.
      destruct match_pattern eqn:e1. 2: discriminate.
      move e at top.
      destruct match_pattern eqn:e2. 2: discriminate.
      eapply subs_merge_complete in e as sc. 2: eassumption.
      destruct sc as [? ?].
      eapply ihp in e2. 2: eassumption.
      eapply ih in e1. 2: eassumption.
      subst. reflexivity.
Qed.

Lemma nth_error_list_init :
  forall A (x : A) n l,
    n < l ->
    nth_error (list_init x l) n = Some x.
Proof.
  intros A x n l h.
  induction l in n, h |- *. 1: lia.
  cbn. destruct n.
  - cbn. reflexivity.
  - cbn. apply IHl. lia.
Qed.

Lemma nth_error_subs_empty :
  forall npat n,
    n < npat ->
    nth_error (subs_empty npat) n = Some None.
Proof.
  intros npat n h.
  apply nth_error_list_init. assumption.
Qed.

(* Lemma list_init_length :
  forall A (x : A) n,
    #|list_init x n| = n.
Proof.
  intros A x n. induction n. 1: reflexivity.
  cbn. f_equal. assumption.
Qed. *)

Lemma firstn_list_init :
  forall A n m (x : A),
    firstn n (list_init x m) = list_init x (min n m).
Proof.
  intros A n m x.
  induction n in m |- *. 1: reflexivity.
  destruct m. 1: reflexivity.
  cbn. f_equal. apply IHn.
Qed.

Lemma skipn_list_init :
  forall A n m (x : A),
    skipn n (list_init x m) = list_init x (m - n).
Proof.
  intros A n m x.
  induction m in n |- *.
  - cbn. rewrite skipn_nil. reflexivity.
  - destruct n. 1: reflexivity.
    cbn. apply IHm.
Qed.

Lemma nth_error_app_dec :
  forall A (l l' : list A) n x,
    nth_error (l ++ l') n = Some x ->
    (n < #|l| /\ nth_error l n = Some x) +
    (n >= #|l| /\ nth_error l' (n - #|l|) = Some x).
Proof.
  intros A l l' n x e.
  destruct (Nat.ltb_spec0 n #|l|).
  - left. rewrite -> nth_error_app1 in e by assumption.
    intuition lia.
  - right. rewrite -> nth_error_app2 in e by lia.
    intuition lia.
Qed.

Lemma subs_complete_subs_empty :
  forall npat σ,
    #|σ| = npat ->
    subs_complete (subs_empty npat) σ.
Proof.
  intros npat σ eσ.
  apply subs_complete_spec. split.
  - rewrite subs_empty_length. auto.
  - intros n t e.
    apply nth_error_Some_length in e as l.
    rewrite subs_empty_length in l.
    rewrite nth_error_subs_empty in e by auto.
    discriminate.
Qed.

Inductive masks : list bool -> partial_subst -> Type :=
| masks_nil : masks [] []
| masks_true :
    forall m σ t,
      masks m σ ->
      masks (true :: m) (Some t :: σ)
| masks_false :
    forall m σ,
      masks m σ ->
      masks (false :: m) (None :: σ).

Lemma lin_set_eq :
  forall n m,
    lin_set n m =
    match nth_error m n with
    | Some true => None
    | Some false => Some (firstn n m ++ true :: skipn (S n) m)
    | None => None
    end.
Proof.
  intros n m.
  induction n in m |- *.
  - cbn. destruct m as [| [] m]. all: reflexivity.
  - cbn. destruct m as [| [] m].
    + reflexivity.
    + destruct lin_set eqn:e.
      * cbn. rewrite IHn in e.
        destruct nth_error as [[]|] eqn: e1. 1,3: discriminate.
        apply some_inj in e. subst.
        reflexivity.
      * cbn. rewrite IHn in e.
        destruct nth_error as [[]|] eqn: e1. 2: discriminate.
        all: reflexivity.
    + destruct lin_set eqn:e.
      * cbn. rewrite IHn in e.
        destruct nth_error as [[]|] eqn: e1. 1,3: discriminate.
        apply some_inj in e. subst.
        reflexivity.
      * cbn. rewrite IHn in e.
        destruct nth_error as [[]|] eqn: e1. 2: discriminate.
        all: reflexivity.
Qed.

Lemma masks_app :
  forall m1 m2 σ1 σ2,
    masks m1 σ1 ->
    masks m2 σ2 ->
    masks (m1 ++ m2) (σ1 ++ σ2).
Proof.
  intros m1 m2 σ1 σ2 h1 h2.
  induction h1 in m2, σ2, h2 |- *.
  - assumption.
  - cbn. constructor.
    apply IHh1. assumption.
  - cbn. constructor.
    apply IHh1. assumption.
Qed.

Lemma masks_firstn :
  forall m σ n,
    masks m σ ->
    masks (firstn n m) (firstn n σ).
Proof.
  intros m σ n h.
  induction h in n |- *.
  - destruct n. all: constructor.
  - destruct n.
    + cbn. constructor.
    + cbn. constructor. apply IHh.
  - destruct n.
  + cbn. constructor.
  + cbn. constructor. apply IHh.
Qed.

Lemma masks_skipn :
  forall m σ n,
    masks m σ ->
    masks (skipn n m) (skipn n σ).
Proof.
  intros m σ n h.
  induction h in n |- *.
  - destruct n. all: constructor.
  - destruct n.
    + unfold skipn. constructor. assumption.
    + rewrite 2!skipn_S. apply IHh.
  - destruct n.
    + unfold skipn. constructor. assumption.
    + rewrite 2!skipn_S. apply IHh.
Qed.

Lemma masks_linear_mask_init :
  forall n,
    masks (linear_mask_init n) (subs_empty n).
Proof.
  intro n. induction n.
  - constructor.
  - cbn. constructor. assumption.
Qed.

Lemma masks_merge :
  forall m1 m2 m σ1 σ2,
    lin_merge m1 m2 = Some m ->
    masks m1 σ1 ->
    masks m2 σ2 ->
    ∑ σ,
      subs_merge σ1 σ2 = Some σ ×
      masks m σ.
Proof.
  intros m1 m2 m σ1 σ2 hm h1 h2.
  induction h1 in m2, m, hm, σ2, h2 |- *.
  - destruct m2. 2: discriminate.
    cbn in hm. apply some_inj in hm. subst.
    inversion h2. subst.
    eexists. intuition reflexivity.
  - destruct m2 as [| [] m2]. 1,2: discriminate.
    cbn in hm. destruct lin_merge eqn:e. 2: discriminate.
    apply some_inj in hm. subst.
    inversion h2. subst.
    specialize IHh1 with (1 := e) (2 := X).
    destruct IHh1 as [σ' [e1 h]].
    cbn. rewrite e1.
    eexists. intuition eauto.
    constructor. assumption.
  - destruct m2 as [| b m2]. 1: discriminate.
    cbn in hm. destruct lin_merge eqn:e. 2: discriminate.
    apply some_inj in hm. subst.
    inversion h2.
    + subst.
      specialize IHh1 with (1 := e) (2 := X).
      destruct IHh1 as [σ' [e1 h]].
      cbn. rewrite e1.
      eexists. intuition eauto.
      constructor. assumption.
    + subst.
      specialize IHh1 with (1 := e) (2 := X).
      destruct IHh1 as [σ' [e1 h]].
      cbn. rewrite e1.
      eexists. intuition eauto.
      constructor. assumption.
Qed.

Lemma subs_complete_merge :
  forall σ1 σ2 σ θ,
    subs_merge σ1 σ2 = Some σ ->
    subs_complete σ1 θ ->
    subs_complete σ2 θ ->
    subs_complete σ θ.
Proof.
  intros σ1 σ2 σ θ me c1 c2.
  induction c1 in σ2, σ, me, c2 |- *.
  - destruct σ2. 2: discriminate.
    cbn in me. apply some_inj in me. subst. constructor.
  - destruct σ2 as [| [] σ2]. 1,2: discriminate.
    cbn in me. destruct subs_merge eqn:e. 2: discriminate.
    apply some_inj in me. subst.
    constructor. eapply IHc1.
    + eauto.
    + inversion c2. assumption.
  - destruct σ2 as [| o σ2]. 1: discriminate.
    cbn in me. destruct subs_merge eqn:e. 2: discriminate.
    apply some_inj in me. subst.
    inversion c2.
    + subst. constructor. eapply IHc1. all: eauto.
    + subst. constructor. eapply IHc1. all: eauto.
Qed.

Lemma match_pattern_complete :
  forall npat p m σ,
    pattern npat p ->
    pattern_mask npat p = Some m ->
    #|σ| = npat ->
    ∑ θ,
      masks m θ ×
      match_pattern npat p (subst0 σ p) = Some θ ×
      subs_complete θ σ.
Proof.
  intros npat p m σ hp hm eσ.
  induction hp
  as [n hn | ind n ui args ha ih]
  in m, hm |- *
  using pattern_all_rect.
  - unfold match_pattern. cbn.
    replace (n - 0) with n by lia.
    destruct nth_error eqn:e.
    2:{ apply nth_error_None in e. exfalso. lia. }
    rewrite lift0_id.
    unfold subs_init, subs_add.
    rewrite nth_error_subs_empty. 2: auto.
    cbn in hm. rewrite lin_set_eq in hm.
    unfold linear_mask_init in hm.
    rewrite -> nth_error_list_init in hm by auto.
    apply some_inj in hm. subst.
    eexists. intuition eauto.
    + apply masks_app.
      * apply masks_firstn. apply masks_linear_mask_init.
      * constructor. apply masks_skipn. apply masks_linear_mask_init.
    + unfold subs_empty. rewrite firstn_list_init. rewrite skipn_list_init.
      replace (min n #|σ|) with n by lia.
      apply subs_complete_spec. split.
      * rewrite app_length. cbn.
        rewrite 2!list_init_length. lia.
      * intros i u ei.
        eapply nth_error_app_dec in ei as [[hi ei] | [hi ei]].
        1:{
          rewrite list_init_length in hi.
          rewrite -> nth_error_list_init in ei by auto.
          discriminate.
        }
        rewrite list_init_length in ei. rewrite list_init_length in hi.
        case_eq (i - n).
        2:{
          intros k ek.
          rewrite ek in ei. cbn in ei.
          apply nth_error_Some_length in ei as l.
          rewrite list_init_length in l.
          rewrite -> nth_error_list_init in ei by auto.
          discriminate.
        }
        intros hh. assert (i = n) by lia. subst.
        rewrite hh in ei. clear hh hi.
        cbn in ei. inversion ei. subst.
        assumption.
  - eapply All_prod in ih. 2: exact ha.
    clear ha.
    induction ih
    as [| p args [hp ihp] _ ih]
    in m, hm |- *
    using All_rev_rect.
    + cbn in hm. apply some_inj in hm. subst.
      unfold mkApps. unfold match_pattern.
      unfold subst. unfold assert_eq.
      match goal with
      | |- context [ eqb ?x ?y ] =>
        destruct (eqb_spec x y)
      end.
      2:{ exfalso. auto. }
      cbn.
      eexists. intuition eauto.
      * apply masks_linear_mask_init.
      * apply subs_complete_subs_empty.
        reflexivity.
    + rewrite <- mkApps_nested in hm. cbn in hm.
      destruct pattern_mask eqn:e1. 2: discriminate.
      move hm at top.
      destruct pattern_mask eqn:e2. 2: discriminate.
      specialize ihp with (1 := eq_refl).
      specialize ih with (1 := eq_refl).
      destruct ihp as [θ1 [hm1 [mp1 c1]]].
      destruct ih as [θ2 [hm2 [mp2 c2]]].
      rewrite <- mkApps_nested. cbn.
      rewrite mp2. rewrite mp1.
      eapply masks_merge in hm. 2,3: eauto.
      destruct hm as [θ [sm hm]].
      eexists. intuition eauto.
      eapply subs_complete_merge. all: eauto.
Qed.

Fixpoint option_map2 {A B C}
  (f : A -> B -> option C) (l1 : list A) (l2 : list B) : option (list C) :=
  match l1, l2 with
  | [], [] => ret []
  | x :: l1, y :: l2 =>
      z <- f x y ;;
      l <- option_map2 f l1 l2 ;;
      ret (z :: l)
  | _, _ => None
  end.

Fixpoint match_prelhs npat k n l t :=
  match l with
  | [] =>
    match t with
    | tSymb k' n' ui =>
      assert_eq k k' ;;
      assert_eq n n' ;;
      ret (ui, subs_empty npat)
    | _ => None
    end

  | eApp p :: l =>
    match t with
    | tApp u v =>
      σ1 <- match_pattern npat p v ;;
      '(ui,σ2) <- match_prelhs npat k n l u ;;
      σ <- subs_merge σ1 σ2 ;;
      ret (ui, σ)
    | _ => None
    end

  | eCase ind p brs :: l =>
    match t with
    | tCase ind' p' c brs' =>
      assert_eq ind ind' ;;
      σp <- match_pattern npat p p' ;;
      σb <- option_map2 (fun br br' =>
              assert_eq br.1 br'.1 ;;
              match_pattern npat br.2 br'.2
            ) brs brs' ;;
      σb <- monad_fold_right subs_merge σb (subs_empty npat) ;;
      '(ui,σc) <- match_prelhs npat k n l c ;;
      σ1 <- subs_merge σp σb ;;
      σ2 <- subs_merge σ1 σc ;;
      ret (ui, σ2)
    | _ => None
    end

  | eProj p :: l =>
    match t with
    | tProj p' u =>
      assert_eq p p' ;;
      match_prelhs npat k n l u
    | _ => None
    end
  end.

Lemma match_prelhs_sound :
  forall npat k n ui l t σ,
    All (elim_pattern npat) l ->
    match_prelhs npat k n l t = Some (ui, σ) ->
    forall θ,
      subs_complete σ θ ->
      t = subst0 θ (fold_right (fun e t => mkElim t e) (tSymb k n ui) l).
Admitted.

Lemma match_prelhs_complete :
  forall npat k n ui l m σ,
    All (elim_pattern npat) l ->
    linear_mask npat l = Some m ->
    #|σ| = npat ->
    ∑ θ,
      masks m θ ×
      let t := fold_right (fun e t => mkElim t e) (tSymb k n ui) l in
      match_prelhs npat k n l (subst0 σ t) = Some (ui, θ) ×
      subs_complete θ σ.
Admitted.

Definition match_lhs npat k n l t :=
  '(ui,σ) <- match_prelhs npat k n (List.rev l) t ;;
  σ <- map_option_out σ ;;
  ret (ui, σ).

Lemma map_option_out_subs_complete :
  forall s s',
    map_option_out s = Some s' ->
    subs_complete s s'.
Proof.
  intros s s' e.
  induction s in s', e |- *.
  - cbn in e. apply some_inj in e. subst. constructor.
  - cbn in e. destruct a. 2: discriminate.
    destruct map_option_out eqn:e1. 2: discriminate.
    apply some_inj in e. subst.
    constructor. eapply IHs. reflexivity.
Qed.

Lemma match_lhs_sound :
  forall npat k n ui l t σ,
    All (elim_pattern npat) l ->
    match_lhs npat k n l t = Some (ui, σ) ->
    t = subst0 σ (mkElims (tSymb k n ui) l).
Proof.
  intros npat k n ui l t σ pl e.
  unfold match_lhs in e.
  destruct match_prelhs as [[? ?]|] eqn:e1. 2: discriminate.
  cbn in e. destruct map_option_out eqn:e2. 2: discriminate.
  inversion e. subst. clear e.
  apply map_option_out_subs_complete in e2 as hs.
  eapply match_prelhs_sound in e1. 3: eauto.
  - rewrite fold_left_rev_right in e1. assumption.
  - eapply All_rev. assumption.
Qed.

(* Lemma monad_map_rev :
  forall M {hM : Monad M} A B (f : A -> M B) l l',
    monad_map f l = ret l' ->
    monad_map f (List.rev l) = ret (List.rev l').
Proof.
  intros M hM A B f l l' e.
  induction l in l', e |- *.
  - cbn in *. *)

(* Lemma linear_mask_rev :
  forall npat l m,
    linear_mask npat l = Some m ->
    linear_mask npat (List.rev l) = Some m.
Proof.
  intros npat l m h.
  unfold linear_mask in *.
  induction *)

Lemma match_lhs_complete :
  forall npat k n ui l σ,
    All (elim_pattern npat) l ->
    linear npat l ->
    #|σ| = npat ->
    match_lhs npat k n l (subst0 σ (mkElims (tSymb k n ui) l)) = Some (ui, σ).
Proof.
  intros npat k n ui l σ pl ll eσ.
  unfold linear in ll.
  destruct linear_mask eqn:e1. 2: discriminate.
  unfold match_lhs.
  apply All_rev in pl.
  eapply match_prelhs_complete in pl. 3: eauto.
Admitted.

Lemma match_lhs_rename :
  forall npat k n ui l t σ r,
    All (elim_pattern npat) l ->
    match_lhs npat k n l t = Some (ui, σ) ->
    match_lhs npat k n l (rename r t) = Some (ui, map (rename r) σ).
Proof.
  intros npat k n ui l t σ r pl e.
  unfold match_lhs in e.
  destruct match_prelhs as [[? ?]|] eqn:e1. 2: discriminate.
  cbn in e. destruct map_option_out eqn:e2. 2: discriminate.
  inversion e. subst. clear e.
  unfold match_lhs.
  (* Need to do it on all previous things *)
Admitted.
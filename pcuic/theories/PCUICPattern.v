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

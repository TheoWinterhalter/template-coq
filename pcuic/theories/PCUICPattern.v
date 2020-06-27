(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils Universes BasicAst
  AstUtils UnivSubst EnvironmentTyping.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICSize.

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
Proof.
  intros npat k n ui l t σ h e θ hθ.
  induction h as [| ? l [] hl ih ] in t, σ, e, θ, hθ |- *.
  - cbn in *. destruct t. all: try discriminate.
    assert_eq e. subst. cbn in e.
    assert_eq e. subst. cbn in e.
    inversion e. subst. clear e.
    reflexivity.
  - cbn in *. destruct t. all: try discriminate.
    destruct match_pattern eqn:e1. 2: discriminate.
    destruct match_prelhs as [[] |] eqn:e2. 2: discriminate.
    destruct subs_merge eqn:e3. 2: discriminate.
    inversion e. subst. clear e.
    eapply subs_merge_complete in e3 as sc. 2: eassumption.
    destruct sc.
    eapply match_pattern_sound in e1. 2,3: eauto.
    eapply ih in e2. 2: eauto.
    subst. reflexivity.
  - cbn in *. destruct t. all: try discriminate.
    assert_eq e. subst. cbn in e.
    destruct match_pattern eqn:e1. 2: discriminate.
    destruct option_map2 eqn:e2. 2: discriminate.
    destruct monad_fold_right eqn:e3. 2: discriminate.
    destruct match_prelhs as [[] |] eqn:e4. 2: discriminate.
    destruct subs_merge eqn:e5. 2: discriminate.
    move e at top.
    destruct subs_merge eqn:e6. 2: discriminate.
    inversion e. subst. clear e.
    eapply subs_merge_complete in e6 as sc. 2: eassumption.
    destruct sc.
    eapply subs_merge_complete in e5 as sc. 2: eassumption.
    destruct sc as [? hl2].
    eapply match_pattern_sound in e1. 2,3: eauto.
    eapply ih in e4. 2: eauto.
    subst. f_equal.
    clear - a e2 e3 hl2.
    induction a as [| [] brs ? a ih] in brs0, l1, e2, l2, e3, θ, hl2 |- *.
    + destruct brs0. 2: discriminate.
      cbn in e2. apply some_inj in e2. subst.
      cbn in e3. apply some_inj in e3. subst.
      reflexivity.
    + destruct brs0 as [| [] brs0]. 1: discriminate.
      cbn in *.
      assert_eq e2. subst. cbn in e2.
      destruct match_pattern eqn:e1. 2: discriminate.
      destruct option_map2 eqn:e4. 2: discriminate.
      apply some_inj in e2. subst.
      cbn in e3. destruct monad_fold_right eqn:e5. 2: discriminate.
      eapply subs_merge_complete in e3 as sc. 2: eauto.
      destruct sc.
      eapply ih in e4. 2-3: eauto.
      eapply match_pattern_sound in e1. 2-3: eauto.
      subst.
      reflexivity.
  - cbn in *. destruct t. all: try discriminate.
    assert_eq e. subst. cbn in e.
    eapply ih in e. 2: eauto.
    subst. reflexivity.
Qed.

Lemma assert_eq_refl :
  forall {A} `{ReflectEq A} (x : A),
    assert_eq x x = Some ().
Proof.
  intros A H x.
  unfold assert_eq. destruct (eqb_spec x x).
  - reflexivity.
  - exfalso. auto.
Qed.

Lemma lin_merge_sym :
  forall m1 m2 m,
    lin_merge m1 m2 = Some m ->
    lin_merge m2 m1 = Some m.
Proof.
  intros m1 m2 m e.
  induction m1 as [| [] m1 ih] in m2, m, e |- *.
  - destruct m2. 2: discriminate.
    assumption.
  - destruct m2 as [| [] m2]. 1,2: discriminate.
    cbn in e. destruct lin_merge eqn:e1. 2: discriminate.
    apply some_inj in e. subst.
    cbn. erewrite -> ih by eassumption.
    reflexivity.
  - destruct m2 as [| [] m2]. 1: discriminate.
    + cbn in e. destruct lin_merge eqn:e1. 2: discriminate.
      apply some_inj in e. subst.
      cbn. erewrite -> ih by eassumption.
      reflexivity.
    + cbn in e. destruct lin_merge eqn:e1. 2: discriminate.
      apply some_inj in e. subst.
      cbn. erewrite -> ih by eassumption.
      reflexivity.
Qed.

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
Proof.
  intros npat k n ui l m σ pl ll σl.
  induction pl as [| [] l pe pl ih] in m, σ, ll, σl |- *.
  - cbn. rewrite !assert_eq_refl.
    cbn in ll. apply some_inj in ll. subst.
    eexists. intuition eauto.
    + apply masks_linear_mask_init.
    + apply subs_complete_subs_empty. reflexivity.
  - cbn. cbn in ll.
    destruct pattern_mask eqn:e1. 2: discriminate.
    destruct monad_map eqn:e2. 2: discriminate.
    cbn in ll. destruct monad_fold_right eqn:e3. 2: discriminate.
    cbn in ih. rewrite e2 in ih.
    specialize ih with (1 := e3).
    inversion pe. subst.
    eapply match_pattern_complete in e1. 2,3: eauto.
    destruct e1 as [θ1 [hθ1 [e1 hc1]]].
    rewrite e1.
    specialize ih with (1 := eq_refl).
    destruct ih as [θ2 [hθ2 [eq2 hc2]]].
    rewrite eq2.
    eapply lin_merge_sym in ll.
    eapply masks_merge in ll. 3,2: eauto.
    destruct ll as [θ [hθ hm]].
    rewrite hθ. eexists. intuition eauto.
    eapply subs_complete_merge. all: eauto.
  - cbn. rewrite !assert_eq_refl.
    cbn in ll.
    destruct pattern_mask eqn:e1. 2: discriminate.
    destruct monad_map eqn:e2. 2: discriminate.
    destruct monad_fold_right eqn:e3. 2: discriminate.
    destruct lin_merge eqn:e4. 2: discriminate.
    move ll at top.
    destruct monad_map eqn:e5. 2: discriminate.
    cbn in ll. destruct monad_fold_right eqn:e6. 2: discriminate.
    cbn in ih. rewrite e5 in ih. rewrite e6 in ih.
    specialize ih with (1 := eq_refl).
    inversion pe. subst.
    specialize ih with (1 := eq_refl).
    eapply match_pattern_complete in e1. 2,3: eauto.
    destruct e1 as [θ1 [hθ1 [e1 hc1]]].
    rewrite e1.
    destruct ih as [θ2 [hθ2 [eq2 hc2]]].
    rewrite eq2.
    match goal with
    | |- context [ option_map2 ?f ?x ?y ] =>
      assert (e7 :
        ∑ l ρ,
          option_map2 f x y = Some l ×
          monad_fold_right subs_merge l (subs_empty #|σ|) = Some ρ ×
          masks l2 ρ ×
          subs_complete ρ σ
      )
    end.
    { clear - e2 e3 X0. induction X0 in l1, e2, l2, e3 |- *.
      - cbn in e2. apply some_inj in e2. subst.
        cbn in e3. apply some_inj in e3. subst.
        cbn. eexists _,_. intuition eauto.
        + eapply masks_linear_mask_init.
        + eapply subs_complete_subs_empty. reflexivity.
      - cbn in e2. destruct pattern_mask eqn:e1. 2: discriminate.
        destruct monad_map eqn:e4. 2: discriminate.
        apply some_inj in e2. subst.
        cbn in e3.
        destruct monad_fold_right eqn:e5. 2: discriminate.
        specialize IHX0 with (1 := eq_refl).
        specialize IHX0 with (1 := e5).
        cbn. rewrite !assert_eq_refl.
        eapply match_pattern_complete in e1. 2,3: eauto.
        destruct e1 as [θ1 [hθ1 [e1 hc1]]].
        rewrite e1.
        destruct IHX0 as [l' [ρ [e [e6 [? ?]]]]].
        rewrite e.
        eapply masks_merge in e3. 3,2: eauto.
        destruct e3 as [θ [hθ hm]].
        eexists _,_. split. 1: reflexivity.
        split. 2: split.
        + cbn. rewrite e6. eassumption.
        + assumption.
        + eapply subs_complete_merge. all: eauto.
    }
    destruct e7 as [l' [ρ [e [e7 [? ?]]]]].
    rewrite e. rewrite e7.
    eapply masks_merge in e4. 3,2: eauto.
    destruct e4 as [θ [hθ hm]].
    rewrite hθ.
    eapply lin_merge_sym in ll.
    eapply masks_merge in ll. 3,2: eauto.
    destruct ll as [θ' [hθ' hm']].
    rewrite hθ'.
    eexists. intuition eauto.
    eapply subs_complete_merge. all: eauto.
    eapply subs_complete_merge. all: eauto.
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

Lemma option_monad_map_app :
  forall A B (f : A -> option B) l l',
    monad_map f (l ++ l') = (
      x <- monad_map f l ;;
      y <- monad_map f l' ;;
      ret (x ++ y)
    ).
Proof.
  intros A B f l l'.
  induction l in l' |- *.
  - cbn. destruct monad_map. all: reflexivity.
  - cbn. destruct f. 2: reflexivity.
    rewrite IHl. cbn. destruct monad_map. 2: reflexivity.
    destruct monad_map. 2: reflexivity.
    reflexivity.
Qed.

Lemma option_monad_map_rev :
  forall A B (f : A -> option B) l l',
    monad_map f l = Some l' ->
    monad_map f (List.rev l) = Some (List.rev l').
Proof.
  intros A B f l l' e.
  induction l in l', e |- *.
  - cbn in *. apply some_inj in e. subst. reflexivity.
  - cbn in *. destruct (f _) eqn:e1. 2: discriminate.
    destruct monad_map eqn:e2. 2: discriminate.
    apply some_inj in e. subst.
    specialize IHl with (1 := eq_refl).
    rewrite option_monad_map_app. rewrite IHl.
    cbn. rewrite e1. reflexivity.
Qed.

Lemma option_monad_fold_right_app :
  forall A B (f : A -> B -> option A) l l' a,
    monad_fold_right f (l ++ l') a = (
      x <- monad_fold_right f l' a ;;
      monad_fold_right f l x
    ).
Proof.
  intros A B f l l' a.
  induction l in l', a |- *.
  - cbn. destruct monad_fold_right. all: reflexivity.
  - cbn. rewrite IHl. cbn. destruct monad_fold_right. 2: reflexivity.
    reflexivity.
Qed.

Lemma lin_merge_linear_mask_init_eq :
  forall npat m1 m2,
    lin_merge (linear_mask_init npat) m1 = Some m2 ->
    m1 = m2.
Proof.
  intros npat m1 m2 h.
  induction npat in m1, m2, h |- *.
  - cbn in h. destruct m1. 2: discriminate.
    apply some_inj in h. assumption.
  - destruct m1. 1: discriminate.
    cbn in h. destruct lin_merge eqn:e. 2: discriminate.
    apply some_inj in h. subst.
    eapply IHnpat in e. subst. reflexivity.
Qed.

Lemma lin_merge_assoc :
  forall a b c d e,
    lin_merge a b = Some c ->
    lin_merge c d = Some e ->
    ∑ f,
      lin_merge a d = Some f ×
      lin_merge f b = Some e.
Proof.
  intros a b c d e hc he.
  induction a as [| [] a ih] in b, c, d, e, hc, he |- *.
  - destruct b. 2: discriminate.
    cbn in hc. apply some_inj in hc. subst.
    destruct d. 2: discriminate.
    cbn in he. apply some_inj in he. subst.
    exists []. intuition reflexivity.
  - destruct b as [| [] b]. 1,2: discriminate.
    cbn in hc. destruct (lin_merge a b) as [g|] eqn:hg. 2: discriminate.
    apply some_inj in hc. subst.
    destruct d as [| [] d]. 1,2: discriminate.
    cbn in he. destruct (lin_merge g d) as [h|] eqn:hh. 2: discriminate.
    apply some_inj in he. subst.
    specialize ih with (1 := hg) (2 := hh).
    destruct ih as [f [h1 h2]].
    cbn. rewrite h1.
    eexists. intuition eauto.
    cbn. rewrite h2. reflexivity.
  - destruct b as [| x b]. 1: discriminate.
    cbn in hc. destruct (lin_merge a b) as [g|] eqn:hg. 2: discriminate.
    apply some_inj in hc. subst.
    destruct x.
    + destruct d as [| [] d]. 1,2: discriminate.
      cbn in he. destruct (lin_merge g d) as [h|] eqn:hh. 2: discriminate.
      apply some_inj in he. subst.
      specialize ih with (1 := hg) (2 := hh).
      destruct ih as [f [h1 h2]].
      cbn. rewrite h1.
      eexists. intuition eauto.
      cbn. rewrite h2. reflexivity.
    + destruct d as [| x d]. 1: discriminate.
      cbn in he. destruct (lin_merge g d) as [h|] eqn:hh. 2: discriminate.
      apply some_inj in he. subst.
      specialize ih with (1 := hg) (2 := hh).
      destruct ih as [f [h1 h2]].
      cbn. rewrite h1.
      eexists. intuition eauto.
      destruct x.
      * cbn. rewrite h2. reflexivity.
      * cbn. rewrite h2. reflexivity.
Qed.

Lemma lin_merge_app :
  forall npat l1 l2 m1 m2 m,
    monad_fold_right lin_merge l1 (linear_mask_init npat) = Some m1 ->
    monad_fold_right lin_merge l2 (linear_mask_init npat) = Some m2 ->
    lin_merge m1 m2 = Some m ->
    monad_fold_right lin_merge (l1 ++ l2) (linear_mask_init npat) = Some m.
Proof.
  intros npat l1 l2 m1 m2 m h1 h2 hm.
  induction l1 in l2, m1, m2, m, h1, h2, hm |- *.
  - cbn in h1. apply some_inj in h1. subst.
    cbn. rewrite h2. f_equal.
    apply lin_merge_linear_mask_init_eq in hm. auto.
  - cbn in *. destruct monad_fold_right eqn:e. 2: discriminate.
    pose proof (lin_merge_assoc _ _ _ _ _ h1 hm) as h3.
    destruct h3 as [m' [h3 h4]].
    eapply IHl1 in h2. 2,3: eauto.
    rewrite h2. auto.
Qed.

Lemma lin_merge_length :
  forall m1 m2 m,
    lin_merge m1 m2 = Some m ->
    #|m| = #|m1| /\ #|m| = #|m2|.
Proof.
  intros m1 m2 m hm.
  induction m1 as [| [] m1 ih] in m2, m, hm |- *.
  - destruct m2. 2: discriminate.
    cbn in hm. apply some_inj in hm. subst.
    auto.
  - destruct m2 as [| [] m2]. 1,2: discriminate.
    cbn in hm. destruct lin_merge eqn:e. 2: discriminate.
    apply some_inj in hm. subst.
    apply ih in e. cbn. intuition eauto.
  - cbn in hm. destruct m2. 1: discriminate.
    destruct lin_merge eqn:e. 2: discriminate.
    apply some_inj in hm. subst.
    apply ih in e. cbn. intuition eauto.
Qed.

Lemma fold_lin_merge_length :
  forall npat l m,
    monad_fold_right lin_merge l (linear_mask_init npat) = Some m ->
    #|m| = npat.
Proof.
  intros npat l m h.
  induction l in npat, m, h |- *.
  - cbn in h. apply some_inj in h. subst.
    unfold linear_mask_init. apply list_init_length.
  - cbn in h. destruct monad_fold_right eqn:e. 2: discriminate.
    eapply IHl in e. eapply lin_merge_length in h as [? ?].
    lia.
Qed.

Lemma lin_merge_linear_mask_init :
    forall m,
      lin_merge (linear_mask_init #|m|) m = Some m.
  Proof.
    intros m.
    unfold linear_mask_init.
    induction m as [| [] m ih].
    - reflexivity.
    - cbn. rewrite ih. reflexivity.
    - cbn. rewrite ih. reflexivity.
  Qed.

Lemma lin_merge_rev :
  forall npat l m,
    monad_fold_right lin_merge l (linear_mask_init npat) = Some m ->
    monad_fold_right lin_merge (List.rev l) (linear_mask_init npat) = Some m.
Proof.
  intros npat l m h.
  induction l in npat, m, h |- *.
  - cbn in h. apply some_inj in h. subst.
    cbn. reflexivity.
  - cbn in h. destruct monad_fold_right eqn:e. 2: discriminate.
    eapply IHl in e.
    cbn. eapply lin_merge_app. 1,3: eauto.
    cbn. eapply lin_merge_length in h as [? ?].
    eapply fold_lin_merge_length in e.
    replace npat with #|a| by lia.
    apply lin_merge_linear_mask_init.
Qed.

Lemma list_ext :
  forall {A} (m1 m2 : list A),
    (forall n, nth_error m1 n = nth_error m2 n) ->
    m1 = m2.
Proof.
  intros A m1 m2 h.
  induction m1 in m2, h |- *.
  - destruct m2. 1: reflexivity.
    exfalso. specialize (h 0). cbn in h. discriminate.
  - destruct m2.
    1:{ specialize (h 0). cbn in h. discriminate. }
    f_equal.
    + specialize (h 0). cbn in h. apply some_inj in h. auto.
    + eapply IHm1. intros n.
      apply (h (S n)).
Qed.

Lemma linear_mask_rev :
  forall npat l m,
    linear_mask npat l = Some m ->
    linear_mask npat (List.rev l) = Some m.
Proof.
  intros npat l m h.
  unfold linear_mask in *.
  destruct monad_map as [l1|] eqn:e1. 2: discriminate.
  eapply option_monad_map_rev in e1.
  cbn in h.
  destruct monad_map. 2: discriminate.
  apply some_inj in e1. subst.
  cbn.
  apply lin_merge_rev. assumption.
Qed.

Lemma all_mask_map_option_out :
  forall σ θ m,
    forallb (fun x => x) m ->
    masks m θ ->
    subs_complete θ σ ->
    map_option_out θ = Some σ.
Proof.
  intros σ θ m hm hθ h.
  induction h in m, hm, hθ |- *.
  - cbn. reflexivity.
  - cbn. inversion hθ. subst.
    inversion hm.
    erewrite IHh. all: eauto.
  - inversion hθ. subst. inversion hm.
Qed.

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
  2:{
    eapply linear_mask_rev. eassumption.
  }
  destruct pl as [θ [hθ [e ?]]].
  rewrite fold_left_rev_right in e. unfold mkElims.
  rewrite e.
  cbn. eapply all_mask_map_option_out in ll. 2,3: eauto.
  rewrite ll. reflexivity.
Qed.

(* TODO MOVE *)
Lemma map_list_init :
  forall {A} (x : A) n {B} (f : A -> B),
    map f (list_init x n) = list_init (f x) n.
Proof.
  intros A x n B f.
  induction n.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.

Lemma subs_merge_map :
  forall σ θ ρ f,
    subs_merge σ θ = Some ρ ->
    subs_merge (map (option_map f) σ) (map (option_map f) θ) =
    Some (map (option_map f) ρ).
Proof.
  intros σ θ ρ f e.
  induction σ as [| [] σ ih] in θ, ρ, f, e |- *.
  - destruct θ. 2: discriminate.
    cbn in e. apply some_inj in e. subst.
    cbn. reflexivity.
  - destruct θ as [| [] θ]. 1,2: discriminate.
    cbn in e. destruct subs_merge eqn:e1. 2: discriminate.
    apply some_inj in e. subst.
    eapply ih in e1.
    cbn. rewrite e1. reflexivity.
  - destruct θ as [| x θ]. 1: discriminate.
    cbn in e. destruct subs_merge eqn:e1. 2: discriminate.
    apply some_inj in e. subst.
    eapply ih in e1.
    cbn. rewrite e1. reflexivity.
Qed.

Lemma match_pattern_rename :
  forall npat p t σ r,
    pattern npat p ->
    match_pattern npat p t = Some σ ->
    match_pattern npat p (rename r t) = Some (map (option_map (rename r)) σ).
Proof.
  intros npat p t σ r hp e.
  induction hp
  as [n hn | ind n ui args ha ih]
  in t, σ, e |- *
  using pattern_all_rect.
  - cbn in *.
    unfold subs_init in *. unfold subs_add in *.
    destruct nth_error as [[]|]. 1,3: discriminate.
    apply some_inj in e. subst. f_equal.
    rewrite map_app. cbn.
    rewrite <- firstn_map. rewrite map_skipn.
    unfold subs_empty. rewrite !map_list_init.
    cbn. reflexivity.
  - eapply All_prod in ih. 2: exact ha.
    clear ha.
    induction ih
    as [| p args [hp ihp] _ ih]
    in t, σ, e |- *
    using All_rev_rect.
    + unfold mkApps in *.
      unfold match_pattern in *.
      unfold assert_eq.
      assert_eq e. subst.
      cbn in e. inversion e. subst.
      cbn [ rename ].
      destruct (eqb_spec (tConstruct ind n ui) (tConstruct ind n ui)).
      2:{ exfalso. auto. }
      cbn. unfold subs_empty. rewrite map_list_init. reflexivity.
    + rewrite <- mkApps_nested. cbn.
      rewrite <- mkApps_nested in e. cbn in e.
      destruct t. all: try discriminate.
      destruct match_pattern eqn:e1. 2: discriminate.
      move e at top.
      destruct match_pattern eqn:e2. 2: discriminate.
      cbn. eapply ih in e1.
      eapply ihp in e2.
      rewrite e1. rewrite e2.
      eapply subs_merge_map. assumption.
Qed.

Lemma match_prelhs_rename :
  forall npat k n l t ui σ r,
    All (elim_pattern npat) l ->
    match_prelhs npat k n l t = Some (ui, σ) ->
    match_prelhs npat k n l (rename r t) =
    Some (ui, map (option_map (rename r)) σ).
Proof.
  intros npat k n l t ui σ r hl e.
  induction hl as [| ? l [] hl ih ] in t, σ, e, r |- *.
  - cbn in *. destruct t. all: try discriminate.
    cbn. unfold assert_eq.
    assert_eq e. subst. cbn in e.
    assert_eq e. subst. cbn in e.
    inversion e. subst. clear e.
    cbn. unfold subs_empty. rewrite map_list_init.
    reflexivity.
  - cbn in *. destruct t. all: try discriminate.
    cbn. destruct match_pattern eqn:e1. 2: discriminate.
    destruct match_prelhs as [[]|] eqn:e2. 2: discriminate.
    destruct subs_merge eqn:e3. 2: discriminate.
    inversion e. subst. clear e.
    eapply match_pattern_rename in e1. 2: auto.
    eapply ih in e2.
    rewrite e1. rewrite e2. erewrite subs_merge_map. 2: eassumption.
    reflexivity.
  - cbn in *. destruct t. all: try discriminate.
    cbn. unfold assert_eq.
    assert_eq e. subst. cbn in e.
    destruct match_pattern eqn:e1. 2: discriminate.
    destruct option_map2 eqn:e2. 2: discriminate.
    destruct monad_fold_right eqn:e3. 2: discriminate.
    destruct match_prelhs as [[]|] eqn:e4. 2: discriminate.
    destruct subs_merge eqn:e5. 2: discriminate.
    move e at top.
    destruct subs_merge eqn:e6. 2: discriminate.
    inversion e. subst. clear e.
    cbn. eapply match_pattern_rename in e1. 2: auto.
    eapply ih in e4.
    rewrite e1. rewrite e4.
    match goal with
    | |- context [ option_map2 ?f ?b1 ?b2 ] =>
      assert (e7 :
        ∑ l,
          option_map2 f b1 b2 = Some l ×
          monad_fold_right subs_merge l (subs_empty npat) =
          Some (map (option_map (rename r)) l2)
      )
    end.
    { clear - a e2 e3.
      induction a as [| [] ] in brs0, l1, e2, l2, e3 |- *.
      - destruct brs0. 2: discriminate.
        cbn in e2. apply some_inj in e2. subst.
        cbn in e3. apply some_inj in e3. subst.
        cbn. exists []. intuition auto.
        unfold subs_empty. rewrite map_list_init. reflexivity.
      - destruct brs0 as [| []]. 1: discriminate.
        cbn in e2.
        assert_eq e2. subst. cbn in e2.
        destruct match_pattern eqn:e4. 2: discriminate.
        destruct option_map2 eqn:e5. 2: discriminate.
        apply some_inj in e2. subst.
        cbn in e3. destruct monad_fold_right eqn:e1. 2: discriminate.
        eapply IHa in e5. 2: eauto.
        destruct e5 as [ll [e5 e2]].
        cbn. change (n0 =? n0) with (eqb n0 n0).
        destruct (eqb_spec n0 n0). 2:{ exfalso. auto. }
        cbn.
        eapply match_pattern_rename in e4. 2: auto.
        rewrite e4.
        rewrite e5.
        eexists. intuition eauto.
        cbn. rewrite e2.
        eapply subs_merge_map. auto.
    }
    destruct e7 as [? [e7 e8]].
    rewrite e7. rewrite e8.
    erewrite subs_merge_map. 2: eauto.
    erewrite subs_merge_map. 2: eauto.
    reflexivity.
  - cbn in *. destruct t. all: try discriminate.
    cbn. unfold assert_eq. assert_eq e.
    cbn in e. subst. cbn.
    eapply ih. assumption.
Qed.

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
  eapply match_prelhs_rename in e1.
  2:{ eapply All_rev. auto. }
  rewrite e1. cbn.
  rewrite map_option_out_map_option_map. rewrite e2.
  cbn. reflexivity.
Qed.

Definition symb_discr t :=
  match t with
  | tSymb k n ui => False
  | _ => True
  end.

Inductive symb_view : term -> Type :=
| is_symb k n ui : symb_view (tSymb k n ui)
| is_not_symb t : symb_discr t -> symb_view t.

Equations symb_viewc (t : term) : symb_view t :=
  symb_viewc (tSymb k n ui) := is_symb k n ui ;
  symb_viewc t := is_not_symb t I.

Lemma subs_merge_map_none :
  forall l1 l2 f,
    subs_merge l1 l2 = None ->
    subs_merge (map (option_map f) l1) (map (option_map f) l2) = None.
Proof.
  intros l1 l2 f e.
  induction l1 as [| [] l1 ih ] in l2, e |- *.
  - destruct l2. 1: discriminate.
    cbn. reflexivity.
  - destruct l2 as [| [] l2]. 1,2: auto.
    cbn in *. destruct subs_merge eqn:e1. 1: discriminate.
    eapply ih in e1. rewrite e1. reflexivity.
  - destruct l2 as [| x l2]. 1: auto.
    cbn in *. destruct subs_merge eqn:e1. 1: discriminate.
    eapply ih in e1. rewrite e1. reflexivity.
Qed.

Lemma match_pattern_rename_None :
  forall npat p t r,
    pattern npat p ->
    match_pattern npat p t = None ->
    match_pattern npat p (rename r t) = None.
Proof.
  intros npat p t r hp e.
  induction hp
  as [n hn | ind n ui args ha ih]
  in t, e |- *
  using pattern_all_rect.
  - cbn in *. unfold subs_init in *. unfold subs_add in *.
    destruct nth_error as [[]|]. 1,3: auto.
    discriminate.
  - eapply All_prod in ih. 2: exact ha.
    clear ha.
    induction ih
    as [| p args [hp ihp] hargs ih]
    in t, e |- *
    using All_rev_rect.
    + unfold mkApps in *.
      unfold match_pattern in *.
      unfold assert_eq in *.
      destruct t. all: auto.
    + rewrite <- mkApps_nested. cbn.
      rewrite <- mkApps_nested in e. cbn in e.
      destruct t. all: auto.
      cbn.
      destruct match_pattern eqn:e1.
      2:{
        eapply ih in e1. rewrite e1. reflexivity.
      }
      move e at top.
      eapply match_pattern_rename in e1.
      2:{
        constructor. eapply All_impl. 1: eauto.
        cbn. intros. intuition auto.
      }
      rewrite e1.
      destruct match_pattern eqn:e2.
      2:{
        eapply ihp in e2. rewrite e2. reflexivity.
      }
      eapply match_pattern_rename in e2. 2: auto.
      rewrite e2.
      eapply subs_merge_map_none. assumption.
Qed.

Lemma match_prelhs_rename_None :
  forall npat k n l t r,
    All (elim_pattern npat) l ->
    match_prelhs npat k n l t = None ->
    match_prelhs npat k n l (rename r t) = None.
Proof.
  intros npat k n l t r hl e.
  induction hl as [| ? l [] hl ih ] in t, e, r |- *.
  - cbn in e. destruct (symb_viewc t) as [| t h].
    2:{
      destruct t. all: cbn in h. all: auto.
    }
    cbn.
    unfold assert_eq in *.
    destruct (eqb_spec k k0). 2: auto.
    cbn - [eqb] in *.
    destruct (eqb_spec n n0). 2: auto.
    cbn in *. discriminate.
  - cbn in *. destruct t. all: auto.
    cbn. destruct match_pattern eqn:e1.
    2:{
      eapply match_pattern_rename_None in e1. 2: auto.
      rewrite e1. reflexivity.
    }
    eapply match_pattern_rename in e1. 2: auto.
    rewrite e1.
    destruct match_prelhs as [[]|] eqn:e2.
    2:{
      eapply ih in e2. rewrite e2. reflexivity.
    }
    eapply match_prelhs_rename in e2. 2: auto.
    rewrite e2.
    destruct subs_merge eqn:e3.
    2:{
      eapply subs_merge_map_none in e3.
      rewrite e3. reflexivity.
    }
    discriminate.
  - cbn in *. destruct t. all: auto.
    cbn. unfold assert_eq in *.
    destruct (eqb_spec indn indn0). 2: auto.
    cbn in *. subst.
    destruct match_pattern eqn:e1.
    2:{
      eapply match_pattern_rename_None in e1. 2: auto.
      rewrite e1. reflexivity.
    }
    eapply match_pattern_rename in e1. 2: auto.
    rewrite e1.
    destruct option_map2 eqn:e2.
    2:{
      match goal with
      | |- context [ option_map2 ?f ?b1 ?b2 ] =>
        assert (e3 :
          option_map2 f b1 b2 = None
        )
      end.
      { clear - a e2.
        induction a as [| [] ] in brs0, e2 |- *.
        - destruct brs0. 2: auto.
          cbn in e2. discriminate.
        - destruct brs0 as [| []]. 1: auto.
          cbn in *.
          change (n =? n0) with (eqb n n0) in *.
          destruct (eqb_spec n n0). 2: auto.
          cbn in *. subst.
          destruct match_pattern eqn:e1.
          2:{
            eapply match_pattern_rename_None in e1. 2: auto.
            rewrite e1. reflexivity.
          }
          eapply match_pattern_rename in e1. 2: auto.
          rewrite e1.
          destruct option_map2 eqn:e3.
          2:{
            eapply IHa in e3. rewrite e3. reflexivity.
          }
          discriminate.
      }
      rewrite e3. reflexivity.
    }
    match goal with
    | |- context [ option_map2 ?f ?b1 ?b2 ] =>
      assert (e7 :
          option_map2 f b1 b2 = Some (map (map (option_map (rename r))) l1)
      )
    end.
    { clear - a e2.
      induction a as [| [] ] in brs0, l1, e2 |- *.
      - destruct brs0. 2: discriminate.
        cbn in e2. apply some_inj in e2. subst.
        cbn. reflexivity.
      - destruct brs0 as [| []]. 1: discriminate.
        cbn in *.
        change (n =? n0) with (eqb n n0) in *.
        destruct (eqb_spec n n0). 2: discriminate.
        subst. cbn in *.
        destruct match_pattern eqn:e4. 2: discriminate.
        destruct option_map2 eqn:e5. 2: discriminate.
        apply some_inj in e2. subst.
        eapply IHa in e5.
        eapply match_pattern_rename in e4. 2: auto.
        rewrite e4.
        rewrite e5. cbn. reflexivity.
    }
    rewrite e7.
    destruct monad_fold_right eqn:e3.
    2:{
      match goal with
      | |- context [ monad_fold_right ?f ?x ?y ] =>
        assert (e8 : monad_fold_right f x y = None)
      end.
      { clear - e3. induction l1.
        - cbn in e3. discriminate.
        - cbn in *. destruct monad_fold_right eqn:e1.
          2:{
            specialize IHl1 with (1 := eq_refl).
            rewrite IHl1. reflexivity.
          }
          lazymatch goal with
          | h : monad_fold_right _ _ _ = Some ?l
            |- context [ monad_fold_right ?f ?x ?y ] =>
            assert (e2 :
              monad_fold_right f x y =
              Some (map (option_map (rename r)) l)
            )
          end.
          { clear - e1. induction l1 in l, e1 |- *.
            - cbn in e1. apply some_inj in e1. subst.
              cbn. unfold subs_empty. rewrite map_list_init. reflexivity.
            - cbn in *. destruct monad_fold_right eqn:e2. 2: discriminate.
              specialize IHl1 with (1 := eq_refl). rewrite IHl1.
              eapply subs_merge_map. auto.
          }
          rewrite e2. eapply subs_merge_map_none. auto.
      }
      rewrite e8. reflexivity.
    }
    lazymatch goal with
    | h : monad_fold_right _ _ _ = Some ?l
      |- context [ monad_fold_right ?f ?x ?y ] =>
      assert (e9 :
        monad_fold_right f x y =
        Some (map (option_map (rename r)) l)
      )
    end.
    { clear - e3. induction l1 in l2, e3 |- *.
      - cbn in e3. apply some_inj in e3. subst.
        cbn. unfold subs_empty. rewrite map_list_init. reflexivity.
      - cbn in *. destruct monad_fold_right eqn:e2. 2: discriminate.
        specialize IHl1 with (1 := eq_refl). rewrite IHl1.
        eapply subs_merge_map. auto.
    }
    rewrite e9.
    destruct match_prelhs as [[]|] eqn:e4.
    2:{
      eapply ih in e4. rewrite e4. reflexivity.
    }
    eapply match_prelhs_rename in e4. 2: auto.
    rewrite e4.
    destruct subs_merge eqn:e5.
    2:{
      eapply subs_merge_map_none in e5. rewrite e5. reflexivity.
    }
    eapply subs_merge_map in e5. rewrite e5.
    move e at top.
    destruct subs_merge eqn:e6.
    2:{
      eapply subs_merge_map_none in e6. rewrite e6. reflexivity.
    }
    eapply subs_merge_map in e6. rewrite e6.
    discriminate.
  - cbn in *. destruct t. all: auto.
    cbn. unfold assert_eq in *. destruct (eqb_spec p p0). 2: auto.
    cbn in *. eapply ih. auto.
Qed.

Lemma match_lhs_rename_None :
  forall npat k n l t r,
    All (elim_pattern npat) l ->
    match_lhs npat k n l t = None ->
    match_lhs npat k n l (rename r t) = None.
Proof.
  intros npat k n l t r pl e.
  unfold match_lhs in *.
  destruct match_prelhs as [[? ?]|] eqn:e1.
  2:{
    eapply match_prelhs_rename_None in e1.
    2:{ apply All_rev. auto. }
    rewrite e1. reflexivity.
  }
  eapply match_prelhs_rename in e1.
  2:{ apply All_rev. auto. }
  rewrite e1.
  cbn in *.
  rewrite map_option_out_map_option_map.
  destruct map_option_out eqn:e2. 1: discriminate.
  cbn. reflexivity.
Qed.

Lemma subs_merge_length_r :
  forall σ1 σ2 σ,
    subs_merge σ1 σ2 = Some σ ->
    #|σ2| = #|σ|.
Proof.
  intros σ1 σ2 σ e.
  induction σ1 as [| [] σ1 ih] in σ2, σ, e |- *.
  - destruct σ2.
    + cbn in e. apply some_inj in e. subst. reflexivity.
    + cbn in *. discriminate.
  - destruct σ2 as [| [] σ2].
    + cbn in e. discriminate.
    + cbn in e. discriminate.
    + cbn in *. destruct subs_merge eqn:e1. 2: discriminate.
      apply some_inj in e. subst. cbn.
      eapply ih in e1. auto.
  - destruct σ2 as [| [] σ2].
    + cbn in e. discriminate.
    + cbn in *. destruct subs_merge eqn:e1. 2: discriminate.
      apply some_inj in e. subst. cbn.
      eapply ih in e1. auto.
    + cbn in e. destruct subs_merge eqn:e1. 2: discriminate.
      apply some_inj in e. subst. cbn.
      eapply ih in e1. auto.
Qed.

Lemma match_prelhs_subst_length :
  forall npat k n l t ui σ,
    match_prelhs npat k n l t = Some (ui, σ) ->
    #|σ| = npat.
Proof.
  intros npat k n l t ui σ e.
  induction l as [| a l ih] in t, ui, σ, e |- *.
  - cbn in e. destruct t. all: try discriminate.
    destruct assert_eq. 2: discriminate.
    destruct assert_eq. 2: discriminate.
    inversion e.
    apply subs_empty_length.
  - cbn in e. destruct a.
    + destruct t. all: try discriminate.
      destruct match_pattern. 2: discriminate.
      destruct match_prelhs as [[? ?]|] eqn:e1. 2: discriminate.
      destruct subs_merge eqn:e2. 2: discriminate.
      inversion e. subst. clear e.
      eapply ih in e1. subst.
      eapply subs_merge_length_r in e2. auto.
    + destruct t. all: try discriminate.
      destruct assert_eq. 2: discriminate.
      destruct match_pattern. 2: discriminate.
      destruct option_map2. 2: discriminate.
      destruct monad_fold_right eqn:e1. 2: discriminate.
      destruct match_prelhs as [[? ?]|] eqn:e2. 2: discriminate.
      destruct subs_merge as [θ|] eqn:e3. 2: discriminate.
      destruct (subs_merge θ _) eqn:e4. 2: discriminate.
      inversion e. subst. clear e.
      eapply ih in e2. subst.
      eapply subs_merge_length_r in e4. auto.
    + destruct t. all: try discriminate.
      destruct assert_eq. 2: discriminate.
      eapply ih in e. auto.
Qed.

Lemma match_lhs_subst_length :
  forall npat k n l t ui σ,
    match_lhs npat k n l t = Some (ui, σ) ->
    #|σ| = npat.
Proof.
  intros npat k n l t ui σ e.
  unfold match_lhs in e.
  destruct match_prelhs as [[? ?]|] eqn:e1. 2: discriminate.
  cbn in e. destruct map_option_out eqn:e2. 2: discriminate.
  inversion e. subst. clear e.
  eapply match_prelhs_subst_length in e1.
  eapply map_option_out_length in e2. lia.
Qed.

Fixpoint partial_subst_size (σ : partial_subst) : nat :=
  match σ with
  | [] => 0
  | None :: σ => partial_subst_size σ
  | Some t :: σ => S (size t + partial_subst_size σ)
  end.

Lemma partial_subst_size_subs_empty :
  forall npat,
    partial_subst_size (subs_empty npat) = 0.
Proof.
  intro npat.
  unfold subs_empty.
  induction npat.
  - reflexivity.
  - cbn. auto.
Qed.

Lemma partial_subst_size_subs_merge :
  forall σ θ ρ,
    subs_merge σ θ = Some ρ ->
    partial_subst_size ρ = partial_subst_size σ + partial_subst_size θ.
Proof.
  intros σ θ ρ e.
  induction σ as [| [] σ ih] in θ, ρ, e |- *.
  - destruct θ. 2: discriminate.
    cbn in e. apply some_inj in e. subst.
    cbn. reflexivity.
  - destruct θ as [| [] θ]. 1-2: discriminate.
    cbn in *. destruct subs_merge eqn:e1. 2: discriminate.
    apply some_inj in e. subst.
    eapply ih in e1. cbn. lia.
  - destruct θ as [| x θ].
    + discriminate.
    + cbn in e. destruct subs_merge eqn:e1. 2: discriminate.
      apply some_inj in e. subst.
      eapply ih in e1.
      cbn.
      destruct x.
      * lia.
      * lia.
Qed.

Lemma partial_subst_size_app :
  forall σ θ,
    partial_subst_size (σ ++ θ) = partial_subst_size σ + partial_subst_size θ.
Proof.
  intros σ θ.
  induction σ as [| [] σ ih] in θ |- *.
  - reflexivity.
  - cbn. rewrite ih. lia.
  - cbn. apply ih.
Qed.

Lemma list_decompose :
  forall {A : Type} n (l : list A) t,
    nth_error l n = Some t ->
    l = firstn n l ++ t :: skipn (S n) l.
Proof.
  intros A n l t e.
  induction l in n, t, e |- *.
  - destruct n. all: discriminate.
  - destruct n.
    + cbn in e. apply some_inj in e. subst.
      cbn. reflexivity.
    + cbn in e. eapply IHl in e.
      cbn. f_equal. auto.
Qed.

Lemma partial_subst_size_subs_add :
  forall n t σ θ,
    subs_add n t σ = Some θ ->
    partial_subst_size θ = S (size t + partial_subst_size σ).
Proof.
  intros n t σ θ e.
  unfold subs_add in e.
  destruct nth_error as [[]|] eqn:e1. 1,3: discriminate.
  apply some_inj in e. subst.
  rewrite partial_subst_size_app. cbn.
  rewrite (list_decompose n σ) at 3. 2: eauto.
  rewrite partial_subst_size_app. cbn.
  lia.
Qed.

Lemma partial_subst_size_subs_init :
  forall npat n t σ,
    subs_init npat n t = Some σ ->
    partial_subst_size σ = S (size t).
Proof.
  intros npat n t σ e.
  unfold subs_init in e.
  eapply partial_subst_size_subs_add in e.
  rewrite e. rewrite partial_subst_size_subs_empty.
  lia.
Qed.

Lemma partial_subst_size_map_option_out :
  forall σ θ,
    map_option_out σ = Some θ ->
    partial_subst_size σ = list_size size θ.
Proof.
  intros σ θ e.
  induction σ as [| [] σ ih] in θ, e |- *.
  - cbn in e. apply some_inj in e. subst.
    reflexivity.
  - cbn in *. destruct map_option_out eqn:e1. 2: discriminate.
    apply some_inj in e. subst.
    specialize ih with (1 := eq_refl).
    cbn. auto.
  - cbn in e. discriminate.
Qed.

Lemma match_pattern_subst_size :
  forall npat p t σ,
    match_pattern npat p t = Some σ ->
    partial_subst_size σ <= S (size t).
Proof.
  intros npat p t σ e.
  induction p using term_forall_list_ind in t, σ, e |- *.
  all: try discriminate.
  - cbn in e. eapply partial_subst_size_subs_init in e. lia.
  - cbn in e. destruct t. all: try discriminate.
    destruct match_pattern eqn:e1. 2: discriminate.
    move e at top.
    destruct match_pattern eqn:e2. 2: discriminate.
    eapply partial_subst_size_subs_merge in e.
    eapply IHp1 in e1.
    eapply IHp2 in e2.
    cbn. lia.
  - cbn - [ assert_eq ] in e.
    unfold assert_eq in e.
    destruct (eqb_spec (tConstruct i n u) t). 2: discriminate.
    cbn in e. apply some_inj in e. subst.
    cbn. rewrite partial_subst_size_subs_empty. auto.
Qed.

Lemma match_prelhs_subst_size :
  forall npat k n l t ui σ,
    match_prelhs npat k n l t = Some (ui, σ) ->
    partial_subst_size σ < size t.
Proof.
  intros npat k n l t ui σ e.
  induction l as [| a l ih] in t, ui, σ, e |- *.
  - cbn in e. destruct t. all: try discriminate.
    destruct assert_eq. 2: discriminate.
    destruct assert_eq. 2: discriminate.
    inversion e.
    cbn. rewrite partial_subst_size_subs_empty. auto.
  - cbn in e. destruct a.
    + destruct t. all: try discriminate.
      destruct match_pattern eqn:e3. 2: discriminate.
      destruct match_prelhs as [[? ?]|] eqn:e1. 2: discriminate.
      destruct subs_merge eqn:e2. 2: discriminate.
      inversion e. subst. clear e.
      eapply ih in e1.
      cbn.
      eapply partial_subst_size_subs_merge in e2.
      eapply match_pattern_subst_size in e3.
      lia.
    + destruct t. all: try discriminate.
      destruct assert_eq. 2: discriminate.
      destruct match_pattern eqn:e5. 2: discriminate.
      destruct option_map2 as [l1 |] eqn:e6. 2: discriminate.
      destruct monad_fold_right as [l2 |] eqn:e1. 2: discriminate.
      destruct match_prelhs as [[? ?]|] eqn:e2. 2: discriminate.
      destruct subs_merge as [θ|] eqn:e3. 2: discriminate.
      destruct (subs_merge θ _) eqn:e4. 2: discriminate.
      inversion e. subst. clear e.
      eapply ih in e2.
      cbn.
      eapply match_pattern_subst_size in e5.
      eapply partial_subst_size_subs_merge in e3.
      eapply partial_subst_size_subs_merge in e4.
      assert (partial_subst_size l2 <= list_size (fun x => size x.2) brs0).
      { clear - e6 e1.
        induction brs0 as [| [] brs0 ih] in brs, l1, e6, l2, e1 |- *.
        - destruct brs. 2: discriminate.
          cbn in e6. apply some_inj in e6. subst.
          cbn in e1. apply some_inj in e1. subst.
          rewrite partial_subst_size_subs_empty. cbn. auto.
        - cbn. destruct brs as [| [] brs]. 1: discriminate.
          cbn in e6.
          destruct assert_eq. 2: discriminate.
          destruct match_pattern eqn:e2. 2: discriminate.
          destruct option_map2 eqn:e3. 2: discriminate.
          apply some_inj in e6. subst.
          cbn in e1. destruct monad_fold_right eqn:e4. 2: discriminate.
          eapply ih in e3. 2: eauto.
          eapply partial_subst_size_subs_merge in e1.
          eapply match_pattern_subst_size in e2.
          lia.
      }
      lia.
    + destruct t. all: try discriminate.
      destruct assert_eq. 2: discriminate.
      eapply ih in e. cbn. auto.
Qed.

Lemma match_lhs_subst_size :
  forall npat k n l t ui σ,
    match_lhs npat k n l t = Some (ui, σ) ->
    list_size size σ < size t.
Proof.
  intros npat k n l t ui σ e.
  unfold match_lhs in e.
  destruct match_prelhs as [[? ?]|] eqn:e1. 2: discriminate.
  cbn in e. destruct map_option_out eqn:e2. 2: discriminate.
  inversion e. subst. clear e.
  eapply match_prelhs_subst_size in e1.
  eapply partial_subst_size_map_option_out in e2.
  lia.
Qed.
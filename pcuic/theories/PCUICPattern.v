(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils Universes BasicAst
  AstUtils UnivSubst EnvironmentTyping.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition.

(* TODO MOVE *)
Fixpoint list_make {A} (f : nat -> A) (i n : nat) : list A :=
  match n with
  | 0 => []
  | S n => f i :: list_make f (S i) n
  end.

(* TODO MOVE *)
Lemma list_make_length :
  forall A f i n,
    #|@list_make A f i n| = n.
Proof.
  intros A f i n.
  induction n in i |- *.
  - reflexivity.
  - simpl. f_equal. apply IHn.
Qed.

(* TODO MOVE *)
Lemma list_make_map :
  forall A f i n B (g : A -> B),
    map g (@list_make A f i n) = list_make (fun i => g (f i)) i n.
Proof.
  intros A f i n B g.
  induction n in i |- *.
  - reflexivity.
  - simpl. f_equal. eapply IHn.
Qed.

Definition symbols_subst k n u m :=
  list_make (fun i => tSymb k i u) n (m - n).

Lemma symbols_subst_length :
  forall k n u m,
    #|symbols_subst k n u m| = m - n.
Proof.
  intros k n u m.
  unfold symbols_subst.
  apply list_make_length.
Qed.

(** Instantiation of symbols in a pattern *)

Fixpoint pattern_inst_symb k ui {nsymb npat nb} (p : pattern nsymb npat nb) :
  pattern 0 npat nb :=
  let ss := symbols_subst k 0 ui nsymb in
  match p with
  | pattern_variable n mask hn hmask =>
    pattern_variable n mask hn hmask
  | pattern_bound n h =>
    pattern_bound n h
  | pattern_lambda na A b =>
    pattern_lambda na (subst ss (npat + nb) A) (pattern_inst_symb k ui b)
  | pattern_construct ind n ui' args =>
    pattern_construct ind n ui' (map (pattern_inst_symb k ui) args)
  | pattern_symbol k' n ui' args =>
    pattern_symbol k' n ui' (map (pattern_inst_symb k ui) args)
  | pattern_local n hs args =>
    pattern_symbol k n ui (map (pattern_inst_symb k ui) args)
  end.

Fixpoint elim_pattern_inst_symb k ui {nsymb npat} (e : elim_pattern nsymb npat)
  : elim_pattern 0 npat :=
  match e with
  | epApp p => epApp (pattern_inst_symb k ui p)
  | epCase ind p brs =>
    epCase ind (pattern_inst_symb k ui p) (map (on_snd (pattern_inst_symb k ui)) brs)
  | epProj p => epProj p
  end.

Import MonadNotation.

(** Strengthening along a mask

  Assume Γ, Δ, Ξ ⊢ t : A and #|m| = #|Δ|
  strengthen_mask m t #|Ξ| should return a term where masked varibles
  (their interpretation is false) of Δ are removed (if they can).
*)

Fixpoint nfalse m :=
  match m with
  | true :: m => nfalse m
  | false :: m => S (nfalse m)
  | [] => 0
  end.

Definition masked_before m n : nat :=
  nfalse (firstn n m).

(* TODO MOVE *)
Definition option_map_def {A B : Set}
  (tf bf : A -> option B) (d : def A) : option (def B) :=
  ty <- tf d.(dtype) ;;
  bo <- bf d.(dbody) ;;
  ret {|
    dname := d.(dname) ;
    dtype := ty ;
    dbody := bo ;
    rarg := d.(rarg)
  |}.

(* TODO MOVE *)
Definition option_on_snd {A B C : Type}
  (f : B -> option C) (p : A × B) : option (A × C) :=
  c <- f p.2 ;;
  ret (p.1, c).

Fixpoint strengthen_mask (m : list bool) k (t : term) : option term :=
  match t with
  | tRel i =>
      if i <? k then ret (tRel i)
      else
        match nth_error m (i - k) with
        | Some true => ret (tRel (i - masked_before m (i - k)))
        | Some false => None
        | None => ret (tRel (i - nfalse m))
        end

  | tEvar ev args =>
      args' <- monad_map (strengthen_mask m k) args ;;
      ret (tEvar ev args')
  | tLambda na A t =>
      A' <- strengthen_mask m k A ;;
      t' <- strengthen_mask m (S k) t ;;
      ret (tLambda na A' t')

  | tApp u v =>
      u' <- strengthen_mask m k u ;;
      v' <- strengthen_mask m k v ;;
      ret (tApp u' v')

  | tProd na A B =>
      A' <- strengthen_mask m k A ;;
      B' <- strengthen_mask m (S k) B ;;
      ret (tProd na A' B')

  | tLetIn na b B t =>
      b' <- strengthen_mask m k b ;;
      B' <- strengthen_mask m k B ;;
      t' <- strengthen_mask m (S k) t ;;
      ret (tLetIn na b' B' t')

  | tCase ind p c brs =>
      brs' <- monad_map (option_on_snd (strengthen_mask m k)) brs ;;
      p' <- strengthen_mask m k p ;;
      c' <- strengthen_mask m k c ;;
      ret (tCase ind p' c' brs')

  | tProj p c =>
      c' <- strengthen_mask m k c ;;
      ret (tProj p c')

  | tFix mfix idx =>
      let k' := (#|mfix| + k)%nat in
      mfix' <- monad_map (option_map_def (strengthen_mask m k) (strengthen_mask m k')) mfix ;;
      ret (tFix mfix' idx)

  | tCoFix mfix idx =>
      let k' := (#|mfix| + k)%nat in
      mfix' <- monad_map (option_map_def (strengthen_mask m k) (strengthen_mask m k')) mfix ;;
      ret (tCoFix mfix' idx)

  | x => ret x
  end.

Fixpoint mkLambda_mask (m : list bool) (Ξ : context) (b : term) : term :=
  match m, Ξ with
  | true :: m, {| decl_name := x ; decl_body := None ; decl_type := A |} :: Ξ =>
    tLambda x A (mkLambda_mask m Ξ b)
  | false :: m, d :: Ξ => mkLambda_mask m Ξ b
  | [], [] => b
  | _, _ => b (* Or use option? *)
  end.

(* TODO MOVE *)
Fixpoint list_init {A} (x : A) (n : nat) : list A :=
  match n with
  | 0 => []
  | S n => x :: list_init x n
  end.

Lemma list_init_length :
  forall A (x : A) n,
    #|list_init x n| = n.
Proof.
  intros A x n. induction n. 1: reflexivity.
  cbn. f_equal. assumption.
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

Definition option_assert (b : bool) : option () :=
  if b then ret tt else None.

Definition option_map2 {A B C}
  (f : A -> B -> option C) (l1 : list A) (l2 : list B) : option (list C) :=
  let aux :=
    fix aux l1 l2 :=
      match l1, l2 with
      | [], [] => ret []
      | x :: l1, y :: l2 =>
          z <- f x y ;;
          l <- aux l1 l2 ;;
          ret (z :: l)
      | _, _ => None
      end
  in aux l1 l2.

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

Fixpoint monad_fold_right {T} {M : Monad T} {A B} (g : A -> B -> T A)
  (l : list B) (x : A) : T A :=
  match l with
  | [] => ret x
  | y :: l =>
      a <- monad_fold_right g l x ;;
      g a y
  end.

(* For soundness and completeness we need to define lift_mask... *)

(** In order to apply the rules we need to define higher order matching.
    Contrarily to first-order matching, we can't use substitution for
    instantiation alone.

    We need to keep Ξ, the context of bound variables, in order to reconstruct
    λs when doing higher order matching.

    We cannot be type-directed as suggested by Jesper so we probably should
    restrict the rules to satisfy η.
    PROBLEM Even when η-expanding on the fly we have a problem: what about the
    domain? It's supposed to be a pattern so we would like to unify it with
    something, it's not possible however. To be compliant we need to either
    remove the pattern status of the domain or forget about η... at least so
    it seems.

    ANOTHER PROBLEM If I do η-expansion with tApp (lift0 1 t) (tRel 0)
    then all variables are a priori relevant in the term...
    So we will only be able to match patterns mentionning all bound variables.
    We'd be going through a lot of trouble for not much.

    SOLUTION? Only η-expanding when it's not a λ so as not to introduce
    β-redexes. Meaning two cases for λ patterns.

    ANOTHER PROBLEM pointed out by Jesper, some rewrite rules may not behave
    well with respect to free variable elimination.
    f x y -> c versus f -> λxy. c (we should enforce the latter for things
    to go smoothly).

    NOTE For now we only recognise when no symbols are left uninstantiated.
    This could be changed in the event we need to recognise them in the
    global context.
*)
Fixpoint match_pattern {npat} Ξ (p : pattern 0 npat #|Ξ|) (t : term) {struct p}
  : option partial_subst :=
  match p with
  | pattern_variable n mask hn hmask =>
    u <- strengthen_mask mask #|Ξ| t ;;
    subs_init npat n (mkLambda_mask mask Ξ u)
  | pattern_bound n bound =>
    option_assert (eqb t (tRel n)) ;;
    ret (subs_empty npat)
  | pattern_lambda na A b =>
    match t with
    | tLambda na' A' b' => match_pattern (Ξ ,, vass na A) b b'
    | _ => match_pattern (Ξ ,, vass na A) b (tApp (lift0 1 t) (tRel 0))
    end
  | pattern_construct ind n ui args =>
    let '(u,l) := decompose_app t in
    match u with
    | tConstruct ind' n' ui' =>
      option_assert (eqb ind ind') ;;
      option_assert (eqb n n') ;;
      option_assert (eqb ui ui') ;;
      sl <- option_map2 (fun p t => match_pattern Ξ p t) args l ;;
      monad_fold_right (subs_merge) sl (subs_empty npat)
    | _ => None
    end
  | pattern_symbol k n ui args =>
    let '(u,l) := decompose_app t in
    match u with
    | tSymb k' n' ui' =>
      option_assert (eqb k k') ;;
      option_assert (eqb n n') ;;
      option_assert (eqb ui ui') ;;
      sl <- option_map2 (fun p t => match_pattern Ξ p t) args l ;;
      monad_fold_right (subs_merge) sl (subs_empty npat)
    | _ => None
    end
  | pattern_local n hs args => False_rect _ ltac:(lia)
  end.

(* We assume el given reversed *)
Fixpoint match_elims
  (k : kername) (n : nat) (ui : universe_instance)
  {npat} (el : list (elim_pattern 0 npat))
  (t : term)
  : option (partial_subst) :=
  match el with
  | [] =>
    option_assert (eqb (tSymb k n ui) t) ;;
    ret (subs_empty npat)
  | epApp p :: el =>
    match t with
    | tApp u v =>
      sv <- match_pattern [] p v ;;
      su <- match_elims k n ui el u ;;
      subs_merge su sv
    | _ => None
    end
  | epCase ind p brs :: el =>
    match t with
    | tCase ind' p' c brs' =>
      option_assert (eqb ind ind') ;;
      sp <- match_pattern [] p p' ;;
      sl <- option_map2 (fun br br' =>
              option_assert (eqb br.1 br'.1) ;;
              match_pattern [] br.2 br'.2
            ) brs brs' ;;
      sb <- monad_fold_right (subs_merge) sl (subs_empty npat) ;;
      sc <- match_elims k n ui el c ;;
      s1 <- subs_merge sp sb ;;
      subs_merge s1 sc
    | _ => None
    end
  | epProj p :: l =>
    match t with
    | tProj p' u =>
      option_assert (eqb p p') ;;
      match_elims k n ui el u
    | _ => None
    end
  end.

Definition match_lhs k n ui {npat} (l : list (elim_pattern 0 npat)) t :=
  s <- match_elims k n ui (List.rev l) t ;;
  (* From linearity the following should always succeed *)
  map_option_out s.

Definition match_rule {nsymb} k ui (r : rewrite_rule nsymb) t :=
  match_lhs k r.(head) ui (map (elim_pattern_inst_symb k ui) r.(elims)) t.

Lemma map_option_out_length :
  forall A (l : list (option A)) l',
    map_option_out l = Some l' ->
    #|l| = #|l'|.
Proof.
  intros A l l' e.
  induction l as [| [] l ih] in l', e |- *.
  - cbn in e. apply some_inj in e. subst. reflexivity.
  - cbn in e. destruct map_option_out eqn:e1. 2: discriminate.
    apply some_inj in e. subst. cbn. f_equal.
    apply ih. reflexivity.
  - cbn in e. discriminate.
Qed.

Lemma match_pattern_length :
  forall npat Ξ p t s,
    @match_pattern npat Ξ p t = Some s ->
    #|s| = npat.
Admitted.

Lemma match_elims_length :
  forall k n ui npat el t s,
    @match_elims k n ui npat el t = Some s ->
    #|s| = npat.
Proof.
  intros k n ui npat el t s e.
  induction el as [| [] el ih].
  - unfold match_elims in e. cbn fix in e.
    (* WHY doesn't it reduce??? *)
    admit.
  -
Admitted.

Lemma match_lhs_length :
  forall k n ui npat l t s,
    @match_lhs k n ui npat l t = Some s ->
    #|s| = npat.
Proof.
  intros k n ui npat l t s e.
  unfold match_lhs in e.
  destruct match_elims eqn:e1. 2: discriminate.
  cbn in e.
  apply match_elims_length in e1.
  apply map_option_out_length in e.
  lia.
Qed.

Lemma match_rule_length :
  forall nsymb k ui r t s,
    @match_rule nsymb k ui r t = Some s ->
    #|s| = #|r.(pat_context)|.
Proof.
  intros nsymb k ui r t s e.
  unfold match_rule in e.
  apply match_lhs_length in e.
  assumption.
Qed.

(** Notion of linearity

  We use a notion of linear mask. Similar to partial substitutions
  and strengthening masks.
*)

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

Fixpoint pattern_mask {nsymb npat nb} (p : pattern nsymb npat nb) :=
  match p with
  | pattern_variable n mask hn hmask => lin_set n (linear_mask_init npat)
  | pattern_bound n h => ret (linear_mask_init npat)
  | pattern_lambda na A b => pattern_mask b
  | pattern_construct ind n ui args =>
    sl <- monad_map (fun p => pattern_mask p) args ;;
    monad_fold_right (lin_merge) sl (linear_mask_init npat)
  | pattern_symbol k n ui args =>
    sl <- monad_map (fun p => pattern_mask p) args ;;
    monad_fold_right (lin_merge) sl (linear_mask_init npat)
  | pattern_local n hs args =>
    sl <- monad_map (fun p => pattern_mask p) args ;;
    monad_fold_right (lin_merge) sl (linear_mask_init npat)
  end.

Fixpoint elim_mask {nsymb npat} (e : elim_pattern nsymb npat) :=
  match e with
  | epApp p => pattern_mask p
  | epCase ind p brs =>
    lp <- pattern_mask p ;;
    lb <- monad_map (fun p => pattern_mask p.2) brs ;;
    lb <- monad_fold_right (lin_merge) lb (linear_mask_init npat) ;;
    lin_merge lp lb
  | epProj p => ret (linear_mask_init npat)
  end.

Definition linear_mask {nsymb npat} (el : list (elim_pattern nsymb npat)) :=
  l <- monad_map elim_mask el ;;
  monad_fold_right lin_merge l (linear_mask_init npat).

(** We force all variables to appear exactly once
    (we could also allow some to be forgotten)
*)
Definition linear {nsymb npat} (el : list (elim_pattern nsymb npat)) :=
  match linear_mask el with
  | Some l => forallb (fun x => x) l
  | None => false
  end.

(** Some lemmata *)

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
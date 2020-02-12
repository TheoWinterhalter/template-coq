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

(** Notion of linearity

  We use a notion of linear mask. Similar to partial substitutions.
*)

(* TODO MOVE *)
Fixpoint list_init {A} (x : A) (n : nat) : list A :=
  match n with
  | 0 => []
  | S n => x :: list_init x n
  end.

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

Fixpoint elim_mask npat e :=
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
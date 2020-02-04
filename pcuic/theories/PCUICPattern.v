(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils Universes BasicAst
  AstUtils UnivSubst EnvironmentTyping.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition.

Import MonadNotation.

(* Pattern definition

   This definition is relative to the number of pattern variables,
   and the number of bound variables introduced afterwards.

   TODO Can we have an "exact" pattern this way?

   TODO How to guarantee the tConstruct is fully applied?
   Maybe we don't have to.

   TODO Maybe constraint pattern_variable so the list is without duplicates.
*)
Inductive pattern (npat : nat) (nb : nat) : Type :=
| pattern_variable n (mask : list bool) :
    nb <= n ->
    n < npat + nb ->
    #|mask| = nb ->
    pattern npat nb

| pattern_bound n (bound : n < nb)

| pattern_lambda (A : pattern npat nb) (b : pattern npat (S nb))

| pattern_construct
    (ind : inductive) (n : nat) (ui : universe_instance)
    (args : list (pattern npat nb)).

Inductive elim_pattern (npat : nat) : Type :=
| epApp (p : pattern npat 0)
| epCase
    (indn : inductive × nat) (p : pattern npat 0)
    (brs : list (nat × pattern npat 0))
| epProj (p : projection).

Fixpoint mask_to_rels (mask : list bool) (i : nat) :=
  match mask with
  | true :: mask => tRel i :: mask_to_rels mask (S i)
  | false :: mask => mask_to_rels mask (S i)
  | [] => []
  end.

(* Translating patterns to terms

  Maybe it'd be smarter to define instantiation...
*)
Fixpoint pattern_to_term {npat nb} (p : pattern npat nb) : term :=
  match p with
  | pattern_variable n mask h1 h2 h3 =>
    mkApps (tRel n) (mask_to_rels mask 0)
  | pattern_bound n h => tRel n
  | pattern_lambda A b => tLambda nAnon (pattern_to_term A) (pattern_to_term b)
  | pattern_construct ind n ui args =>
    mkApps (tConstruct ind n ui) (map (pattern_to_term) args)
  end.

Fixpoint elim_pattern_to_elim {npat} (e : elim_pattern npat) : elimination :=
  match e with
  | epApp p => eApp (pattern_to_term p)
  | epCase indn p brs =>
    eCase indn (pattern_to_term p) (map (on_snd (pattern_to_term)) brs)
  | epProj p => eProj p
  end.

Local Notation mask := (list bool).
Notation partial_subst := (list (option term)).

(* Strengthening along a mask
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

(* For soundness and completeness we need to define lift_mask... *)

(* In order to apply the rules we need to define higher order matching.
   Contrarily to first-order matching, we can't use substitution for
   instantiation alone.
*)
(* Fixpoint match_pattern {npat nb} (p : pattern npat nb) (t : term)
  : option partial_subst :=
  match p with
  | pattern_variable n mask hnb hnpat hmask => *)
(* In order to complete the definition we need strengthen_mask but also
  some way to write lambdas from a mask, however we're missing the types
  to put in the domains...
*)
(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils Universes BasicAst
  AstUtils UnivSubst EnvironmentTyping.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition.

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

Notation partial_subst := (list (option term)).

(* In order to apply the rules we need to define higher order matching.
   Contrarily to first-order matching, we can't use substitution for
   instantiation alone.
*)
(* Fixpoint match_pattern {npat nb} (p : pattern npat nb) (t : term) : option partial_subst *)
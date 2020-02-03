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
Inductive pattern (npat : nat) (nb : nat) : term -> Prop :=
| pattern_variable :
    forall n l,
      nb <= n ->
      n < npat + nb ->
      Forall (fun m => m < nb) l ->
      pattern npat nb (mkApps (tRel n) (map tRel l))

| pattern_bound :
    forall n,
      n < nb ->
      pattern npat nb (tRel n)

| pattern_lambda :
    forall na A t,
      pattern npat nb A ->
      pattern npat (S nb) t ->
      pattern npat nb (tLambda na A t)

| pattern_construct :
    forall ind n ui args,
      Forall (pattern npat nb) args ->
      pattern npat nb (mkApps (tConstruct ind n ui) args)

| pattern_symbol :
    forall k n ui args,
      Forall (pattern npat nb) args ->
      pattern npat nb (mkApps (tSymb k n ui) args)
.

Inductive elim_pattern (npat : nat) : elimination -> Prop :=
| pat_elim_App :
    forall p,
      pattern npat 0 p ->
      elim_pattern npat (eApp p)

| pat_elim_Case :
    forall indn p brs,
      pattern npat 0 p ->
      Forall (fun br => pattern npat 0 br.2) brs ->
      elim_pattern npat (eCase indn p brs)

| pat_elim_Proj :
    forall p,
      elim_pattern npat (eProj p).
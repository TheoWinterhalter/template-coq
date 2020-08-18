(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".
Require Import ssreflect.
From Equations Require Import Equations.
From Coq Require Import String Bool List Utf8 Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping
  PCUICReduction PCUICWeakening PCUICEquality PCUICUnivSubstitution
  PCUICParallelReduction PCUICParallelReductionConfluence PCUICInduction
  PCUICRW PCUICPattern.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Import MonadNotation.

Set Asymmetric Patterns.

Set Default Goal Selector "!".

(** EXAMPLES OF REWRITE RULES

Here are some examples of rewrite rules that are handled by the system.
This also illustrates how modular it is.

*)

Open Scope string_scope.

Existing Instance config.default_checker_flags.

Definition nouniv :=
  Monomorphic_ctx (
    {| LS.this := [] ; LS.is_ok := LevelSet.Raw.empty_ok |},
    {| CS.this := [] ; CS.is_ok := ConstraintSet.Raw.empty_ok |}
  ).

(** Natural numbers *)
Definition natpath := MPfile [ "nat" ].

Definition natdecl :=
  InductiveDecl {|
    ind_finite := Finite ;
    ind_npars  := 0 ;
    ind_params := [] ;
    ind_bodies := [
      {|
        ind_name := "nat" ;
        ind_type := tSort {|
          Universe.t_set := {|
            UnivExprSet.this := [ UnivExpr.npe (NoPropLevel.lSet, false) ] ;
            UnivExprSet.is_ok :=
              UnivExprSet.Raw.singleton_ok
                (UnivExpr.npe (NoPropLevel.lSet, false))
          |} ;
          Universe.t_ne := eq_refl
        |} ;
        ind_kelim := InType ;
        ind_ctors := [
          ("O", tRel 0, 0) ;
          ("S", tProd nAnon (tRel 0) (tRel 1), 1)
        ] ;
        ind_projs := []
      |}
    ] ;
    ind_universes := Monomorphic_ctx (
      {| LS.this := [] ; LS.is_ok := LevelSet.Raw.empty_ok |},
      {| CS.this := [] ; CS.is_ok := ConstraintSet.Raw.empty_ok |}
    ) ;
    ind_variance := None
  |}.

Definition Σnat := (natpath, natdecl).

Lemma on_nat :
  on_global_decl (PCUICEnvTyping.lift_typing typing) ([], nouniv)
    (natpath, "nat") natdecl.
Proof.
  cbn. constructor.
  - constructor. 2: constructor.
    econstructor.
    + instantiate (2 := []). cbn. reflexivity.
    + cbn. eexists. (* eapply type_Sort. *) admit.
    + cbn. admit.
    + cbn. contradiction.
    + cbn. admit.
  - cbn. constructor.
  - cbn. reflexivity.
  - admit.
Admitted.

(** Parallel plus

pplus : nat → nat → nat
-----------------------------------------
n,m : nat ⊢ pplus (S n) m ↦ S (pplus n m)
n,m : nat ⊢ pplus n (S m) ↦ S (pplus n m)
m : nat   ⊢ pplus 0 m     ↦ m
n : nat   ⊢ pplus n 0     ↦ n

To prove the local triangle property we add the following parallel rule:

n,m : nat ⊢ pplus (S n) (S m) ↦ S (S (plus n m))

*)

Definition pplus_path := MPfile [ "pplus" ].

Definition tArrow A B :=
  tProd nAnon A (lift0 1 B).

Definition tNat :=
  tInd {|
    inductive_mind := (MPfile [], "nat") ;
    inductive_ind := 0
  |} Instance.empty.

Definition t0 :=
  tConstruct {|
    inductive_mind := (MPfile [], "nat") ;
    inductive_ind := 0
  |} 0 Instance.empty.

Definition cS :=
  tConstruct {|
    inductive_mind := (MPfile [], "nat") ;
    inductive_ind := 0
  |} 1 Instance.empty.

Definition tS (t : term) :=
  tApp cS t.

Definition pplus_decl :=
  RewriteDecl {|
    symbols := [ tArrow tNat (tArrow tNat tNat) ] ;
    rules := [
      {|
        pat_context := [] ,, vass (nNamed "n") tNat ,, vass (nNamed "m") tNat ;
        head := 0 ;
        elims := [ eApp (tS (tRel 1)) ; eApp (tRel 0) ] ;
        rhs := tS (mkApps (tRel 2) [ tRel 1 ; tRel 0 ])
      |} ;
      {|
        pat_context := [] ,, vass (nNamed "n") tNat ,, vass (nNamed "m") tNat ;
        head := 0 ;
        elims := [ eApp (tRel 1) ; eApp (tS (tRel 0)) ] ;
        rhs := tS (mkApps (tRel 2) [ tRel 1 ; tRel 0 ])
      |} ;
      {|
        pat_context := [] ,, vass (nNamed "m") tNat ;
        head := 0 ;
        elims := [ eApp t0 ; eApp (tRel 0) ] ;
        rhs := tRel 0
      |} ;
      {|
        pat_context := [] ,, vass (nNamed "n") tNat ;
        head := 0 ;
        elims := [ eApp (tRel 0) ; eApp t0 ] ;
        rhs := tRel 0
      |}
    ] ;
    prules := [
      {|
        pat_context := [] ,, vass (nNamed "n") tNat ,, vass (nNamed "m") tNat ;
        head := 0 ;
        elims := [ eApp (tS (tRel 1)) ; eApp (tS (tRel 0)) ] ;
        rhs := tS (tS (mkApps (tRel 2) [ tRel 1 ; tRel 0 ]))
      |}
    ] ;
    rew_universes := nouniv
  |}.
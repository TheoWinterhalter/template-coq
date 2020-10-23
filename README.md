MetaCoq with Rewrite Rules
==========================

This branch contains an extension of MetaCoq with rewrite rules and constitutes the artifact associated with the paper "The Taming of the Rew: A Type Theory with Computational Assumptions".

## Quick jump:

- [Building the project](#building-the-project)
- [High-level description of changes](#changes)


## Changes

With respect to the MetaCoq repository, we introduce four new files (in `pcuic/theories`):
- `PCUICPattern.v`,
- `PCUICRw.v`,
- `PCUICPredExtra.v`,
- `RewExamples.v`

and modify several, we will only list the most important changes.

#### [`template-coq/theories/Environment.v`](template-coq/theories/Environment.v):

We extend the notion of global environment to add rewrite rule declarations
(`rewrite_decl`) to it.

#### [`template-coq/theories/EnvironmentTyping.v`](template-coq/theories/EnvironmentTyping.v):

We define the `on_rewrite_decl` predicate indicating what properties must
rewrite rules verify for the environment to be well-formed.

#### [`pcuic/theories/PCUICAst.v`](pcuic/theories/PCUICAst.v):
A new constructor `tSymb` is added to the syntax (i.e. to the inductive type `term`) representing fresh symbols for rewrite rules.

#### [`pcuic/theories/PCUICPattern.v`](pcuic/theories/PCUICPattern.v):

Definition of the notion of pattern and properties about them, including
matching.

#### [`pcuic/theories/PCUICTyping.v`](pcuic/theories/PCUICTyping.v):

Here we only introduce a typing rule for (rewrite rule) symbols:
```coq
type_Symb k n u :
  All_local_env (lift_typing typing Σ) Γ ->
  forall decl (isdecl : declared_symbol Σ.1 k decl) ty,
    nth_error decl.(symbols) n = Some ty ->
    consistent_instance_ext Σ decl.(rew_universes) u ->
    Σ ;;; Γ |- tSymb k n u : subst (symbols_subst k (S n) u #|decl.(symbols)|) 0 (subst_instance_constr u ty)
```

#### [`pcuic/theories/PCUICWeakeningEnv.v`](pcuic/theories/PCUICWeakeningEnv.v):

This file makes sure that properties holding on a subenvironment of a global environment still hold on the bigger one. This means in particular that the properties we require on our rewrite rules are indeed modular (in fact they are even local).

#### [`pcuic/theories/PCUICRW.v`](pcuic/theories/PCUICRW.v):

Various properties on rewrite rules. In particular, define the notion of
`pattern_footprint` which corresponds to the largest subterm of a term which is
a pattern (in case the term is not a pattern, this will return a variable) and a
substitution yielding the original term. This is a factorisation procedure.
In the end we get `lhs_footprint` which returns the footprint of a left-hand
side which behaves the same way with respect to matching.

#### [`pcuic/theories/PCUICParallelReduction.v`](pcuic/theories/PCUICParallelReduction.v):

The definition of the parallel reduction is extended with three cases:
```coq
| pred_symb k n u :
    All2_local_env (on_decl pred1) Γ Γ' ->
    pred1 Γ Γ' (tSymb k n u) (tSymb k n u)

| pred_rewrite_rule k ui decl n r s s' :
    All2_local_env (on_decl pred1) Γ Γ' ->
    declared_symbol Σ k decl ->
    nth_error decl.(rules) n = Some r ->
    All2 (pred1 Γ Γ') s s' ->
    let ss := symbols_subst k 0 ui #|decl.(symbols)| in
    untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
    let lhs := subst0 s (subst ss #|s| (lhs r)) in
    let rhs := subst0 s' (subst ss #|s| (rhs r)) in
    pred1 Γ Γ' lhs rhs

| pred_par_rewrite_rule k ui decl n r s s' :
    All2_local_env (on_decl pred1) Γ Γ' ->
    declared_symbol Σ k decl ->
    nth_error decl.(prules) n = Some r ->
    All2 (pred1 Γ Γ') s s' ->
    let ss := symbols_subst k 0 ui #|decl.(symbols)| in
    untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
    let lhs := subst0 s (subst ss #|s| (lhs r)) in
    let rhs := subst0 s' (subst ss #|s| (rhs r)) in
    pred1 Γ Γ' lhs rhs
```

#### [`pcuic/theories/PCUICPredExtra.v`](pcuic/theories/PCUICPredExtra.v):

Definition of a notion of parallel reduction `pred1_extra` extended with a set
of rewrite rules and relate it to `pred1`.

#### [`pcuic/theories/PCUICParallelReductionConfluence.v`](pcuic/theories/PCUICParallelReductionConfluence.v):

We adapt the proof of confluence for the parallel reduction. The section
`Confluenv` defines the `confluenv` predicate corresponding to the requirements
placed on the rewrite rules to ensure confluence (via the triangle property).

#### [`pcuic/theories/PCUICConfluence.v`](pcuic/theories/PCUICConfluence.v):
Here the proof of confluence is modified. In particular it contains the confluence theorem
```coq
Lemma red_confluence {Γ t u v} :
  red Σ Γ t u ->
  red Σ Γ t v ->
  ∑ v', red Σ Γ u v' * red Σ Γ v v'.
```
Printing assumptions for this theorem yields
```coq
Section Variables:
Σ : global_env
wfΣ : wf Σ
cΣ : confluenv Σ
cf : checker_flags
Axioms:
ind_guard : mutual_inductive_body → bool
FunctionalExtensionality.functional_extensionality_dep :
∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
  (∀ x : A, f x = g x) → f = g
fix_guard : mfixpoint term → bool
cofix_guard : mfixpoint term → bool
```
meaning that only functional extensionality is required to prove the theorem (the other axioms only refer to the guard condition in a way to remain modular with respect to it).

#### [`pcuic/theories/PCUICSR.v`](pcuic/theories/PCUICSR.v):

Updated proof of subject reduction.
The proof is done by assuming the (global) property that rewrite rules are type preserving.
```coq
Definition type_preserving `{cf : checker_flags} (Σ : global_env_ext) :=
  forall k decl n r ui σ Γ A,
    declared_symbol Σ k decl ->
    nth_error (rules decl) n = Some r ->
    let ss := symbols_subst k 0 ui #|symbols decl| in
    untyped_subslet Γ σ (subst_context ss 0 (pat_context r)) ->
    Σ ;;; Γ |- subst0 σ (subst ss #|σ| (lhs r)) : A ->
    Σ ;;; Γ |- subst0 σ (subst ss #|σ| (rhs r)) : A.
```
This allows us to conclude that the interaction between rewrite rules and the
rest of the system does not compromise the subject reduction property.
```coq
Theorem subject_reduction :
  forall (Σ : global_env_ext) Γ t u T,
    wf Σ ->
    confluenv Σ ->
    Minimal (eq_universe Σ) ->
    type_preserving Σ ->
    minimal_inds Σ ->
    minimal_cst Σ ->
    Σ ;;; Γ |- t : T ->
    red Σ Γ t u ->
    Σ ;;; Γ |- u : T.
```
(The `Minimal`, `minimal_inds` and `minimal_cst` predicates ensure that the
universe graph is minimal in that it does not contain two universes defined to
be  equal.)
Once again, printing assumptions yields:
```coq
Axioms:
ind_guard : mutual_inductive_body -> bool
FunctionalExtensionality.functional_extensionality_dep :
forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
(forall x : A, f x = g x) -> f = g
fix_guard_subst_instance : forall (mfix : mfixpoint term) (u : Instance.t),
	                       fix_guard mfix ->
                           fix_guard
                             (map
                                (map_def (subst_instance_constr u)
                                   (subst_instance_constr u)) mfix)
fix_guard_subst : forall (mfix : list (def term)) (s : list term) (k : nat),
                  let k' := #|mfix| + k in
                  let mfix' := map (map_def (subst s k) (subst s k')) mfix in
                  fix_guard mfix -> fix_guard mfix'
fix_guard_red1 : forall (Σ : global_env) (Γ : context)
                   (mfix mfix' : mfixpoint term) (idx : nat),
                 fix_guard mfix ->
                 red1 Σ Γ (tFix mfix idx) (tFix mfix' idx) -> fix_guard mfix'
fix_guard_lift : forall (mfix : list (def term)) (n k : nat),
                 let k' := #|mfix| + k in
                 let mfix' := map (map_def (lift n k) (lift n k')) mfix in
                 fix_guard mfix -> fix_guard mfix'
fix_guard : mfixpoint term -> bool
cofix_guard_subst_instance : forall (mfix : mfixpoint term) (u : Instance.t),
                             cofix_guard mfix ->
                             cofix_guard
                               (map
                                  (map_def (subst_instance_constr u)
                                     (subst_instance_constr u)) mfix)
cofix_guard_subst : forall (mfix : list (def term)) (s : list term) (k : nat),
                    let k' := #|mfix| + k in
                    let mfix' := map (map_def (subst s k) (subst s k')) mfix
                      in
                    cofix_guard mfix -> cofix_guard mfix'
cofix_guard_red1 : forall (Σ : global_env) (Γ : context)
                     (mfix mfix' : mfixpoint term)
                     (idx : nat),
                   cofix_guard mfix ->
                   red1 Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx) ->
                   cofix_guard mfix'
cofix_guard_lift : forall (mfix : list (def term)) (n k : nat),
                   let k' := #|mfix| + k in
                   let mfix' := map (map_def (lift n k) (lift n k')) mfix in
                   cofix_guard mfix -> cofix_guard mfix'
cofix_guard : mfixpoint term -> bool
```
Besides `FunctionalExtensionality.functional_extensionality_dep` all axioms have to do with guard conditions.

## Building the project

In order to build this project you need to have
- Coq 8.11.0
- Equations 1.2.1+8.11

They can be installed using opam:
```sh
opam install coq.8.11.0 coq-equations.1.2.1+8.11
```

Once you have them you can simply build the project using
```
./configure.sh local
make pcuic -j4
```
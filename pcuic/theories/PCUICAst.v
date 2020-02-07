(* Distributed under the terms of the MIT license.   *)

Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import List. Import ListNotations.
From MetaCoq.Template Require Import utils.
From MetaCoq.Template Require Export Universes BasicAst Environment.

(* Declare Scope pcuic.*)
Delimit Scope pcuic with pcuic.
Open Scope pcuic.

(** * AST of the Polymorphic Cumulative Calculus of Inductive Constructions

   This AST is a cleaned-up version of Coq's internal AST better suited for reasoning.
   In particular, it has binary applications and all terms are well-formed.
   Casts are absent as well. *)

Inductive term : Set :=
| tRel (n : nat)
| tVar (i : ident) (* For free variables (e.g. in a goal) *)
| tEvar (n : nat) (l : list term)
| tSort (u : universe)
| tProd (na : name) (A B : term)
| tLambda (na : name) (A t : term)
| tLetIn (na : name) (b B t : term) (* let na := b : B in t *)
| tApp (u v : term)
| tSymb (k : kername) (n : nat) (ui : universe_instance)
| tConst (k : kername) (ui : universe_instance)
| tInd (ind : inductive) (ui : universe_instance)
| tConstruct (ind : inductive) (n : nat) (ui : universe_instance)
| tCase (indn : inductive * nat) (p c : term) (brs : list (nat * term)) (* # of parameters/type info/discriminee/branches *)
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat).

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | u :: us => mkApps (tApp t u) us
  end.

Definition isApp t :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ _ => true
  | _ => false
  end.

(** ** Entries

  The kernel accepts these inputs and typechecks them to produce
  declarations. Reflects [kernel/entries.mli].
*)

(** *** Constant and axiom entries *)

Record parameter_entry := {
  parameter_entry_type      : term;
  parameter_entry_universes : universes_decl }.

Record definition_entry := {
  definition_entry_type      : term;
  definition_entry_body      : term;
  definition_entry_universes : universes_decl;
  definition_entry_opaque    : bool }.


Inductive constant_entry :=
| ParameterEntry  (p : parameter_entry)
| DefinitionEntry (def : definition_entry).

(** *** Inductive entries *)

(** This is the representation of mutual inductives.
    nearly copied from [kernel/entries.mli]

  Assume the following definition in concrete syntax:

[[
  Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
  ...
  with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1  ... | cpnp : Tpnp.
]]

  then, in [i]th block, [mind_entry_params] is [xn:Xn;...;x1:X1];
  [mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
  [mind_entry_lc] is [Ti1;...;Tini], defined in context
  [A'1;...;A'p;x1:X1;...;xn:Xn] where [A'i] is [Ai] generalized over
  [x1:X1;...;xn:Xn].
*)

Inductive local_entry : Set :=
| LocalDef : term -> local_entry (* local let binding *)
| LocalAssum : term -> local_entry.

Record one_inductive_entry : Set := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term (* constructor list *) }.

Record mutual_inductive_entry := {
  mind_entry_record    : option (option ident);
  (* Is this mutual inductive defined as a record?
     If so, is it primitive, using binder name [ident]
     for the record in primitive projections ? *)
  mind_entry_finite    : recursivity_kind;
  mind_entry_params    : list (ident * local_entry);
  mind_entry_inds      : list one_inductive_entry;
  mind_entry_universes : universes_decl;
  mind_entry_private   : option bool
  (* Private flag for sealing an inductive definition in an enclosing
     module. Not handled by Template Coq yet. *) }.


(** Syntax of patterns

  They contain both symbol and local patterns, they correspond to the same
  thing but at different stages.

  Indices are understood locally in their respective contexts.
*)
Inductive pattern : Type :=
| pVar (n : nat) (mask : list bool)
| pBound (n : nat)
| pLambda (na : name) (A : term) (b : pattern)
| pConstruct
    (ind : inductive) (n : nat) (ui : universe_instance)
    (args : list pattern)
| pSymb
    (k : kername) (n : nat) (ui : universe_instance)
    (args : list pattern)
| pLocal (n : nat) (args : list pattern).

Inductive elim_pattern : Type :=
| epApp (p : pattern)
| epCase (ind : inductive × nat) (p : pattern) (brs : list (nat × pattern))
| epProj (p : projection).

Inductive elimination :=
| eApp (p : term)
| eCase (indn : inductive * nat) (p : term) (brs : list (nat * term))
| eProj (p : projection).

Definition mkElim t e :=
  match e with
  | eApp p => mkApps t [ p ]
  | eCase indn p brs => tCase indn p t brs
  | eProj p => tProj p t
  end.

Definition mkElims t el :=
  fold_left mkElim el t.

Fixpoint mask_to_rels (mask : list bool) (i : nat) :=
  match mask with
  | true :: mask => tRel i :: mask_to_rels mask (S i)
  | false :: mask => mask_to_rels mask (S i)
  | [] => []
  end.

(** Translating patterns to terms

  Maybe it'd be smarter to define instantiation...
*)
Fixpoint pattern_to_term npat nb (p : pattern) : term :=
  match p with
  | pVar n mask =>
    mkApps (tRel (n + nb)) (mask_to_rels mask 0)
  | pBound n => tRel n
  | pLambda na A b => tLambda na A (pattern_to_term npat nb b)
  | pConstruct ind n ui args =>
    mkApps (tConstruct ind n ui) (map (pattern_to_term npat nb) args)
  | pSymb k n ui args =>
    mkApps (tSymb k n ui) (map (pattern_to_term npat nb) args)
  | pLocal n args =>
    mkApps (tRel (n + npat + nb)) (map (pattern_to_term npat nb) args)
  end.

Fixpoint elim_pattern_to_elim npat (e : elim_pattern) : elimination :=
  match e with
  | epApp p => eApp (pattern_to_term npat 0 p)
  | epCase ind p brs =>
    eCase
      ind (pattern_to_term npat 0 p)
      (map (on_snd (pattern_to_term npat 0)) brs)
  | epProj p => eProj p
  end.

Definition mkPElims npat (t : term) (l : list elim_pattern) : term :=
  mkElims t (map (elim_pattern_to_elim npat) l).



Module PCUICTerm <: Term.

  Definition term := term.

  Definition tRel := tRel.
  Definition tSort := tSort.
  Definition tProd := tProd.
  Definition tLetIn := tLetIn.
  Definition tSymb := tSymb.
  Definition tInd := tInd.
  Definition tCase := tCase.
  Definition tProj := tProj.

  Definition mkApps := mkApps.
  Definition elim_pattern := elim_pattern.
  Definition mkPElims := mkPElims.

End PCUICTerm.

Module PCUICEnvironment := Environment PCUICTerm.
Include PCUICEnvironment.
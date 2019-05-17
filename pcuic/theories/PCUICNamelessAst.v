(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses Omega.
From Template Require Import config univ monad_utils utils BasicAst AstUtils
     UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICReflect PCUICTyping
     PCUICInduction.

(** * Namesless AST of PCUIC

    This is meant as an erasure of the usual AST.
    It is the effective quotient of term by eq_term.

    Another nicer solution would be to make name a parameter
    of term with two distinguished instances: string and unit.

*)

Section Nl.

Context `{checker_flags}.

Inductive nlterm : Set :=
| nlRel       : nat -> nlterm
| nlVar       : ident -> nlterm
| nlMeta      : nat -> nlterm
| nlEvar      : nat -> list nlterm -> nlterm
| nlSort      : universe -> nlterm
| nlProd      : nlterm -> nlterm -> nlterm
| nlLambda    : nlterm -> nlterm -> nlterm
| nlLetIn     : nlterm -> nlterm -> nlterm -> nlterm
| nlApp       : nlterm -> nlterm -> nlterm
| nlConst     : kername -> universe_instance -> nlterm
| nlInd       : inductive -> universe_instance -> nlterm
| nlConstruct : inductive -> nat -> universe_instance -> nlterm
| nlCase      : (inductive * nat) -> nlterm
               -> nlterm -> list (nat * nlterm) -> nlterm
| nlProj      : projection -> nlterm -> nlterm
| nlFix       : mfixpoint nlterm -> nat -> nlterm
| nlCoFix     : mfixpoint nlterm -> nat -> nlterm.

Fixpoint eq_nlterm (φ : uGraph.t) (u v : nlterm) : bool :=
  match u, v with
  | nlRel x, nlRel y => eqb x y
  | nlVar x, nlVar y => eqb x y
  | nlMeta x, nlMeta y => eqb x y
  | nlEvar n1 l1, nlEvar n2 l2 => eqb n1 n2 && forallb2 (eq_nlterm φ) l1 l2
  | nlSort s, nlSort z => eqb s z
  | nlProd A1 B1, nlProd A2 B2 => eq_nlterm φ A1 A2 && eq_nlterm φ B1 B2
  | nlLambda A1 b1, nlLambda A2 b2 => eq_nlterm φ A1 A2 && eq_nlterm φ b1 b2
  | nlLetIn b1 B1 t1, nlLetIn b2 B2 t2 =>
    eq_nlterm φ b1 b2 && eq_nlterm φ B1 B2 && eq_nlterm φ t1 t2
  | nlApp u1 v1, nlApp u2 v2 => eq_nlterm φ u1 u2 && eq_nlterm φ v1 v2
  | nlConst c1 u1, nlConst c2 u2 => eqb c1 c2 && eqb u1 u2
  | nlInd i1 u1, nlInd i2 u2 => eqb i1 i2 && eqb u1 u2
  | nlConstruct i1 n1 u1, nlConstruct i2 n2 u2 =>
    eqb i1 i2 && eqb n1 n2 && eqb u1 u2
  | nlCase i1 p1 c1 brs1, nlCase i2 p2 c2 brs2 =>
    eqb i1 i2 && eq_nlterm φ p1 p2 && eq_nlterm φ c1 c2 &&
    forallb2 (fun '(a, b) '(a', b') => eq_nlterm φ b b') brs1 brs2
  | nlProj p1 c1, nlProj p2 c2 => eqb p1 p2 && eq_nlterm φ c1 c2
  | nlFix mfix1 idx1, nlFix mfix2 idx2 =>
    forallb2 (fun x y =>
      eq_nlterm φ x.(dtype) y.(dtype) && eq_nlterm φ x.(dbody) y.(dbody)
    ) mfix1 mfix2 &&
    eqb idx1 idx2
  | nlCoFix mfix1 idx1, nlCoFix mfix2 idx2 =>
    forallb2 (fun x y =>
      eq_nlterm φ x.(dtype) y.(dtype) && eq_nlterm φ x.(dbody) y.(dbody)
    ) mfix1 mfix2 &&
    eqb idx1 idx2
  | _, _ => false
  end.

Local Ltac spec :=
  match goal with
  | |- context [ eqb ?x ?y ] =>
    destruct (eqb_spec x y) ; nodec
  end.

Local Ltac ok :=
  constructor ; easy.

Local Ltac ih :=
  match goal with
  | h : forall y, reflect (?u = _) (eq_nlterm _ _ _)
    |- context [ eq_nlterm _ ?u ?v ] =>
    destruct (h v) ; nodec
  end.

(* TODO To complete this we need an induction principle on nlterm *)
Instance reflect_nlterm : forall φ, ReflectEq nlterm := {
  eqb := eq_nlterm φ
}.
Proof.
  intros u. induction u ; intro v.
  all: destruct v ; try (right ; discriminate).
  all: try (cbn - [eqb] ; repeat spec ; repeat ih ; ok).
  - cbn - [eqb]. spec. admit.
  - cbn - [eqb] ; repeat spec ; repeat ih. admit.
  - admit.
  - admit.
Admitted.

(* Erasure map *)
Fixpoint nl (t : term) : nlterm :=
  match t with
  | tRel x => nlRel x
  | tVar x => nlVar x
  | tMeta x => nlMeta x
  | tEvar n l => nlEvar n (map nl l)
  | tSort u => nlSort u
  | tProd _ A B => nlProd (nl A) (nl B)
  | tLambda _ A b => nlLambda (nl A) (nl b)
  | tLetIn _ b B t => nlLetIn (nl b) (nl B) (nl t)
  | tApp u v => nlApp (nl u) (nl v)
  | tConst c u => nlConst c u
  | tInd i u => nlInd i u
  | tConstruct i n u => nlConstruct i n u
  | tCase i p c brs => nlCase i (nl p) (nl c) (map (on_snd nl) brs)
  | tProj p c => nlProj p (nl c)
  | tFix mfix idx => nlFix (map (map_def nl nl) mfix) idx
  | tCoFix mfix idx => nlCoFix (map (map_def nl nl) mfix) idx
  end.

(* Quotient property *)
Lemma eq_term_nl :
  forall φ u v,
    eq_term φ u v = true ->
    nl u = nl v.
Proof.
  intros φ u v h.
  (* destruct (eqb_spec (nl u) (nl v)). *)
  (* revert v h. *)
  (* induction u using term_forall_list_ind ; intros v h. *)
  (* all: destruct v ; try discriminate h. *)
  (* - cbn. cbn in h. *)

Abort.

(* Quotienting a relation *)
Definition nl__R (R : term -> term -> Prop) (u v : nlterm) : Prop :=
  exists u' v',
    nl u' = u /\ nl v' = v /\ R u' v'.

Lemma wf_nl__R :
  forall R,
    well_founded R ->
    well_founded (nl__R R).
Proof.
  intros R h u.
Abort.

End Nl.
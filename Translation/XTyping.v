From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SLiftSubst SCommon.

Reserved Notation " Σ ;;; Γ '|-x' t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ '|-x' t = u : T " (at level 50, Γ, t, u, T at next level).

Open Scope s_scope.

Inductive typing (Σ : sglobal_context) : scontext -> sterm -> sterm -> Type :=
| type_Rel Γ n :
    wf Σ Γ ->
    forall (isdecl : n < List.length Γ),
      Σ ;;; Γ |-x (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(sdecl_type)

| type_Sort Γ s :
    wf Σ Γ ->
    Σ ;;; Γ |-x (sSort s) : sSort (succ_sort s)

| type_Prod Γ n t b s1 s2 :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-x b : sSort s2 ->
    Σ ;;; Γ |-x (sProd n t b) : sSort (max_sort s1 s2)

| type_Lambda Γ n n' t b s1 s2 bty :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-x bty : sSort s2 ->
    Σ ;;; Γ ,, svass n t |-x b : bty ->
    Σ ;;; Γ |-x (sLambda n t bty b) : sProd n' t bty

| type_App Γ n s1 s2 t A B u :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-x B : sSort s2 ->
    Σ ;;; Γ |-x t : sProd n A B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x (sApp t n A B u) : B{ 0 := u }

| type_Eq Γ s A u v :
    Σ ;;; Γ |-x A : sSort s ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x v : A ->
    Σ ;;; Γ |-x sEq A u v : sSort s

| type_Refl Γ s A u :
    Σ ;;; Γ |-x A : sSort s ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sRefl A u : sEq A u u

| type_Ind Γ ind :
    wf Σ Γ ->
    forall univs decl (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
      Σ ;;; Γ |-x sInd ind : decl.(sind_type)

| type_Construct Γ ind i :
    wf Σ Γ ->
    forall univs decl (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
    Σ ;;; Γ |-x (sConstruct ind i)
             : stype_of_constructor (fst Σ) (ind, i) univs decl isdecl

| type_Case Γ ind npar p c brs args :
    forall decl (isdecl : sdeclared_minductive (fst Σ) (inductive_mind ind) decl),
    forall univs decl' (isdecl' : sdeclared_inductive (fst Σ) ind univs decl'),
    decl.(sind_npars) = npar ->
    let pars := List.firstn npar args in
    forall pty, Σ ;;; Γ |-x p : pty ->
    forall indctx inds pctx ps btys,
      stypes_of_case pars p pty decl' = Some (indctx, inds, pctx, ps, btys) ->
      scheck_correct_arity decl' ind indctx inds pars pctx = true ->
      (* List.Exists (fun sf => universe_family ps = sf) decl'.(ind_kelim) -> *)
      Σ ;;; Γ |-x c : Apps (sInd ind) indctx (sSort inds) args ->
      ForallT2 (fun x y => (fst x = fst y) * (Σ ;;; Γ |-x snd x : snd y)) brs btys ->
      Σ ;;; Γ |-x sCase (ind, npar) p c brs
               : Apps p pctx (sSort ps) (List.skipn npar args ++ [c])

| type_conv Γ t A B s :
    Σ ;;; Γ |-x t : A ->
    Σ ;;; Γ |-x B : sSort s ->
    Σ ;;; Γ |-x A = B : sSort s ->
    Σ ;;; Γ |-x t : B

where " Σ ;;; Γ '|-x' t : T " := (@typing Σ Γ t T) : x_scope

with wf (Σ : sglobal_context) : scontext -> Type :=
| wf_nil :
    wf Σ nil

| wf_snoc Γ x A s :
    wf Σ Γ ->
    Σ ;;; Γ |-x A : sSort s ->
    wf Σ (Γ ,, svass x A)

with eq_term (Σ : sglobal_context) : scontext -> sterm -> sterm -> sterm -> Type :=
| eq_reflexivity Γ u A :
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x u = u : A

| eq_symmetry Γ u v A :
    Σ ;;; Γ |-x u = v : A ->
    Σ ;;; Γ |-x v = u : A

| eq_transitivity Γ u v w A :
    Σ ;;; Γ |-x u = v : A ->
    Σ ;;; Γ |-x v = w : A ->
    Σ ;;; Γ |-x u = w : A

| eq_beta Γ s1 s2 n A B t u :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-x B : sSort s2 ->
    Σ ;;; Γ ,, svass n A |-x t : B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sApp (sLambda n A B t) n A B u = t{ 0 := u } : B{ 0 := u }

| eq_conv Γ s T1 T2 t1 t2 :
    Σ ;;; Γ |-x t1 = t2 : T1 ->
    Σ ;;; Γ |-x T1 = T2 : sSort s ->
    Σ ;;; Γ |-x t1 = t2 : T2

| cong_Prod Γ n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, svass n1 A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, svass n2 A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x (sProd n1 A1 B1) = (sProd n2 A2 B2) : sSort (max_sort s1 s2)

| cong_Lambda Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, svass n1 A1 |-x t1 = t2 : B1 ->
    Σ ;;; Γ ,, svass n1 A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, svass n2 A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ ,, svass n1 A1 |-x t1 : B1 ->
    Σ ;;; Γ ,, svass n2 A2 |-x t2 : B2 ->
    Σ ;;; Γ |-x (sLambda n1 A1 B1 t1) = (sLambda n2 A2 B2 t2) : sProd n' A1 B1

| cong_App Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-x t1 = t2 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ ,, svass n1 A1 |-x B1 : sSort s2 ->
    Σ ;;; Γ ,, svass n2 A2 |-x B2 : sSort s2 ->
    Σ ;;; Γ |-x t1 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-x t2 : sProd n2 A2 B2 ->
    Σ ;;; Γ |-x u1 : A1 ->
    Σ ;;; Γ |-x u2 : A2 ->
    Σ ;;; Γ |-x (sApp t1 n1 A1 B1 u1) = (sApp t2 n2 A2 B2 u2) : B1{ 0 := u1 }

| cong_Eq Γ s A1 A2 u1 u2 v1 v2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ |-x v1 = v2 : A1 ->
    Σ ;;; Γ |-x sEq A1 u1 v1 = sEq A2 u2 v2 : sSort s

| cong_Refl Γ s A1 A2 u1 u2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ |-x sRefl A1 u1 = sRefl A2 u2 : sEq A1 u1 u1

| cong_Case Γ ind npar p p' c c' brs brs' args :
    forall decl (isdecl : sdeclared_minductive (fst Σ) (inductive_mind ind) decl),
    forall univs decl' (isdecl' : sdeclared_inductive (fst Σ) ind univs decl'),
    decl.(sind_npars) = npar ->
    let pars := List.firstn npar args in
    forall pty, Σ ;;; Γ |-x p = p' : pty ->
    forall indctx inds pctx ps btys,
      stypes_of_case pars p pty decl' = Some (indctx, inds, pctx, ps, btys) ->
      scheck_correct_arity decl' ind indctx inds pars pctx = true ->
      (* List.Exists (fun sf => universe_family ps = sf) decl'.(ind_kelim) -> *)
      Σ ;;; Γ |-x c = c' : Apps (sInd ind) indctx (sSort inds) args ->
      ForallT3 (fun x y z => (fst x = fst y) * (fst y = fst z) * (Σ ;;; Γ |-x snd x = snd y : snd z)) brs brs' btys ->
      Σ ;;; Γ |-x sCase (ind, npar) p c brs
               = sCase (ind, npar) p' c' brs'
               : Apps p pctx (sSort ps) (List.skipn npar args ++ [c])

| reflection Γ A u v e :
    Σ ;;; Γ |-x e : sEq A u v ->
    Σ ;;; Γ |-x u = v : A

where " Σ ;;; Γ '|-x' t = u : T " := (@eq_term Σ Γ t u T) : x_scope.

Delimit Scope x_scope with x.

Open Scope x_scope.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-x t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

Scheme typing_ind' := Induction for typing Sort Type
  with wf_ind' := Induction for wf Sort Type
  with eq_term_ind' := Induction for eq_term Sort Type.

(* Combined Scheme typing_all from typing_ind , wf_ind , eq_term_ind. *)

Definition typing_all : forall (Σ : sglobal_context)
         (P0 : forall s : scontext, wf Σ s -> Type)
         (P : forall (s : scontext) (s0 s1 : sterm),
              Σ;;; s |-x s0 : s1 -> Type)
         (P1 : forall (s : scontext) (s0 s1 s2 : sterm),
               Σ;;; s |-x s0 = s1 : s2 -> Type),
       P0 [] (wf_nil Σ) ->
       (forall (Γ : scontext) (x : name) (A : sterm)
          (s : sort) (w : wf Σ Γ),
        P0 Γ w ->
        forall t : Σ;;; Γ |-x A : sSort s,
        P Γ A (sSort s) t ->
        P0 (Γ,, svass x A) (wf_snoc Σ Γ x A s w t))->
       (forall (Γ : scontext) (n : nat) (w : wf Σ Γ),
        P0 Γ w ->
        forall isdecl : n < #|Γ|,
        P Γ (sRel n)
          (lift0 (S n)
             (sdecl_type
                (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl))))
          (type_Rel Σ Γ n w isdecl)) ->
       (forall (Γ : scontext) (s : sort) (w : wf Σ Γ),
        P0 Γ w ->
        P Γ (sSort s) (sSort (succ_sort s)) (type_Sort Σ Γ s w)) ->
       (forall (Γ : scontext) (n : name) (t b : sterm)
          (s1 s2 : sort) (t0 : Σ;;; Γ |-x t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-x b : sSort s2,
        P (Γ,, svass n t) b (sSort s2) t1 ->
        P Γ (sProd n t b) (sSort (max_sort s1 s2))
          (type_Prod Σ Γ n t b s1 s2 t0 t1)) ->
       (forall (Γ : scontext) (n n' : name) (t b : sterm)
          (s1 s2 : sort) (bty : sterm) (t0 : Σ;;; Γ |-x t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-x bty : sSort s2,
        P (Γ,, svass n t) bty (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n t |-x b : bty,
        P (Γ,, svass n t) b bty t2 ->
        P Γ (sLambda n t bty b) (sProd n' t bty)
          (type_Lambda Σ Γ n n' t b s1 s2 bty t0 t1 t2)) ->
       (forall (Γ : scontext) (n : name) (s1 s2 : sort)
          (t A B u : sterm) (t0 : Σ;;; Γ |-x A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-x B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ |-x t : sProd n A B,
        P Γ t (sProd n A B) t2 ->
        forall t3 : Σ;;; Γ |-x u : A,
        P Γ u A t3 ->
        P Γ (sApp t n A B u) (B {0 := u})
          (type_App Σ Γ n s1 s2 t A B u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s : sort) (A u v : sterm)
          (t : Σ;;; Γ |-x A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-x u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-x v : A,
        P Γ v A t1 ->
        P Γ (sEq A u v) (sSort s) (type_Eq Σ Γ s A u v t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm)
          (t : Σ;;; Γ |-x A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-x u : A,
        P Γ u A t0 ->
        P Γ (sRefl A u) (sEq A u u) (type_Refl Σ Γ s A u t t0)) ->
       (forall (Γ : scontext) (ind : inductive) (w : wf Σ Γ),
        P0 Γ w ->
        forall univs decl (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
        P Γ (sInd ind) (decl.(sind_type)) (type_Ind Σ Γ ind w univs decl isdecl)) ->
       (forall (Γ : scontext) (ind : inductive) (i : nat) (w : wf Σ Γ),
        P0 Γ w ->
        forall univs decl (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
        P Γ (sConstruct ind i)
          (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl)
          (type_Construct Σ Γ ind i w univs decl isdecl)) ->
       (forall (Γ : scontext) (ind : inductive) (npar : nat) (p c : sterm) (brs : list (nat * sterm)) (args : list sterm)
          (decl : smutual_inductive_body) (isdecl : sdeclared_minductive (fst Σ) (inductive_mind ind) decl)
          (univs : universe_context) (decl' : sone_inductive_body) (isdecl' : sdeclared_inductive (fst Σ) ind univs decl')
          (e : sind_npars decl = npar),
        let pars := firstn npar args in
        forall (pty : sterm) (t : Σ;;; Γ |-x p : pty),
        P Γ p pty t ->
        forall (indctx : scontext) (inds : sort) (pctx : scontext) (ps : sort) (btys : list (nat * sterm))
          (e0 : stypes_of_case pars p pty decl' = Some (indctx, inds, pctx, ps, btys))
          (e1 : scheck_correct_arity decl' ind indctx inds pars pctx = true)
          (t0 : Σ;;; Γ |-x c : Apps (sInd ind) indctx (sSort inds) args),
        P Γ c (Apps (sInd ind) indctx (sSort inds) args) t0 ->
        forall f8 : ForallT2 (fun x y : nat * sterm => (fst x = fst y) * (Σ;;; Γ |-x snd x : snd y)) brs btys,
        P Γ (sCase (ind, npar) p c brs) (Apps p pctx (sSort ps) (skipn npar args ++ [c]))
          (type_Case Σ Γ ind npar p c brs args decl isdecl univs decl' isdecl' e pty t indctx inds pctx ps btys e0 e1 t0 f8)) ->
       (forall (Γ : scontext) (t A B : sterm) (s : sort)
          (t0 : Σ;;; Γ |-x t : A),
        P Γ t A t0 ->
        forall t1 : Σ;;; Γ |-x B : sSort s,
        P Γ B (sSort s) t1 ->
        forall e : Σ;;; Γ |-x A = B : sSort s,
        P1 Γ A B (sSort s) e ->
        P Γ t B (type_conv Σ Γ t A B s t0 t1 e)) ->
       (forall (Γ : scontext) (u A : sterm) (t : Σ;;; Γ |-x u : A),
        P Γ u A t -> P1 Γ u u A (eq_reflexivity Σ Γ u A t)) ->
       (forall (Γ : scontext) (u v A : sterm) (e : Σ;;; Γ |-x u = v : A),
        P1 Γ u v A e -> P1 Γ v u A (eq_symmetry Σ Γ u v A e)) ->
       (forall (Γ : scontext) (u v w A : sterm) (e : Σ;;; Γ |-x u = v : A),
        P1 Γ u v A e ->
        forall e0 : Σ;;; Γ |-x v = w : A,
        P1 Γ v w A e0 -> P1 Γ u w A (eq_transitivity Σ Γ u v w A e e0)) ->
       (forall (Γ : scontext) (s1 s2 : sort) (n : name)
          (A B t u : sterm) (t0 : Σ;;; Γ |-x A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-x B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n A |-x t : B,
        P (Γ,, svass n A) t B t2 ->
        forall t3 : Σ;;; Γ |-x u : A,
        P Γ u A t3 ->
        P1 Γ (sApp (sLambda n A B t) n A B u) (t {0 := u})
          (B {0 := u}) (eq_beta Σ Γ s1 s2 n A B t u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 t1 t2 : sterm)
          (e : Σ;;; Γ |-x t1 = t2 : T1),
        P1 Γ t1 t2 T1 e ->
        forall e0 : Σ;;; Γ |-x T1 = T2 : sSort s,
        P1 Γ T1 T2 (sSort s) e0 ->
        P1 Γ t1 t2 T2 (eq_conv Σ Γ s T1 T2 t1 t2 e e0)) ->
       (forall (Γ : scontext) (n1 n2 : name) (A1 A2 B1 B2 : sterm)
          (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall t : Σ;;; Γ,, svass n1 A1 |-x B1 : sSort s2,
        P (Γ,, svass n1 A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, svass n2 A2 |-x B2 : sSort s2,
        P (Γ,, svass n2 A2) B2 (sSort s2) t0 ->
        P1 Γ (sProd n1 A1 B1) (sProd n2 A2 B2) (sSort (max_sort s1 s2))
          (cong_Prod Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 e e0 t t0)) ->
       (forall (Γ : scontext) (n1 n2 n' : name) (A1 A2 B1 B2 t1 t2 : sterm)
          (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ,, svass n1 A1 |-x t1 = t2 : B1,
        P1 (Γ,, svass n1 A1) t1 t2 B1 e1 ->
        forall t : Σ;;; Γ,, svass n1 A1 |-x B1 : sSort s2,
        P (Γ,, svass n1 A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, svass n2 A2 |-x B2 : sSort s2,
        P (Γ,, svass n2 A2) B2 (sSort s2) t0 ->
        forall t3 : Σ;;; Γ,, svass n1 A1 |-x t1 : B1,
        P (Γ,, svass n1 A1) t1 B1 t3 ->
        forall t4 : Σ;;; Γ,, svass n2 A2 |-x t2 : B2,
        P (Γ,, svass n2 A2) t2 B2 t4 ->
        P1 Γ (sLambda n1 A1 B1 t1) (sLambda n2 A2 B2 t2)
          (sProd n' A1 B1)
          (cong_Lambda Σ Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 e e0 e1 t
             t0 t3 t4)) ->
       (forall (Γ : scontext) (n1 n2 : name) (s1 s2 : sort)
          (t1 t2 A1 A2 B1 B2 u1 u2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ |-x t1 = t2 : sProd n1 A1 B1,
        P1 Γ t1 t2 (sProd n1 A1 B1) e1 ->
        forall e2 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e2 ->
        forall t : Σ;;; Γ,, svass n1 A1 |-x B1 : sSort s2,
        P (Γ,, svass n1 A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, svass n2 A2 |-x B2 : sSort s2,
        P (Γ,, svass n2 A2) B2 (sSort s2) t0 ->
        forall t3 : Σ;;; Γ |-x t1 : sProd n1 A1 B1,
        P Γ t1 (sProd n1 A1 B1) t3 ->
        forall t4 : Σ;;; Γ |-x t2 : sProd n2 A2 B2,
        P Γ t2 (sProd n2 A2 B2) t4 ->
        forall t5 : Σ;;; Γ |-x u1 : A1,
        P Γ u1 A1 t5 ->
        forall t6 : Σ;;; Γ |-x u2 : A2,
        P Γ u2 A2 t6 ->
        P1 Γ (sApp t1 n1 A1 B1 u1) (sApp t2 n2 A2 B2 u2)
          (B1 {0 := u1})
          (cong_App Σ Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 e e0 e1 e2
             t t0 t3 t4 t5 t6)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        forall e1 : Σ;;; Γ |-x v1 = v2 : A1,
        P1 Γ v1 v2 A1 e1 ->
        P1 Γ (sEq A1 u1 v1) (sEq A2 u2 v2) (sSort s)
          (cong_Eq Σ Γ s A1 A2 u1 u2 v1 v2 e e0 e1)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        P1 Γ (sRefl A1 u1) (sRefl A2 u2) (sEq A1 u1 u1)
          (cong_Refl Σ Γ s A1 A2 u1 u2 e e0)) ->
       (forall (Γ : scontext) (ind : inductive) (npar : nat) (p p' c c' : sterm) (brs brs' : list (nat * sterm))
          (args : list sterm) (decl : smutual_inductive_body) (isdecl : sdeclared_minductive (fst Σ) (inductive_mind ind) decl)
          (univs : universe_context) (decl' : sone_inductive_body) (isdecl' : sdeclared_inductive (fst Σ) ind univs decl')
          (e : sind_npars decl = npar),
        let pars := firstn npar args in
        forall (pty : sterm) (e0 : Σ;;; Γ |-x p = p' : pty),
        P1 Γ p p' pty e0 ->
        forall (indctx : scontext) (inds : sort) (pctx : scontext) (ps : sort) (btys : list (nat * sterm))
          (e1 : stypes_of_case pars p pty decl' = Some (indctx, inds, pctx, ps, btys))
          (e2 : scheck_correct_arity decl' ind indctx inds pars pctx = true)
          (e3 : Σ;;; Γ |-x c = c' : Apps (sInd ind) indctx (sSort inds) args),
        P1 Γ c c' (Apps (sInd ind) indctx (sSort inds) args) e3 ->
        forall
          f9 : ForallT3 (fun x y z : nat * sterm => (fst x = fst y) * (fst y = fst z) * (Σ;;; Γ |-x snd x = snd y : snd z)) brs
                 brs' btys,
        P1 Γ (sCase (ind, npar) p c brs) (sCase (ind, npar) p' c' brs') (Apps p pctx (sSort ps) (skipn npar args ++ [c]))
          (cong_Case Σ Γ ind npar p p' c c' brs brs' args decl isdecl univs decl' isdecl' e pty e0 indctx inds pctx ps btys e1 e2
             e3 f9)) ->
       (forall (Γ : scontext) (A u v e : sterm) (t : Σ;;; Γ |-x e : sEq A u v),
        P Γ e (sEq A u v) t -> P1 Γ u v A (reflection Σ Γ A u v e t)) ->
       (forall (s : scontext) (w : wf Σ s), P0 s w) *
       (forall (s : scontext) (s0 s1 : sterm) (t : Σ;;; s |-x s0 : s1),
           P s s0 s1 t) *
       (forall (s : scontext) (s0 s1 s2 : sterm) (e : Σ;;; s |-x s0 = s1 : s2),
           P1 s s0 s1 s2 e).
Proof.
  intros; repeat split ; [
  eapply wf_ind' | eapply typing_ind' | eapply eq_term_ind' ]; eauto.
Defined.
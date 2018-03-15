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

Section ForallT2_size.

  Context {A} (P : A -> A -> Type) (fn : forall x1 x2, P x1 x2 -> size).

  Fixpoint forallt2_size {l1 l2 : list A} (f : ForallT2 P l1 l2) : size :=
    match f with
    | ForallT2_nil => 0
    | ForallT2_cons x y l l' rxy rll' => (fn _ _ rxy + forallt2_size rll')%nat
    end.

End ForallT2_size.

Definition typing_size {Σ Γ t T} (d : Σ ;;; Γ |-x t : T) : size.
Proof.
  revert Σ Γ t T d.
  fix 5.
  destruct 1 ;
  repeat match goal with
  | H : typing _ _ _ _ |- _ => apply typing_size in H
  end ;
  match goal with
  | H : ForallT2 _ _ _ |- _ => idtac
  | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
  | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
  | H1 : size |- _ => exact (S H1)
  | _ : sdeclared_inductive _ _ _ _ |- _ => exact 2
  | _ : sdeclared_constructor _ _ _ _ |- _ => exact 2
  | _ => exact 1
  end.
  exact (S (Nat.max d1 (Nat.max d2
     (forallt2_size _ (fun x y p => typing_size Σ Γ (snd x) (snd y) (snd p)) f)))).
Defined.

Scheme typing_ind' := Induction for typing Sort Type
  with wf_ind' := Induction for wf Sort Type
  with eq_term_ind' := Induction for eq_term Sort Type.

(* Combined Scheme typing_all from typing_ind , wf_ind , eq_term_ind. *)

Definition typing_all : forall (Σ : sglobal_context)
         (P0 : scontext -> Type)
         (P : forall (s : scontext) (s0 s1 : sterm), Type)
         (P1 : forall (s : scontext) (s0 s1 s2 : sterm), Type),
       P0 [] ->
       (forall (Γ : scontext) (x : name) (A : sterm)
          (s : sort) (w : wf Σ Γ),
        P0 Γ ->
        forall t : Σ;;; Γ |-x A : sSort s,
        P Γ A (sSort s) ->
        P0 (Γ,, svass x A)) ->
       (forall (Γ : scontext) (n : nat) (w : wf Σ Γ),
        P0 Γ ->
        forall isdecl : n < #|Γ|,
        P Γ (sRel n)
          (lift0 (S n)
             (sdecl_type
                (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl))))) ->
       (forall (Γ : scontext) (s : sort) (w : wf Σ Γ),
        P0 Γ ->
        P Γ (sSort s) (sSort (succ_sort s))) ->
       (forall (Γ : scontext) (n : name) (t b : sterm)
          (s1 s2 : sort) (t0 : Σ;;; Γ |-x t : sSort s1),
        P Γ t (sSort s1) ->
        forall t1 : Σ;;; Γ,, svass n t |-x b : sSort s2,
        P (Γ,, svass n t) b (sSort s2) ->
        P Γ (sProd n t b) (sSort (max_sort s1 s2))) ->
       (forall (Γ : scontext) (n n' : name) (t b : sterm)
          (s1 s2 : sort) (bty : sterm) (t0 : Σ;;; Γ |-x t : sSort s1),
        P Γ t (sSort s1) ->
        forall t1 : Σ;;; Γ,, svass n t |-x bty : sSort s2,
        P (Γ,, svass n t) bty (sSort s2) ->
        forall t2 : Σ;;; Γ,, svass n t |-x b : bty,
        P (Γ,, svass n t) b bty ->
        P Γ (sLambda n t bty b) (sProd n' t bty)) ->
       (forall (Γ : scontext) (n : name) (s1 s2 : sort)
          (t A B u : sterm) (t0 : Σ;;; Γ |-x A : sSort s1),
        P Γ A (sSort s1) ->
        forall t1 : Σ;;; Γ,, svass n A |-x B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) ->
        forall t2 : Σ;;; Γ |-x t : sProd n A B,
        P Γ t (sProd n A B) ->
        forall t3 : Σ;;; Γ |-x u : A,
        P Γ u A ->
        P Γ (sApp t n A B u) (B {0 := u})) ->
       (forall (Γ : scontext) (s : sort) (A u v : sterm)
          (t : Σ;;; Γ |-x A : sSort s),
        P Γ A (sSort s) ->
        forall t0 : Σ;;; Γ |-x u : A,
        P Γ u A ->
        forall t1 : Σ;;; Γ |-x v : A,
        P Γ v A ->
        P Γ (sEq A u v) (sSort s)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm)
          (t : Σ;;; Γ |-x A : sSort s),
        P Γ A (sSort s) ->
        forall t0 : Σ;;; Γ |-x u : A,
        P Γ u A ->
        P Γ (sRefl A u) (sEq A u u)) ->
       (forall (Γ : scontext) (ind : inductive) (w : wf Σ Γ),
        P0 Γ ->
        forall univs decl (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
        P Γ (sInd ind) (decl.(sind_type))) ->
       (forall (Γ : scontext) (ind : inductive) (i : nat) (w : wf Σ Γ),
        P0 Γ ->
        forall univs decl (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
        P Γ (sConstruct ind i)
          (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl)) ->
       (forall (Γ : scontext) (ind : inductive) (npar : nat) (p c : sterm) (brs : list (nat * sterm)) (args : list sterm)
          (decl : smutual_inductive_body) (isdecl : sdeclared_minductive (fst Σ) (inductive_mind ind) decl)
          (univs : universe_context) (decl' : sone_inductive_body) (isdecl' : sdeclared_inductive (fst Σ) ind univs decl')
          (e : sind_npars decl = npar),
        let pars := firstn npar args in
        forall (pty : sterm) (t : Σ;;; Γ |-x p : pty),
        P Γ p pty ->
        forall (indctx : scontext) (inds : sort) (pctx : scontext) (ps : sort) (btys : list (nat * sterm))
          (e0 : stypes_of_case pars p pty decl' = Some (indctx, inds, pctx, ps, btys))
          (e1 : scheck_correct_arity decl' ind indctx inds pars pctx = true)
          (t0 : Σ;;; Γ |-x c : Apps (sInd ind) indctx (sSort inds) args),
        P Γ c (Apps (sInd ind) indctx (sSort inds) args) ->
        forall f8 : ForallT2 (fun x y : nat * sterm => (fst x = fst y) * (Σ;;; Γ |-x snd x : snd y) * P Γ (snd x) (snd y)) brs btys,
        P Γ (sCase (ind, npar) p c brs) (Apps p pctx (sSort ps) (skipn npar args ++ [c]))) ->
       (forall (Γ : scontext) (t A B : sterm) (s : sort)
          (t0 : Σ;;; Γ |-x t : A),
        P Γ t A ->
        forall t1 : Σ;;; Γ |-x B : sSort s,
        P Γ B (sSort s) ->
        forall e : Σ;;; Γ |-x A = B : sSort s,
        P1 Γ A B (sSort s) ->
        P Γ t B) ->
       (forall (Γ : scontext) (u A : sterm) (t : Σ;;; Γ |-x u : A),
        P Γ u A -> P1 Γ u u A) ->
       (forall (Γ : scontext) (u v A : sterm) (e : Σ;;; Γ |-x u = v : A),
        P1 Γ u v A -> P1 Γ v u A) ->
       (forall (Γ : scontext) (u v w A : sterm) (e : Σ;;; Γ |-x u = v : A),
        P1 Γ u v A ->
        forall e0 : Σ;;; Γ |-x v = w : A,
        P1 Γ v w A -> P1 Γ u w A) ->
       (forall (Γ : scontext) (s1 s2 : sort) (n : name)
          (A B t u : sterm) (t0 : Σ;;; Γ |-x A : sSort s1),
        P Γ A (sSort s1) ->
        forall t1 : Σ;;; Γ,, svass n A |-x B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) ->
        forall t2 : Σ;;; Γ,, svass n A |-x t : B,
        P (Γ,, svass n A) t B ->
        forall t3 : Σ;;; Γ |-x u : A,
        P Γ u A ->
        P1 Γ (sApp (sLambda n A B t) n A B u) (t {0 := u})
          (B {0 := u})) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 t1 t2 : sterm)
          (e : Σ;;; Γ |-x t1 = t2 : T1),
        P1 Γ t1 t2 T1 ->
        forall e0 : Σ;;; Γ |-x T1 = T2 : sSort s,
        P1 Γ T1 T2 (sSort s) ->
        P1 Γ t1 t2 T2) ->
       (forall (Γ : scontext) (n1 n2 : name) (A1 A2 B1 B2 : sterm)
          (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) ->
        forall t : Σ;;; Γ,, svass n1 A1 |-x B1 : sSort s2,
        P (Γ,, svass n1 A1) B1 (sSort s2) ->
        forall t0 : Σ;;; Γ,, svass n2 A2 |-x B2 : sSort s2,
        P (Γ,, svass n2 A2) B2 (sSort s2) ->
        P1 Γ (sProd n1 A1 B1) (sProd n2 A2 B2) (sSort (max_sort s1 s2))) ->
       (forall (Γ : scontext) (n1 n2 n' : name) (A1 A2 B1 B2 t1 t2 : sterm)
          (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) ->
        forall e1 : Σ;;; Γ,, svass n1 A1 |-x t1 = t2 : B1,
        P1 (Γ,, svass n1 A1) t1 t2 B1 ->
        forall t : Σ;;; Γ,, svass n1 A1 |-x B1 : sSort s2,
        P (Γ,, svass n1 A1) B1 (sSort s2) ->
        forall t0 : Σ;;; Γ,, svass n2 A2 |-x B2 : sSort s2,
        P (Γ,, svass n2 A2) B2 (sSort s2) ->
        forall t3 : Σ;;; Γ,, svass n1 A1 |-x t1 : B1,
        P (Γ,, svass n1 A1) t1 B1 ->
        forall t4 : Σ;;; Γ,, svass n2 A2 |-x t2 : B2,
        P (Γ,, svass n2 A2) t2 B2 ->
        P1 Γ (sLambda n1 A1 B1 t1) (sLambda n2 A2 B2 t2)
          (sProd n' A1 B1)) ->
       (forall (Γ : scontext) (n1 n2 : name) (s1 s2 : sort)
          (t1 t2 A1 A2 B1 B2 u1 u2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) ->
        forall e1 : Σ;;; Γ |-x t1 = t2 : sProd n1 A1 B1,
        P1 Γ t1 t2 (sProd n1 A1 B1) ->
        forall e2 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 ->
        forall t : Σ;;; Γ,, svass n1 A1 |-x B1 : sSort s2,
        P (Γ,, svass n1 A1) B1 (sSort s2) ->
        forall t0 : Σ;;; Γ,, svass n2 A2 |-x B2 : sSort s2,
        P (Γ,, svass n2 A2) B2 (sSort s2) ->
        forall t3 : Σ;;; Γ |-x t1 : sProd n1 A1 B1,
        P Γ t1 (sProd n1 A1 B1) ->
        forall t4 : Σ;;; Γ |-x t2 : sProd n2 A2 B2,
        P Γ t2 (sProd n2 A2 B2) ->
        forall t5 : Σ;;; Γ |-x u1 : A1,
        P Γ u1 A1 ->
        forall t6 : Σ;;; Γ |-x u2 : A2,
        P Γ u2 A2 ->
        P1 Γ (sApp t1 n1 A1 B1 u1) (sApp t2 n2 A2 B2 u2)
          (B1 {0 := u1})) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) ->
        forall e0 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 ->
        forall e1 : Σ;;; Γ |-x v1 = v2 : A1,
        P1 Γ v1 v2 A1 ->
        P1 Γ (sEq A1 u1 v1) (sEq A2 u2 v2) (sSort s)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) ->
        forall e0 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 ->
        P1 Γ (sRefl A1 u1) (sRefl A2 u2) (sEq A1 u1 u1)) ->
       (forall (Γ : scontext) (ind : inductive) (npar : nat) (p p' c c' : sterm) (brs brs' : list (nat * sterm))
          (args : list sterm) (decl : smutual_inductive_body) (isdecl : sdeclared_minductive (fst Σ) (inductive_mind ind) decl)
          (univs : universe_context) (decl' : sone_inductive_body) (isdecl' : sdeclared_inductive (fst Σ) ind univs decl')
          (e : sind_npars decl = npar),
        let pars := firstn npar args in
        forall (pty : sterm) (e0 : Σ;;; Γ |-x p = p' : pty),
        P1 Γ p p' pty ->
        forall (indctx : scontext) (inds : sort) (pctx : scontext) (ps : sort) (btys : list (nat * sterm))
          (e1 : stypes_of_case pars p pty decl' = Some (indctx, inds, pctx, ps, btys))
          (e2 : scheck_correct_arity decl' ind indctx inds pars pctx = true)
          (e3 : Σ;;; Γ |-x c = c' : Apps (sInd ind) indctx (sSort inds) args),
        P1 Γ c c' (Apps (sInd ind) indctx (sSort inds) args) ->
        forall
          f9 : ForallT3 (fun x y z : nat * sterm => (fst x = fst y) * (fst y = fst z) * (Σ;;; Γ |-x snd x = snd y : snd z) * P1 Γ (snd x) (snd y) (snd z)) brs
                 brs' btys,
        P1 Γ (sCase (ind, npar) p c brs) (sCase (ind, npar) p' c' brs') (Apps p pctx (sSort ps) (skipn npar args ++ [c]))) ->
       (forall (Γ : scontext) (A u v e : sterm) (t : Σ;;; Γ |-x e : sEq A u v),
        P Γ e (sEq A u v) -> P1 Γ u v A) ->
       (forall (s : scontext) (w : wf Σ s), P0 s) *
       (forall (s : scontext) (s0 s1 : sterm) (t : Σ;;; s |-x s0 : s1),
           P s s0 s1) *
       (forall (s : scontext) (s0 s1 s2 : sterm) (e : Σ;;; s |-x s0 = s1 : s2),
           P1 s s0 s1 s2).
Proof.
  intros.
  repeat split ; [
    eapply wf_ind' with (P0 := fun Γ _ => P0 Γ)
                        (P := fun Γ t A _ => P Γ t A)
                        (P1 := fun Γ t1 t2 A _ => P1 Γ t1 t2 A)
  | eapply typing_ind' with (P0 := fun Γ _ => P0 Γ)
                        (P := fun Γ t A _ => P Γ t A)
                        (P1 := fun Γ t1 t2 A _ => P1 Γ t1 t2 A)
  | eapply eq_term_ind' with (P0 := fun Γ _ => P0 Γ)
                        (P := fun Γ t A _ => P Γ t A)
                        (P1 := fun Γ t1 t2 A _ => P1 Γ t1 t2 A)
  ] ; eauto.
  - intros. eapply X10. all: try eassumption.
    induction f.
    + constructor.
    + econstructor.
      * destruct r.
        repeat split ; try eassumption. admit.
      * apply IHf.


Abort.
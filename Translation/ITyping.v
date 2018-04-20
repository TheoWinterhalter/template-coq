From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SInduction SLiftSubst SCommon Conversion.

Open Scope s_scope.

(*! Typing *)

Reserved Notation " Σ ;;; Γ '|-i' t : T " (at level 50, Γ, t, T at next level).

Inductive typing (Σ : sglobal_context) : scontext -> sterm -> sterm -> Prop :=
| type_Rel Γ n :
    wf Σ Γ ->
    forall (isdecl : n < List.length Γ),
      Σ ;;; Γ |-i (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl))

| type_Sort Γ s :
    wf Σ Γ ->
    Σ ;;; Γ |-i (sSort s) : sSort (succ_sort s)

| type_Prod Γ n t b s1 s2 :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, t |-i b : sSort s2 ->
    Σ ;;; Γ |-i (sProd n t b) : sSort (max_sort s1 s2)

| type_Lambda Γ n n' t b s1 s2 bty :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, t |-i bty : sSort s2 ->
    Σ ;;; Γ ,, t |-i b : bty ->
    Σ ;;; Γ |-i (sLambda n t bty b) : sProd n' t bty

| type_App Γ n s1 s2 t A B u :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, A |-i B : sSort s2 ->
    Σ ;;; Γ |-i t : sProd n A B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i (sApp t A B u) : B{ 0 := u }

| type_Eq Γ s A u v :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEq A u v : sSort s

| type_Refl Γ s A u :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u

| type_J Γ s1 s2 A u v P p w :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ ,, A ,, (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2 ->
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i w : P{ 1 := u }{ 0 := sRefl A u } ->
    Σ ;;; Γ |-i sJ A u P w v p : P{ 1 := v }{ 0 := p }

| type_Transport Γ s T1 T2 p t :
    Σ ;;; Γ |-i T1 : sSort s ->
    Σ ;;; Γ |-i T2 : sSort s ->
    Σ ;;; Γ |-i p : sEq (sSort s) T1 T2 ->
    Σ ;;; Γ |-i t : T1 ->
    Σ ;;; Γ |-i sTransport T1 T2 p t : T2

| type_Heq Γ A a B b s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i sHeq A a B b : sSort s

| type_HeqToEq Γ A u v p s :
    Σ ;;; Γ |-i p : sHeq A u A v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sHeqToEq p : sEq A u v

| type_HeqRefl Γ A a s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i sHeqRefl A a : sHeq A a A a

| type_HeqSym Γ A a B b p s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i sHeqSym p : sHeq B b A a

| type_HeqTrans Γ A a B b C c p q s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i C : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i c : C ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i q : sHeq B b C c ->
    Σ ;;; Γ |-i sHeqTrans p q : sHeq A a C c

| type_HeqTransport Γ A B p t s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ ;;; Γ |-i sHeqTransport p t : sHeq A t B (sTransport A B p t)

| type_CongProd Γ s z nx ny A1 A2 B1 B2 pA pB :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (max_sort s z)) (sProd nx A1 B1)
         (sSort (max_sort s z)) (sProd ny A2 B2)

| type_CongLambda Γ s z nx ny A1 A2 B1 B2 t1 t2 pA pB pt :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ ,, A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2)

| type_CongApp Γ s z nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i u1 : sProd nx A1 B1 ->
    Σ ;;; Γ |-i u2 : sProd ny A2 B2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 A2 B2 v2)

| type_CongEq Γ s A1 A2 u1 u2 v1 v2 pA pu pv :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i u1 : A1 ->
    Σ ;;; Γ |-i u2 : A2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv :
               sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2)

| type_CongRefl Γ s A1 A2 u1 u2 pA pu :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i u1 : A1 ->
    Σ ;;; Γ |-i u2 : A2 ->
    Σ ;;; Γ |-i sCongRefl pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2)

| type_EqToHeq Γ A u v p s :
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEqToHeq p : sHeq A u A v

| type_HeqTypeEq Γ A u B v p s :
    Σ ;;; Γ |-i p : sHeq A u B v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B ->
    Σ ;;; Γ |-i sHeqTypeEq A B p : sEq (sSort s) A B

| type_Pack Γ A1 A2 s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i sPack A1 A2 : sSort s

| type_ProjT1 Γ A1 A2 p s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT1 p : A1

| type_ProjT2 Γ A1 A2 p s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT2 p : A2

| type_ProjTe Γ A1 A2 p s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjTe p : sHeq A1 (sProjT1 p) A2 (sProjT2 p)

| type_Ind Γ ind :
    wf Σ Γ ->
    forall univs decl (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
      Σ ;;; Γ |-i sInd ind : decl.(sind_type)

| type_Construct Γ ind i :
    wf Σ Γ ->
    forall univs decl (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
    Σ ;;; Γ |-i (sConstruct ind i)
             : stype_of_constructor (fst Σ) (ind, i) univs decl isdecl

| type_conv Γ t A B s :
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ |-i A = B ->
    Σ ;;; Γ |-i t : B

where " Σ ;;; Γ '|-i' t : T " := (@typing Σ Γ t T) : i_scope

with wf (Σ : sglobal_context) : scontext -> Prop :=
| wf_nil :
    wf Σ nil

| wf_snoc s Γ A :
    wf Σ Γ ->
    Σ ;;; Γ |-i A : sSort s ->
    wf Σ (Γ ,, A)
.

Derive Signature for typing.
Derive Signature for wf.

Delimit Scope i_scope with i.

(* We define the notion of ETT compatibility to restrict the syntax
   to the one that is allowed in ETT.
 *)
Inductive Xcomp : sterm -> Type :=
| xcomp_Rel n : Xcomp (sRel n)
| xcomp_Sort s : Xcomp (sSort s)
| xcomp_Prod na A B :
    Xcomp A ->
    Xcomp B ->
    Xcomp (sProd na A B)
| xcomp_Lambda na A B t :
    Xcomp A ->
    Xcomp B ->
    Xcomp t ->
    Xcomp (sLambda na A B t)
| xcomp_App u A B v :
    Xcomp u ->
    Xcomp A ->
    Xcomp B ->
    Xcomp v ->
    Xcomp (sApp u A B v)
| xcomp_Eq A u v :
    Xcomp A ->
    Xcomp u ->
    Xcomp v ->
    Xcomp (sEq A u v)
| xcomp_Refl A u :
    Xcomp A ->
    Xcomp u ->
    Xcomp (sRefl A u)
| xcomp_Ind ind : Xcomp (sInd ind)
| xcomp_Construct ind i : Xcomp (sConstruct ind i)
.

Derive Signature for Xcomp.

Definition isType Σ Γ A :=
  exists s, Σ ;;; Γ |-i A : sSort s.

Inductive type_constructors (Σ : sglobal_context) (Γ : scontext) :
  list (ident * sterm * nat) -> Type :=
| type_cnstrs_nil : type_constructors Σ Γ []
| type_cnstrs_cons id t n l :
    isType Σ Γ t ->
    Xcomp t ->
    type_constructors Σ Γ l ->
    (** TODO: check it has n products ending in a tRel application *)
    type_constructors Σ Γ ((id, t, n) :: l).

Inductive type_projections (Σ : sglobal_context) (Γ : scontext) :
  list (ident * sterm) -> Type :=
| type_projs_nil : type_projections Σ Γ []
| type_projs_cons id t l :
    isType Σ Γ t ->
    Xcomp t ->
    type_projections Σ Γ l ->
    type_projections Σ Γ ((id, t) :: l).

Definition arities_context (l : list sone_inductive_body) : scontext :=
  rev_map (fun ind => ind.(sind_type)) l.

Definition isArity Σ Γ T :=
  isType Σ Γ T (* FIXME  /\ decompose_prod_n *).

Inductive type_inddecls (Σ : sglobal_context) (pars : scontext) (Γ : scontext) :
  list sone_inductive_body -> Type :=
| type_ind_nil : type_inddecls Σ pars Γ []
| type_ind_cons na ty cstrs projs kelim l :
    (** Arity is well-formed *)
    isArity Σ [] ty ->
    (** TMP: The type can be written in ETT *)
    Xcomp ty ->
    (** Constructors are well-typed *)
    type_constructors Σ Γ cstrs ->
    (** Projections are well-typed *)
    type_projections Σ (Γ ,,, pars ,, ty) projs ->
    (** The other inductives in the block are well-typed *)
    type_inddecls Σ pars Γ l ->
    (** TODO: check kelim*)
    type_inddecls Σ pars Γ (Build_sone_inductive_body na ty kelim cstrs projs :: l).

Definition type_inductive Σ pars inds :=
  wf Σ pars *
  ForallT Xcomp pars *
  (** FIXME: should be pars ++ arities w/o params *)
  (* I don't know if it still should be fixed.
     To be honest, I believe ind_type and the types of constructors
     in the declaration should be in the context of parameters.
     For now, we'll do as TemplateCoq.
   *)
  type_inddecls Σ pars (arities_context inds) inds.

Definition type_global_decl Σ decl : Type :=
  match decl with  (* TODO universes *)
  | SConstantDecl id d => (* type_constant_decl Σ d *) ()
  | SInductiveDecl ind inds =>
    type_inductive Σ (nlctx inds.(sind_params)) inds.(sind_bodies)
  end.

Inductive fresh_global (s : string) : sglobal_declarations -> Prop :=
| fresh_global_nil : fresh_global s nil
| fresh_global_cons env g :
    fresh_global s env -> sglobal_decl_ident g <> s ->
    fresh_global s (cons g env).

Derive Signature for fresh_global.

Inductive type_global_env φ : sglobal_declarations -> Type :=
| globenv_nil : type_global_env φ []
| globenv_decl Σ d :
    type_global_env φ Σ ->
    fresh_global (sglobal_decl_ident d) Σ ->
    type_global_decl (Σ, φ) d ->
    type_global_env φ (d :: Σ).

Derive Signature for type_global_env.

Definition type_glob (Σ : sglobal_context) : Type :=
  type_global_env (snd Σ) (fst Σ).





Inductive typed_list Σ Γ : list sterm -> scontext -> Prop :=
| typed_list_nil : typed_list Σ Γ [] []
| typed_list_cons A l Δ T :
    typed_list Σ Γ l Δ ->
    Σ ;;; Γ ,,, Δ |-i A : T ->
    typed_list Σ Γ (A :: l) (Δ ,, T).

Derive Signature for typed_list.
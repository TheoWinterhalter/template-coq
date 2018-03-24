From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SLiftSubst SCommon.

Open Scope s_scope.

(*! Reduction. *)

(** NOTE: Do we need to switch to n-ary application? *)

(* TODO in branch case with Apps *)
(* Definition iota_red npar c args brs := *)
(*   (mkApps (snd (List.nth c brs (0, tRel 0))) (List.skipn npar args)). *)

Inductive red1 (Σ : sglobal_declarations) (Γ : scontext) : sterm -> sterm -> Prop :=
(*! Computation *)

(** β *)
| red_beta n A B t u :
    red1 Σ Γ (sApp (sLambda n A B t) n A B u) (t{ 0 := u })

(** Case TODO *)
(* | red_iota ind pars c args p brs : *)
(*     red1 Σ Γ (sCase (ind, pars) p (Apps (sConstruct ind c) _ _ args) brs) *)
(*          (iota_red pars c args brs) *)

(*! Subterm reduction *)

(** Lambda *)
| abs_red_dom na A A' B t :
    red1 Σ Γ A A' ->
    red1 Σ Γ (sLambda na A B t) (sLambda na A' B t)

| abs_red_codom na A B B' t :
    red1 Σ (Γ,, svass na A) B B' ->
    red1 Σ Γ (sLambda na A B t) (sLambda na A B' t)

| abs_red_body na A B t t' :
    red1 Σ (Γ,, svass na A) t t' ->
    red1 Σ Γ (sLambda na A B t) (sLambda na A B t')

(** Case *)
| case_red_discr ind p c c' brs :
    red1 Σ Γ c c' ->
    red1 Σ Γ (sCase ind p c brs) (sCase ind p c' brs)

| case_red_brs ind p c brs brs' :
    redbrs1 Σ Γ brs brs' ->
    red1 Σ Γ (sCase ind p c brs) (sCase ind p c brs')

(** App *)
| app_red_fun u u' na A B v :
    red1 Σ Γ u u' ->
    red1 Σ Γ (sApp u na A B v) (sApp u' na A B v)

| app_red_dom u na A A' B v :
    red1 Σ Γ A A' ->
    red1 Σ Γ (sApp u na A B v) (sApp u na A' B v)

| app_red_codom u na A B B' v :
    red1 Σ (Γ,, svass na A) B B' ->
    red1 Σ Γ (sApp u na A B v) (sApp u na A B' v)

| app_red_arg u na A B v v' :
    red1 Σ Γ v v' ->
    red1 Σ Γ (sApp u na A B v) (sApp u na A B v')

(** Prod *)
| prod_red_l na na' A A' B :
    red1 Σ Γ A A' ->
    red1 Σ Γ (sProd na A B) (sProd na' A' B)

| prod_red_r na na' A B B' :
    red1 Σ (Γ,, svass na A) B B' ->
    red1 Σ Γ (sProd na A B) (sProd na' A B')

(* TODO: The other terms that we added, plus the corresponding computations. *)

with redbrs1 (Σ : sglobal_declarations) (Γ : scontext) :
       list (nat * sterm) -> list (nat * sterm) -> Prop :=
| redbrs1_hd n hd hd' tl :
    red1 Σ Γ hd hd' ->
    redbrs1 Σ Γ ((n, hd) :: tl) ((n, hd') :: tl)
| redbrs1_tl hd tl tl' :
    redbrs1 Σ Γ tl tl' ->
    redbrs1 Σ Γ (hd :: tl) (hd :: tl')
.

(* Reflexive and transitive closure of 1-step reduction. *)
Inductive red Σ Γ t : sterm -> Prop :=
| refl_red : red Σ Γ t t
| trans_red u v : red Σ Γ t u -> red1 Σ Γ u v -> red Σ Γ t v.

(* TODO Pull eq_term from case branch, it will probably remain in SCommon *)

(*! Conversion *)

Reserved Notation " Σ ;;; Γ '|-i' t <= u " (at level 50, Γ, t, u at next level).

Inductive cumul (Σ : sglobal_context) (Γ : scontext) : sterm -> sterm -> Prop :=
| cumul_refl t u : eq_term t u = true -> Σ ;;; Γ |-i t <= u
| cumul_red_l t u v : red1 (fst Σ) Γ t v -> Σ ;;; Γ |-i v <= u -> Σ ;;; Γ |-i t <= u
| cumul_red_r t u v : Σ ;;; Γ |-i t <= v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |-i t <= u

where " Σ ;;; Γ '|-i' t <= u " := (@cumul Σ Γ t u) : i_scope.

Open Scope i_scope.

Definition conv Σ Γ T U :=
  Σ ;;; Γ |-i T <= U /\ Σ ;;; Γ |-i U <= T.

Notation " Σ ;;; Γ |-i t = u " :=
  (@conv Σ Γ t u) (at level 50, Γ, t, u at next level) : i_scope.

(*! Typing *)

Reserved Notation " Σ ;;; Γ '|-i' t : T " (at level 50, Γ, t, T at next level).

Inductive typing (Σ : sglobal_context) : scontext -> sterm -> sterm -> Type :=
| type_Rel Γ n :
    wf Σ Γ ->
    forall (isdecl : n < List.length Γ),
      Σ ;;; Γ |-i (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(sdecl_type)

| type_Sort Γ s :
    wf Σ Γ ->
    Σ ;;; Γ |-i (sSort s) : sSort (succ_sort s)

| type_Prod Γ n t b s1 s2 :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-i b : sSort s2 ->
    Σ ;;; Γ |-i (sProd n t b) : sSort (max_sort s1 s2)

| type_Lambda Γ n n' t b s1 s2 bty :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-i bty : sSort s2 ->
    Σ ;;; Γ ,, svass n t |-i b : bty ->
    Σ ;;; Γ |-i (sLambda n t bty b) : sProd n' t bty

| type_App Γ n s1 s2 t A B u :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-i B : sSort s2 ->
    Σ ;;; Γ |-i t : sProd n A B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i (sApp t n A B u) : B{ 0 := u }

| type_Eq Γ s A u v :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEq A u v : sSort s

| type_Refl Γ s A u :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u

| type_J Γ nx ne s1 s2 A u v P p w :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ ,, svass nx A ,, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2 ->
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
    Σ ;;; Γ |-i sHeq A a B b : sSort (succ_sort s)

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

| type_CongProd Γ s z nx ny np A1 A2 B1 B2 pA pB :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (max_sort s z)) (sProd nx A1 B1)
         (sSort (max_sort s z)) (sProd ny A2 B2)

| type_CongLambda Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ ,, svass nx A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, svass ny A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2)

| type_CongApp Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i u1 : sProd nx A1 B1 ->
    Σ ;;; Γ |-i u2 : sProd ny A2 B2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 ny A2 B2 v2)

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
    Σ ;;; Γ |-i sHeqTypeEq p : sEq (sSort s) A B

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
    Σ ;;; Γ |-i A = B ->
    Σ ;;; Γ |-i t : B

where " Σ ;;; Γ '|-i' t : T " := (@typing Σ Γ t T) : i_scope

with wf (Σ : sglobal_context) : scontext -> Type :=
| wf_nil :
    wf Σ nil

| wf_snoc s Γ x A :
    wf Σ Γ ->
    Σ ;;; Γ |-i A : sSort s ->
    wf Σ (Γ ,, svass x A)
.

(* | eq_JRefl Γ nx ne s1 s2 A u P w : *)
(*     Σ ;;; Γ |-i A : sSort s1 -> *)
(*     Σ ;;; Γ |-i u : A -> *)
(*     Σ ;;; Γ ,, svass nx A ,, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2 -> *)
(*     Σ ;;; Γ |-i w : P{ 1 := u }{ 0 := sRefl A u } -> *)
(*     Σ ;;; Γ |-i sJ A u P w u (sRefl A u) = w : P{ 1 := u }{ 0 := sRefl A u } *)

(* | eq_TransportRefl Γ s A t : *)
(*     Σ ;;; Γ |-i A : sSort s -> *)
(*     Σ ;;; Γ |-i t : A -> *)
(*     Σ ;;; Γ |-i sTransport A A (sRefl (sSort s) A) t = t : A *)

(* | eq_HeqToEqRefl Γ s A u : *)
(*     Σ ;;; Γ |-i A : sSort s -> *)
(*     Σ ;;; Γ |-i u : A -> *)
(*     Σ ;;; Γ |-i sHeqToEq (sHeqRefl A u) = sRefl A u : sEq A u u *)

Derive Signature for typing.
Derive Signature for wf.

Delimit Scope i_scope with i.

(* Temporary:
   We define the notion of ETT compatibility to restrict the syntax
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
| xcomp_App u na A B v :
    Xcomp u ->
    Xcomp A ->
    Xcomp B ->
    Xcomp v ->
    Xcomp (sApp u na A B v)
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

Definition isType (Σ : sglobal_context) (Γ : scontext) (t : sterm) :=
  ∑ s, Σ ;;; Γ |-i t : sSort s.

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

Definition rev {A} (l : list A) : list A :=
  let fix aux (l : list A) (acc : list A) : list A :=
    match l with
    | [] => acc
    | x :: l => aux l (x :: acc)
    end
  in aux l [].

Definition rev_map {A B} (f : A -> B) (l : list A) : list B :=
  let fix aux (l : list A) (acc : list B) : list B :=
    match l with
    | [] => acc
    | x :: l => aux l (f x :: acc)
    end
  in aux l [].

Definition arities_context (l : list sone_inductive_body) :=
  rev_map (fun ind => svass (nNamed ind.(sind_name)) ind.(sind_type)) l.

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
    type_projections Σ (Γ ,,, pars ,, svass nAnon ty) projs ->
    (** The other inductives in the block are well-typed *)
    type_inddecls Σ pars Γ l ->
    (** TODO: check kelim*)
    type_inddecls Σ pars Γ (Build_sone_inductive_body na ty kelim cstrs projs :: l).

Definition type_inductive Σ inds :=
  (** FIXME: should be pars ++ arities w/o params *)
  type_inddecls Σ [] (arities_context inds) inds.

Definition type_global_decl Σ decl : Type :=
  match decl with  (* TODO universes *)
  | SConstantDecl id d => (* type_constant_decl Σ d *) ()
  | SInductiveDecl ind inds => type_inductive Σ inds.(sind_bodies)
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
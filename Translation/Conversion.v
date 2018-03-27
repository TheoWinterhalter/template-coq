From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SInduction SLiftSubst SCommon.

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

(** J-Refl *)
| red_JRefl A u P w v A' u' :
    red1 Σ Γ (sJ A u P w v (sRefl A' u')) w

(** Transport of Refl *)
| red_TransportRefl A A' A'' T t :
    red1 Σ Γ (sTransport A A' (sRefl T A'') t) t

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

(** Eq *)
| eq_red_ty A A' u v :
    red1 Σ Γ A A' ->
    red1 Σ Γ (sEq A u v) (sEq A' u v)

| eq_red_l A u u' v :
    red1 Σ Γ u u' ->
    red1 Σ Γ (sEq A u v) (sEq A u' v)

| eq_red_r A u v v' :
    red1 Σ Γ v v' ->
    red1 Σ Γ (sEq A u v) (sEq A u v')

(** Refl *)
| refl_red_ty A A' u :
    red1 Σ Γ A A' ->
    red1 Σ Γ (sRefl A u) (sRefl A' u)

| refl_red_tm A u u' :
    red1 Σ Γ u u' ->
    red1 Σ Γ (sRefl A u) (sRefl A u')

(** J *)
| j_red_ty A A' u v P p w :
    red1 Σ Γ A A' ->
    red1 Σ Γ (sJ A u P w v p) (sJ A' u P w v p)

| j_red_l A u u' v P p w :
    red1 Σ Γ u u' ->
    red1 Σ Γ (sJ A u P w v p) (sJ A u' P w v p)

| j_red_pred A u v P P' p w nx ne :
    red1 Σ (Γ,, svass nx A ,, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)))
         P P' ->
    red1 Σ Γ (sJ A u P w v p) (sJ A u P' w v p)

| j_red_prf A u v P p w w' :
    red1 Σ Γ w w' ->
    red1 Σ Γ (sJ A u P w v p) (sJ A u P w' v p)

| j_red_r A u v v' P p w :
    red1 Σ Γ v v' ->
    red1 Σ Γ (sJ A u P w v p) (sJ A u P w v' p)

| j_red_eq A u v P p p' w :
    red1 Σ Γ p p' ->
    red1 Σ Γ (sJ A u P w v p) (sJ A u P w v p')

(** Transport *)
| transport_red_ty_l A A' B p t :
    red1 Σ Γ A A' ->
    red1 Σ Γ (sTransport A B p t) (sTransport A' B p t)

| transport_red_ty_r A B B' p t :
    red1 Σ Γ B B' ->
    red1 Σ Γ (sTransport A B p t) (sTransport A B' p t)

| transport_red_eq A B p p' t :
    red1 Σ Γ p p' ->
    red1 Σ Γ (sTransport A B p t) (sTransport A B p' t)

| transport_red_tm A B p t t' :
    red1 Σ Γ t t' ->
    red1 Σ Γ (sTransport A B p t) (sTransport A B p t')

(** Heq *)
| heq_red_ty_l A A' a B b :
    red1 Σ Γ A A' ->
    red1 Σ Γ (sHeq A a B b) (sHeq A' a B b)

| heq_red_tm_l A a a' B b :
    red1 Σ Γ a a' ->
    red1 Σ Γ (sHeq A a B b) (sHeq A a' B b)

| heq_red_ty_r A a B B' b :
    red1 Σ Γ B B' ->
    red1 Σ Γ (sHeq A a B b) (sHeq A a B' b)

| heq_red_tm_r A a B b b' :
    red1 Σ Γ b b' ->
    red1 Σ Γ (sHeq A a B b) (sHeq A a B b')

(** HeqToEq *)
| heqtoeq_red p p' :
    red1 Σ Γ p p' ->
    red1 Σ Γ (sHeqToEq p) (sHeqToEq p')

(** HeqRefl *)
| heqrefl_red_ty A A' a :
    red1 Σ Γ A A' ->
    red1 Σ Γ (sHeqRefl A a) (sHeqRefl A' a)

| heqrefl_red_tm A a a' :
    red1 Σ Γ a a' ->
    red1 Σ Γ (sHeqRefl A a) (sHeqRefl A a')

(** HeqSym *)
| heqsym_red p p' :
    red1 Σ Γ p p' ->
    red1 Σ Γ (sHeqSym p) (sHeqSym p')

(** HeqTrans *)
| heqtrans_red_l p p' q :
    red1 Σ Γ p p' ->
    red1 Σ Γ (sHeqTrans p q) (sHeqTrans p' q)

| heqtrans_red_r p q q' :
    red1 Σ Γ q q' ->
    red1 Σ Γ (sHeqTrans p q) (sHeqTrans p q')

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

(*! Conversion *)

Reserved Notation " Σ ;;; Γ '|-i' t = u " (at level 50, Γ, t, u at next level).

Inductive conv (Σ : sglobal_context) (Γ : scontext) : sterm -> sterm -> Prop :=
| conv_eq t u : eq_term t u = true -> Σ ;;; Γ |-i t = u
| conv_red_l t u v : red1 (fst Σ) Γ t v -> Σ ;;; Γ |-i v = u -> Σ ;;; Γ |-i t = u
| conv_red_r t u v : Σ ;;; Γ |-i t = v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |-i t = u

where " Σ ;;; Γ '|-i' t = u " := (@conv Σ Γ t u) : i_scope.

Derive Signature for conv.

Open Scope i_scope.

Lemma conv_refl :
  forall Σ Γ t, Σ ;;; Γ |-i t = t.
Proof.
  intros Σ Γ t.
  apply conv_eq. apply eq_term_refl.
Defined.

Lemma conv_sym :
  forall {Σ Γ t u},
    Σ ;;; Γ |-i t = u ->
    Σ ;;; Γ |-i u = t.
Proof.
  intros Σ Γ t u h.
  induction h.
  - admit.
  - eapply conv_red_r ; eassumption.
  - eapply conv_red_l ; eassumption.
Admitted.

Lemma conv_trans :
  forall {Σ Γ t u v},
    Σ ;;; Γ |-i t = u ->
    Σ ;;; Γ |-i u = v ->
    Σ ;;; Γ |-i t = v.
Proof.
  intros Σ Γ t u v h1 h2.
  revert v h2. induction h1 ; intros w h2.
  - admit.
  - specialize (IHh1 _ h2). eapply conv_red_l ; eassumption.
  - admit.
Admitted.


(*! Inversion results about conversion *)

Lemma sort_conv :
  forall {Σ Γ s1 s2},
    Σ ;;; Γ |-i sSort s1 = sSort s2 ->
    s1 = s2.
Proof.
  intros Σ Γ s1 s2 h. dependent induction h.
  - cbn in H. unfold eq_nat in H. bprop H. assumption.
  - inversion H.
  - inversion H.
Defined.

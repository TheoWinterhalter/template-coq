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

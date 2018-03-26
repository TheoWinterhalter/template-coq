(* Inversion lemmata *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SLiftSubst SCommon ITyping.

Lemma inversionRel :
  forall {Σ Γ n T},
    Σ ;;; Γ |-i sRel n : T ->
    ∑ isdecl,
      let A := lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(sdecl_type) in
      Σ ;;; Γ |-i A = T.
Proof.
  intros Σ Γ n T h. dependent induction h.
  - exists isdecl. apply conv_refl.
  - destruct IHh1 as [isdecl h].
    exists isdecl. eapply conv_trans ; eassumption.
Defined.

Lemma inversionSort :
  forall {Σ Γ s T},
    Σ ;;; Γ |-i sSort s : T ->
    Σ ;;; Γ |-i sSort (succ_sort s) = T.
Proof.
  intros Σ Γ s T h.
  dependent induction h.
  - apply conv_refl.
  - eapply conv_trans ; eassumption.
Defined.

Lemma inversionInd :
  forall {Σ Γ ind T},
    Σ ;;; Γ |-i sInd ind : T ->
    ∑ univs decl (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
      Σ ;;; Γ |-i decl.(sind_type) = T.
Proof.
  intros Σ Γ ind T h.
  dependent induction h.
  - exists univs, decl, isdecl. apply conv_refl.
  - destruct IHh1 as (univs & decl & isdecl & ?).
    exists univs, decl, isdecl. eapply conv_trans ; eassumption.
Defined.

Lemma inversionConstruct :
  forall {Σ Γ ind i T},
    Σ ;;; Γ |-i sConstruct ind i : T ->
    ∑ univs decl (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
      Σ ;;; Γ |-i stype_of_constructor (fst Σ) (ind, i) univs decl isdecl = T.
Proof.
  intros Σ Γ ind i T h.
  dependent induction h.
  - exists univs, decl, isdecl. apply conv_refl.
  - destruct IHh1 as (univs & decl & isdecl & ?).
    exists univs, decl, isdecl. eapply conv_trans ; eassumption.
Defined.

Lemma inversionProd :
  forall {Σ Γ n A B T},
    Σ ;;; Γ |-i sProd n A B : T ->
    ∑ s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ ,, svass n A |-i B : sSort s2) *
      (Σ ;;; Γ |-i sSort (max_sort s1 s2) = T).
Proof.
  intros Σ Γ n A B T h.
  dependent induction h.
  - exists s1, s2. split ; [ split | ..] ; try assumption. apply conv_refl.
  - destruct IHh1 as [s1 [s2 [[? ?] ?]]].
    exists s1, s2. split ; [ split | ..] ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionLambda :
  forall {Σ Γ na A B t T},
    Σ ;;; Γ |-i sLambda na A B t : T ->
      ∑ s1 s2,
        (Σ ;;; Γ |-i A : sSort s1) *
        (Σ ;;; Γ ,, svass na A |-i B : sSort s2) *
        (Σ ;;; Γ ,, svass na A |-i t : B) *
        (Σ ;;; Γ |-i sProd na A B = T).
Proof.
  intros Σ Γ na A B t T h.
  dependent induction h.
  - exists s1, s2. split ; [ split ; [ split | .. ] | ..] ; try assumption.
    split.
    + apply cumul_refl. cbn. rewrite !eq_term_refl. reflexivity.
    + apply cumul_refl. cbn. rewrite !eq_term_refl. reflexivity.
  - destruct IHh1 as [s1 [s2 [[[? ?] ?] ?]]].
    exists s1, s2. split ; [ split ; [ split | .. ] | ..] ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionApp :
  forall {Σ Γ t n A B u T},
    Σ ;;; Γ |-i sApp t n A B u : T ->
    ∑ s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ ,, svass n A |-i B : sSort s2) *
      (Σ ;;; Γ |-i t : sProd n A B) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i B{ 0 := u } = T).
Proof.
  intros Σ Γ t n A B u T h.
  dependent induction h.
  - exists s1, s2. split ; [ split ; [ split ; [ split |] |] |] ; try assumption.
    apply conv_refl.
  - destruct IHh1 as [s1 [s2 [[[[? ?] ?] ?] ?]]].
    exists s1, s2. split ; [ split ; [ split ; [ split |] |] |] ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionEq :
  forall {Σ Γ A u v T},
    Σ ;;; Γ |-i sEq A u v : T ->
    ∑ s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i v : A) *
      (Σ ;;; Γ |-i sSort s = T).
Proof.
  intros Σ Γ A u v T h.
  dependent induction h.
  - exists s. split ; [ split ; [ split |] |] ; try assumption.
    apply conv_refl.
  - destruct IHh1 as [s' [[[? ?] ?] ?]].
    exists s'. split ; [ split ; [ split |] |] ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionRefl :
  forall {Σ Γ A u T},
    Σ ;;; Γ |-i sRefl A u : T ->
    ∑ s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i sEq A u u = T).
Proof.
  intros Σ Γ A u T h.
  dependent induction h.
  - exists s. split ; [ split |] ; try assumption.
    apply conv_refl.
  - destruct IHh1 as [s' [[? ?] ?]].
    exists s'. split ; [ split |] ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Ltac splits n :=
  match n with
  | S ?n => split ; [ splits n |]
  | _ => idtac
  end.

Ltac split_hyp :=
  match goal with
  | H : _ * _ |- _ => destruct H
  end.

Ltac split_hyps :=
  repeat split_hyp.

Lemma inversionJ :
  forall {Σ Γ A u P w v p T},
    Σ ;;; Γ |-i sJ A u P w v p : T ->
    ∑ s1 s2 nx ne,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i v : A) *
      (Σ ;;; Γ ,, svass nx A ,,
         svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2) *
      (Σ ;;; Γ |-i p : sEq A u v) *
      (Σ ;;; Γ |-i w : (P {1 := u}){0 := sRefl A u}) *
      (Σ ;;; Γ |-i P{1 := v}{0 := p} = T).
Proof.
  intros Σ Γ A u P w v p T h.
  dependent induction h.
  - exists s1, s2, nx, ne. splits 6 ; try assumption.
    apply conv_refl.
  - destruct IHh1 as (s1 & s2 & nx & ne & ?).
    split_hyps.
    exists s1, s2, nx, ne. splits 6 ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionTransport :
  forall {Σ Γ A B p t T},
    Σ ;;; Γ |-i sTransport A B p t : T ->
    ∑ s,
      (Σ ;;; Γ |-i p : sEq (sSort s) A B) *
      (Σ ;;; Γ |-i t : A) *
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i B : sSort s) *
      (Σ ;;; Γ |-i B = T).
Proof.
  intros Σ Γ A B p t T h.
  dependent induction h.
  - exists s. splits 4 ; try assumption. apply conv_refl.
  - destruct IHh1 as [s' ?]. split_hyps.
    exists s'. splits 4 ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeq :
  forall {Σ Γ A B a b T},
    Σ ;;; Γ |-i sHeq A a B b : T ->
    ∑ s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i B : sSort s) *
      (Σ ;;; Γ |-i a : A) *
      (Σ ;;; Γ |-i b : B) *
      (Σ ;;; Γ |-i sSort (succ_sort s) = T).
Proof.
  intros Σ Γ A B a b T h.
  dependent induction h.
  - exists s. splits 4 ; try assumption. apply conv_refl.
  - destruct IHh1 as [s' ?]. split_hyps.
    exists s'. splits 4 ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionPack :
  forall {Σ Γ A1 A2 T},
    Σ ;;; Γ |-i sPack A1 A2 : T ->
    ∑ s,
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ |-i sSort s = T).
Proof.
  intros Σ Γ A1 A2 T h.
  dependent induction h.
  - exists s. splits 2 ; try assumption. apply conv_refl.
  - destruct IHh1 as [s' ?]. split_hyps.
    exists s'. splits 2 ; try assumption.
    eapply conv_trans ; eassumption.
Defined.

(*Corollary: Uniqueness of typing *)

Ltac ttinv h :=
  let s := fresh "s" in
  let s1 := fresh "s1" in
  let s2 := fresh "s2" in
  let his := fresh "is" in
  let nx := fresh "nx" in
  let ne := fresh "ne" in
  let hh := fresh "h" in
  match type of h with
  | _ ;;; _ |-i ?t : _ =>
    match t with
    | sRel _ => destruct (inversionRel h) as [his hh]
    | sSort _ => pose proof (inversionSort h) as hh
    | sProd _ _ _ => destruct (inversionProd h) as [s1 [s2 [[? ?] ?]]]
    | sLambda _ _ _ _ => destruct (inversionLambda h) as [s1 [s2 [[[? ?] ?] ?]]]
    | sApp _ _ _ _ _ => destruct (inversionApp h) as [s1 [s2 [[[[? ?] ?] ?] ?]]]
    | sEq _ _ _ => destruct (inversionEq h) as [s [[[? ?] ?] ?]]
    | sRefl _ _ => destruct (inversionRefl h) as [s [[? ?] ?]]
    | sJ _ _ _ _ _ _ => destruct (inversionJ h)
        as [s1 [s2 [nx [ne [[[[[[? ?] ?] ?] ?] ?] ?]]]]]
    | sTransport _ _ _ _ => destruct (inversionTransport h)
        as [s [[[[? ?] ?] ?] ?]]
    | sHeq _ _ _ _ => destruct (inversionHeq h) as [s [[[[? ?] ?] ?] ?]]
    (* TODO: Add more, this means proving more inversions as well. *)
    end
  end.

Ltac unitac h1 h2 :=
  ttinv h1 ; ttinv h2 ;
  eapply conv_trans ; [
    eapply conv_sym ; eassumption
  | idtac
  ].

Lemma uniqueness :
  forall {Σ Γ A B u},
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u : B ->
    Σ ;;; Γ |-i A = B.
Proof.
  intros Σ Γ A B u h1 h2.
  revert Γ A B h1 h2.
  induction u ; intros Γ A B h1 h2.
  all: try unitac h1 h2. all: try assumption.
  - cbn in *. erewrite @safe_nth_irr with (isdecl' := is) in h0. assumption.
  - specialize (IHu1 _ _ _ pi1_ pi1_0).
    specialize (IHu2 _ _ _ pi2_ pi2_1).
    eapply conv_trans ; try eapply pi2_2.
    admit.
  - (* Maybe this isn't the right way to prove it.
       Indeed, with inversion, we lose the uniqueness of the sorts and extra it
       returns.
     *)
Admitted.
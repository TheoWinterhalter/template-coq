(* Inversion lemmata *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import util SAst SLiftSubst SCommon Conversion ITyping.

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

(* TMP *)
Lemma inversionCase :
  forall {Σ Γ ind npar p c brs T},
    Σ ;;; Γ |-i sCase (ind, npar) p c brs : T ->
    False.
Proof.
  intros Σ Γ ind npar p c brs T h.
  dependent induction h. assumption.
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
    apply conv_eq. cbn. rewrite !eq_term_refl. reflexivity.
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

Lemma inversionHeqToEq :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sHeqToEq p : T ->
    ∑ A u v s,
     (Σ ;;; Γ |-i p : sHeq A u A v) *
     (Σ ;;; Γ |-i A : sSort s) *
     (Σ ;;; Γ |-i u : A) *
     (Σ ;;; Γ |-i v : A) *
     (Σ ;;; Γ |-i sEq A u v = T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists A, u, v, s. splits 4. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (A' & u & v & s' & ?). split_hyps.
    exists A', u, v, s'. splits 4. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqRefl :
  forall {Σ Γ A a T},
    Σ ;;; Γ |-i sHeqRefl A a : T ->
    ∑ s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i a : A) *
      (Σ ;;; Γ |-i sHeq A a A a = T).
Proof.
  intros Σ Γ A a T h.
  dependent induction h.
  - exists s. splits 2. all: try assumption. apply conv_refl.
  - destruct IHh1 as [s' ?]. split_hyps. exists s'.
    splits 2. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqSym :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sHeqSym p : T ->
    ∑ A a B b s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i B : sSort s) *
      (Σ ;;; Γ |-i a : A) *
      (Σ ;;; Γ |-i b : B) *
      (Σ ;;; Γ |-i p : sHeq A a B b) *
      (Σ ;;; Γ |-i sHeq B b A a = T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists A, a, B, b, s. splits 5. all: try assumption. apply conv_refl.
  - destruct IHh1 as (A' & a & B' & b & s' & ?). split_hyps.
    exists A', a, B', b, s'. splits 5. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqTrans :
  forall {Σ Γ p q T},
    Σ ;;; Γ |-i sHeqTrans p q : T ->
    ∑ A a B b C c s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i B : sSort s) *
      (Σ ;;; Γ |-i C : sSort s) *
      (Σ ;;; Γ |-i a : A) *
      (Σ ;;; Γ |-i b : B) *
      (Σ ;;; Γ |-i c : C) *
      (Σ ;;; Γ |-i p : sHeq A a B b) *
      (Σ ;;; Γ |-i q : sHeq B b C c) *
      (Σ ;;; Γ |-i sHeq A a C c = T).
Proof.
  intros Σ Γ p q T h.
  dependent induction h.
  - exists A, a, B, b, C, c, s. repeat split. all: try assumption. apply conv_refl.
  - destruct IHh1 as (A' & a & B' & b & C & c' & s' & hh). split_hyps.
    exists A', a, B', b, C, c', s'. repeat split. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqTransport :
  forall {Σ Γ p t T},
    Σ ;;; Γ |-i sHeqTransport p t : T ->
    ∑ A B s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i B : sSort s) *
      (Σ ;;; Γ |-i t : A) *
      (Σ ;;; Γ |-i p : sEq (sSort s) A B) *
      (Σ ;;; Γ |-i sHeq A t B (sTransport A B p t) = T).
Proof.
  intros Σ Γ p t T h.
  dependent induction h.
  - exists A, B, s. repeat split. all: try assumption. apply conv_refl.
  - destruct IHh1 as (A' & B' & s' & ?). split_hyps.
    exists A', B', s'. repeat split. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongProd :
  forall {Σ Γ B1 B2 pA pB T},
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB : T ->
    ∑ s z nx ny np A1 A2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) *
      (Σ ;;; Γ ,, svass np (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) *
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z) *
      (Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z) *
      (Σ ;;; Γ |-i sHeq (sSort (max_sort s z)) (sProd nx A1 B1)
                       (sSort (max_sort s z)) (sProd ny A2 B2)
                = T).
Proof.
  intros Σ Γ B1 B2 pA pB T h.
  dependent induction h.
  - exists s, z, nx, ny, np, A1, A2. repeat split. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & np & A1 & A2 & ?).
    split_hyps.
    exists s', z, nx, ny, np, A1, A2. repeat split. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongLambda :
  forall {Σ Γ B1 B2 t1 t2 pA pB pt T},
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt : T ->
    ∑ s z nx ny np A1 A2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) *
      (Σ ;;; Γ ,, svass np (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) *
      (Σ ;;; Γ ,, svass np (sPack A1 A2)
       |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                    ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                    ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) })) *
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z) *
      (Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z) *
      (Σ ;;; Γ ,, svass nx A1 |-i t1 : B1) *
      (Σ ;;; Γ ,, svass ny A2 |-i t2 : B2) *
      (Σ ;;; Γ |-i sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                       (sProd ny A2 B2) (sLambda ny A2 B2 t2)
                = T).
Proof.
  intros Σ Γ B1 B2 t1 t2 pA pB pt T h.
  dependent induction h.
  - exists s, z, nx, ny, np, A1, A2. repeat split. all: try assumption.
    apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & np & A1 & A2 & ?). split_hyps.
    exists s', z, nx, ny, np, A1, A2. repeat split. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongApp :
  forall {Σ Γ B1 B2 pu pA pB pv T},
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv : T ->
    ∑ s z nx ny np A1 A2 u1 u2 v1 v2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) *
      (Σ ;;; Γ ,, svass np (sPack A1 A2)
       |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                    (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })) *
      (Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2) *
      (Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2) *
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z) *
      (Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z) *
      (Σ ;;; Γ |-i u1 : sProd nx A1 B1) *
      (Σ ;;; Γ |-i u2 : sProd ny A2 B2) *
      (Σ ;;; Γ |-i v1 : A1) *
      (Σ ;;; Γ |-i v2 : A2) *
      (Σ ;;; Γ |-i sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                       (B2{0 := v2}) (sApp u2 ny A2 B2 v2)
                = T).
Proof.
  intros Σ Γ B1 B2 pu pA pB pv T h.
  dependent induction h.
  - exists s, z, nx, ny, np, A1, A2, u1, u2, v1, v2. repeat split.
    all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & z & nx & ny & np & A1 & A2 & u1 & u2 & v1 & v2 & ?).
    split_hyps.
    exists s', z, nx, ny, np, A1, A2, u1, u2, v1, v2. repeat split.
    all: try assumption. eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongEq :
  forall {Σ Γ pA pu pv T},
    Σ ;;; Γ |-i sCongEq pA pu pv : T ->
    ∑ s A1 A2 u1 u2 v1 v2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) *
      (Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2) *
      (Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2) *
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ |-i u1 : A1) *
      (Σ ;;; Γ |-i u2 : A2) *
      (Σ ;;; Γ |-i v1 : A1) *
      (Σ ;;; Γ |-i v2 : A2) *
      (Σ ;;; Γ |-i sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2)
                = T).
Proof.
  intros Σ Γ pA pu pv T h.
  dependent induction h.
  - exists s, A1, A2, u1, u2, v1, v2.
    repeat split. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & u1 & u2 & v1 & v2 & ?). split_hyps.
    exists s', A1, A2, u1, u2, v1, v2.
    repeat split. all: try assumption. eapply conv_trans ; eassumption.
Defined.

Lemma inversionCongRefl :
  forall {Σ Γ pA pu T},
    Σ ;;; Γ |-i sCongRefl pA pu : T ->
    ∑ s A1 A2 u1 u2,
      (Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2) *
      (Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2) *
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ |-i u1 : A1) *
      (Σ ;;; Γ |-i u2 : A2) *
      (Σ ;;; Γ |-i sHeq (sEq A1 u1 u1) (sRefl A1 u1)
                       (sEq A2 u2 u2) (sRefl A2 u2)
                = T).
Proof.
  intros Σ Γ pA pu T h.
  dependent induction h.
  - exists s, A1, A2, u1, u2.
    repeat split. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & u1 & u2 & ?). split_hyps.
    exists s', A1, A2, u1, u2.
    repeat split. all: try assumption. eapply conv_trans ; eassumption.
Defined.

Lemma inversionEqToHeq :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sEqToHeq p : T ->
    ∑ A u v s,
      (Σ ;;; Γ |-i p : sEq A u v) *
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i v : A) *
      (Σ ;;; Γ |-i sHeq A u A v = T).
Proof.
  intros Σ Γ p T h. dependent induction h.
  - exists A, u, v, s. repeat split. all: try assumption. apply conv_refl.
  - destruct IHh1 as (A' & u & v & s' & ?). split_hyps.
    exists A', u, v, s'.
    repeat split. all: try assumption. eapply conv_trans ; eassumption.
Defined.

Lemma inversionHeqTypeEq :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sHeqTypeEq p : T ->
    ∑ A u B v s,
      (Σ ;;; Γ |-i p : sHeq A u B v) *
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i B : sSort s) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i v : B) *
      (Σ ;;; Γ |-i sEq (sSort s) A B = T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists A, u, B, v, s. repeat split. all: try assumption. apply conv_refl.
  - destruct IHh1 as (A' & u & B' & v & s' & ?). split_hyps.
    exists A', u, B', v, s'. repeat split. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionProjT1 :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sProjT1 p : T ->
    ∑ s A1 A2,
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ |-i p : sPack A1 A2) *
      (Σ ;;; Γ |-i A1 = T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists s, A1, A2. repeat split. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & ?). split_hyps.
    exists s', A1, A2. repeat split. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionProjT2 :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sProjT2 p : T ->
    ∑ s A1 A2,
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ |-i p : sPack A1 A2) *
      (Σ ;;; Γ |-i A2 = T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists s, A1, A2. repeat split. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & ?). split_hyps.
    exists s', A1, A2. repeat split. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

Lemma inversionProjTe :
  forall {Σ Γ p T},
    Σ ;;; Γ |-i sProjTe p : T ->
    ∑ s A1 A2,
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ |-i p : sPack A1 A2) *
      (Σ ;;; Γ |-i sHeq A1 (sProjT1 p) A2 (sProjT2 p) = T).
Proof.
  intros Σ Γ p T h.
  dependent induction h.
  - exists s, A1, A2. repeat split. all: try assumption. apply conv_refl.
  - destruct IHh1 as (s' & A1 & A2 & ?). split_hyps.
    exists s', A1, A2. repeat split. all: try assumption.
    eapply conv_trans ; eassumption.
Defined.

(*Corollary: Uniqueness of typing *)

Ltac ttinv h :=
  let s := fresh "s" in
  let s1 := fresh "s1" in
  let s2 := fresh "s2" in
  let z := fresh "z" in
  let his := fresh "is" in
  let nx := fresh "nx" in
  let ny := fresh "ny" in
  let np := fresh "np" in
  let ne := fresh "ne" in
  let A := fresh "A" in
  let B := fresh "B" in
  let C := fresh "C" in
  let A1 := fresh "A1" in
  let A2 := fresh "A2" in
  let u := fresh "u" in
  let v := fresh "v" in
  let u1 := fresh "u1" in
  let u2 := fresh "u2" in
  let v1 := fresh "v1" in
  let v2 := fresh "v2" in
  let a := fresh "a" in
  let b := fresh "b" in
  let c := fresh "c" in
  let t := fresh "t" in
  let univs := fresh "univs" in
  let decl := fresh "decl" in
  let isdecl := fresh "isdecl" in
  let hh := fresh "h" in
  lazymatch type of h with
  | _ ;;; _ |-i ?term : _ =>
    lazymatch term with
    | sRel _ => destruct (inversionRel h) as [his hh]
    | sSort _ => pose proof (inversionSort h) as hh
    | sProd _ _ _ => destruct (inversionProd h) as (s1 & s2 & hh) ; splits_one hh
    | sLambda _ _ _ _ => destruct (inversionLambda h) as (s1 & s2 & hh) ;
                        splits_one hh
    | sApp _ _ _ _ _ => destruct (inversionApp h) as (s1 & s2 & hh) ;
                       splits_one hh
    | sEq _ _ _ => destruct (inversionEq h) as (s & hh) ; splits_one hh
    | sRefl _ _ => destruct (inversionRefl h) as (s & hh) ; splits_one hh
    | sJ _ _ _ _ _ _ => destruct (inversionJ h) as (s1 & s2 & nx & ne & hh) ;
                       splits_one hh
    | sTransport _ _ _ _ => destruct (inversionTransport h) as (s & hh) ;
                           splits_one hh
    | sHeq _ _ _ _ => destruct (inversionHeq h) as (s & hh) ; splits_one hh
    | sHeqToEq _ => destruct (inversionHeqToEq h) as (A & u & v & s & hh) ;
                   splits_one hh
    | sHeqRefl _ _ => destruct (inversionHeqRefl h) as (s & hh) ; splits_one hh
    | sHeqSym _ => destruct (inversionHeqSym h) as (A & a & B & b & s & hh) ;
                  splits_one hh
    | sHeqTrans _ _ =>
      destruct (inversionHeqTrans h) as (A & a & B & b & C & c & s & hh) ;
      splits_one hh
    | sHeqTransport _ _ =>
      destruct (inversionHeqTransport h) as (A & B & s & hh) ;
      splits_one hh
    | sCongProd _ _ _ _ =>
      destruct (inversionCongProd h) as (s & z & nx & ny & np & A1 & A2 & hh) ;
      splits_one hh
    | sCongLambda _ _ _ _ _ _ _ =>
      destruct (inversionCongLambda h)
        as (s & z & nx & ny & np & A1 & A2 & hh) ;
      splits_one hh
    | sCongApp _ _ _ _ _ _ =>
      destruct (inversionCongApp h)
        as (s & z & nx & ny & np & A1 & A2 & u1 & u2 & v1 & v2 & hh) ;
      splits_one hh
    | sCongEq _ _ _ =>
      destruct (inversionCongEq h) as (s & A1 & A2 & u1 & u2 & v1 & v2 & hh) ;
      splits_one hh
    | sCongRefl _ _ =>
      destruct (inversionCongRefl h) as (s & A1 & A2 & u1 & u2 & hh) ;
      splits_one hh
    | sEqToHeq _ =>
      destruct (inversionEqToHeq h) as (A & u & v & s & hh) ;
      splits_one hh
    | sHeqTypeEq _ =>
      destruct (inversionHeqTypeEq h) as (A & u & B & v & s & hh) ;
      splits_one hh
    | sPack _ _ => destruct (inversionPack h) as (s & hh) ; splits_one hh
    | sProjT1 _ =>
      destruct (inversionProjT1 h) as (s & A1 & A2 & hh) ; splits_one hh
    | sProjT2 _ =>
      destruct (inversionProjT2 h) as (s & A1 & A2 & hh) ; splits_one hh
    | sProjTe _ =>
      destruct (inversionProjTe h) as (s & A1 & A2 & hh) ; splits_one hh
    | sInd _ =>
      destruct (inversionInd h) as (univs & decl & isdecl & hh) ; splits_one hh
    | sConstruct _ _ =>
      destruct (inversionConstruct h) as (univs & decl & isdecl & hh) ;
      splits_one hh
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
  - specialize (IHu1 _ _ _ h h0).
    specialize (IHu2 _ _ _ h4 h7).
    eapply conv_trans ; try eapply h6.
    pose proof (sort_conv_inv IHu1) as e1.
    pose proof (sort_conv_inv IHu2) as e2.
    subst. apply conv_refl.
  - specialize (IHu1 _ _ _ h0 h6).
    pose proof (sort_conv_inv IHu1) as e. subst. assumption.
  - specialize (IHu1 _ _ _ h h0).
    pose proof (sort_conv_inv IHu1) as e. subst. assumption.
  - specialize (IHu _ _ _ h h0).
    pose proof (heq_conv_inv IHu) as e. split_hyps.
    eapply conv_trans ; try exact h8.
    apply cong_Eq ; assumption.
  - specialize (IHu _ _ _ h4 h10).
    pose proof (heq_conv_inv IHu) as e. split_hyps.
    eapply conv_trans ; [ | exact h9 ].
    apply cong_Heq ; assumption.
  - specialize (IHu1 _ _ _ h5 h14).
    specialize (IHu2 _ _ _ h4 h13).
    pose proof (heq_conv_inv IHu1) as e1.
    pose proof (heq_conv_inv IHu2) as e2. split_hyps.
    eapply conv_trans ; [ | exact h12 ].
    apply cong_Heq ; assumption.
  - specialize (IHu1 _ _ _ h4 h9).
    specialize (IHu2 _ _ _ h5 h10).
    pose proof (eq_conv_inv IHu1) as e1. split_hyps.
    eapply conv_trans ; [| exact h8 ].
    apply cong_Heq ; try assumption.
    + apply conv_refl.
    + apply cong_Transport ; try assumption.
      all: apply conv_refl.
  - (* specialize (IHu1 _ _ _ h5 h12). *)
    (* Context conversion problems? *)
    (* We need at least something to conclude the two sorts are the same! *)
    specialize (IHu3 _ _ _ h h0).
    pose proof (heq_conv_inv IHu3) as e3. split_hyps.
    pose proof (sort_conv_inv pi1_). subst.
    eapply conv_trans ; [| exact h10 ].
    apply cong_Heq ; try assumption.
    + (* Need context conversion, or a sort label to conclude. *)
      admit.
    + apply cong_Prod ; try assumption.
      apply conv_refl.
    + (* Same *)
      admit.
    + apply cong_Prod ; try assumption. apply conv_refl.
  - specialize (IHu5 _ _ _ h0 h12).
    pose proof (heq_conv_inv IHu5) as e5. split_hyps.
    pose proof (sort_conv_inv pi1_). subst.
    eapply conv_trans ; [| exact h13 ].
    apply cong_Heq ; try assumption.
    + apply cong_Prod ; try assumption. apply conv_refl.
    + apply cong_Lambda ; try assumption. all: apply conv_refl.
    + apply cong_Prod ; try assumption. apply conv_refl.
    + apply cong_Lambda ; try assumption. all: apply conv_refl.
  - specialize (IHu3 _ _ _ h13 h26).
    specialize (IHu4 _ _ _ h h0).
    specialize (IHu6 _ _ _ h12 h25).
    pose proof (heq_conv_inv IHu3).
    pose proof (heq_conv_inv IHu4).
    pose proof (heq_conv_inv IHu6).
    split_hyps.
    eapply conv_trans ; [| exact h16 ].
    apply cong_Heq ; try assumption.
    + (* Need cong_subst *) admit.
    + apply cong_App ; try assumption. apply conv_refl.
    + (* Need cong_subst *) admit.
    + apply cong_App ; try assumption. apply conv_refl.
  - specialize (IHu1 _ _ _ h0 h12).
    specialize (IHu2 _ _ _ h11 h21).
    specialize (IHu3 _ _ _ h10 h20).
    pose proof (heq_conv_inv IHu1).
    pose proof (heq_conv_inv IHu2).
    pose proof (heq_conv_inv IHu3).
    split_hyps. subst.
    eapply conv_trans ; [| exact h13 ].
    apply cong_Heq ; try assumption.
    + apply cong_Eq ; assumption.
    + apply cong_Eq ; assumption.
  - specialize (IHu1 _ _ _ h h0).
    specialize (IHu2 _ _ _ h8 h15).
    pose proof (heq_conv_inv IHu1).
    pose proof (heq_conv_inv IHu2).
    split_hyps.
    pose proof (sort_conv_inv pi1_0). subst.
    eapply conv_trans ; [| exact h10 ].
    apply cong_Heq.
    + apply cong_Eq ; assumption.
    + apply cong_Refl ; assumption.
    + apply cong_Eq ; assumption.
    + apply cong_Refl ; assumption.
  - specialize (IHu _ _ _ h h0).
    pose proof (eq_conv_inv IHu). split_hyps.
    eapply conv_trans ; [| exact h8 ].
    apply cong_Heq ; assumption.
  - specialize (IHu _ _ _ h0 h8).
    pose proof (heq_conv_inv IHu). split_hyps.
    eapply conv_trans ; [| exact h9 ].
    apply cong_Eq ; try assumption.
    (* Problem, missing hypothesis to conclude equality of sorts.
       Maybe we should label it with a sort?

       Another option would be to prove subject reduction to deduce s = s0
       from A0 : s, A1 : s0 and A0 = A1?
     *)
    admit.
  - specialize (IHu1 _ _ _ h h0).
    eapply conv_trans ; [| exact h6 ].
    assumption.
  - specialize (IHu _ _ _ h4 h8).
    pose proof (pack_conv_inv IHu).
    split_hyps.
    eapply conv_trans ; [| exact h7 ].
    assumption.
  - specialize (IHu _ _ _ h4 h8).
    pose proof (pack_conv_inv IHu).
    split_hyps.
    eapply conv_trans ; [| exact h7 ].
    assumption.
  - specialize (IHu _ _ _ h4 h8).
    pose proof (pack_conv_inv IHu).
    split_hyps.
    eapply conv_trans ; [| exact h7 ].
    apply cong_Heq ; try assumption ; apply conv_refl.
  - eapply conv_trans ; [| exact h0 ].
    destruct isdecl as [d1 [[hd1 ?] hn1]].
    destruct isdecl0 as [d2 [[hd2 ?] hn2]].
    unfold sdeclared_minductive in *.
    rewrite hd1 in hd2. inversion hd2. subst.
    rewrite hn1 in hn2. inversion hn2. subst.
    apply conv_refl.
  - eapply conv_trans ; [| exact h0 ].
    erewrite stype_of_constructor_eq. apply conv_refl.
  - pose proof (inversionCase h1). easy.
Admitted.
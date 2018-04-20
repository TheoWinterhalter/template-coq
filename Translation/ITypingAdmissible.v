From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SLiftSubst SCommon ITyping ITypingLemmata Uniqueness.

Corollary sorts_in_sort :
  forall {Σ Γ s1 s2 s3},
    Σ ;;; Γ |-i sSort s1 : sSort s3 ->
    Σ ;;; Γ |-i sSort s2 : sSort s3 ->
    s1 = s2.
Proof.
  intros Σ Γ s1 s2 s3 h1 h2.
  inversion h1. inversion h2.
  subst. inversion H5. reflexivity.
Defined.

(* We state some admissible typing rules *)

Lemma heq_sort :
  forall {Σ Γ s1 s2 z A B p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq z (sSort s1) A (sSort s2) B ->
    Σ ;;; Γ |-i p : sHeq z (sSort s1) A (sSort s1) B.
Proof.
  intros Σ Γ s1 s2 z A B p hg h.
  destruct (istype_type hg h) as [? i].
  inversion i.
  pose proof (sorts_in_sort H4 H7). subst. assumption.
Defined.

Lemma type_HeqToEq' :
  forall {Σ Γ A u v p s},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq s A u A v ->
    Σ ;;; Γ |-i sHeqToEq p : sEq A u v.
Proof.
  intros Σ Γ A u v p s hg h.
  destruct (istype_type hg h) as [? i].
  inversion i. subst.
  eapply type_HeqToEq ; eassumption.
Defined.

Fact sort_heq :
  forall {Σ Γ s1 s2 A B e},
    type_glob Σ ->
    Σ ;;; Γ |-i e : sHeq (sSort s1) A (sSort s2) B ->
    Σ ;;; Γ |-i sHeqToEq e : sEq (sSort s1) A B.
Proof.
  intros Σ Γ s1 s2 A B e hg h.
  destruct (istype_type hg h) as [? hty].
  inversion hty.
  eapply type_HeqToEq' ; try assumption.
  eapply heq_sort ; eassumption.
Defined.

Corollary sort_heq_ex :
  forall {Σ Γ s1 s2 A B e},
    type_glob Σ ->
    Σ ;;; Γ |-i e : sHeq (sSort s1) A (sSort s2) B ->
    ∑ p, Σ ;;; Γ |-i p : sEq (sSort s1) A B.
Proof.
  intros Σ Γ s A B e hg h.
  eexists. now eapply sort_heq.
Defined.

Lemma type_HeqRefl' :
  forall {Σ Γ A a},
    type_glob Σ ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i sHeqRefl A a : sHeq A a A a.
Proof.
  intros Σ Γ A a hg h.
  destruct (istype_type hg h).
  eapply type_HeqRefl ; eassumption.
Defined.

Lemma type_HeqTrans' :
  forall {Σ Γ A a B b C c p q},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i q : sHeq B b C c ->
    Σ ;;; Γ |-i sHeqTrans p q : sHeq A a C c.
Proof.
  intros Σ Γ A a B b C c p q hg h1 h2.
  destruct (istype_type hg h1) as [? i1].
  inversion i1.
  destruct (istype_type hg h2) as [? i2].
  inversion i2. subst.
  eapply type_HeqTrans. all: try eassumption.
  rewrite (uniqueness hg H6 H15). assumption.
Defined.

Lemma type_HeqTransport' :
  forall {Σ Γ s A B p t},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ ;;; Γ |-i sHeqTransport p t : sHeq A t B (sTransport A B p t).
Proof.
  intros Σ Γ s A B p t hg ht hp.
  destruct (istype_type hg hp) as [? i].
  inversion i.
  eapply type_HeqTransport ; eassumption.
Defined.

Lemma type_CongProd'' :
  forall {Σ Γ s z nx ny A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (max_sort s z)) (sProd nx A1 B1)
         (sSort (max_sort s z)) (sProd ny A2 B2).
Proof.
  intros Σ Γ s z nx ny A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. inversion ipA.
  destruct (istype_type hg hpB) as [? ipB]. inversion ipB.
  eapply type_CongProd.
  all: eassumption.
Defined.

Lemma prod_sorts :
  forall {Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    (s1 = s2) * (z1 = z2).
Proof.
  intros Σ Γ s1 s2 z1 z2 A1 A2 B1 B2 pA pB hg hpA hpB.
  split.
  - destruct (istype_type hg hpA) as [? ipA]. inversion ipA.
    eapply sorts_in_sort ; eassumption.
  - destruct (istype_type hg hpB) as [? ipB]. inversion ipB.
    eapply sorts_in_sort ; eassumption.
Defined.

Lemma type_CongProd' :
  forall {Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (max_sort s1 z1)) (sProd nx A1 B1)
         (sSort (max_sort s2 z2)) (sProd ny A2 B2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  destruct (prod_sorts hg hpA hpB) as [e1 e2].
  subst. rename z2 into z, s2 into s.
  eapply type_CongProd'' ; eassumption.
Defined.

Lemma type_CongLambda'' :
  forall {Σ Γ s z nx nx' ny ny' A1 A2 B1 B2 t1 t2 pA pB pt},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ ,, A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx' A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny' A2 B2 t2).
Proof.
  intros Σ Γ s z nx nx' ny ny' A1 A2 B1 B2 t1 t2 pA pB pt
         hg hpA hpB hpt hB1 hB2 ht1 ht2.
  destruct (istype_type hg hpA) as [? ipA]. inversion ipA.
  destruct (istype_type hg hpB) as [? ipB]. inversion ipB.
  destruct (istype_type hg hpt) as [? ipt]. inversion ipt.
  eapply type_CongLambda ; eassumption.
Defined.

Lemma type_CongLambda' :
  forall {Σ Γ s1 s2 z1 z2 nx ny nx' ny' A1 A2 B1 B2 t1 t2 pA pB pt},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ ,, A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx' A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny' A2 B2 t2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny nx' ny' A1 A2 B1 B2 t1 t2 pA pB pt hg
         hpA hpB hpt hB1 hB2 ht1 ht2.
  destruct (prod_sorts hg hpA hpB) as [e1 e2].
  subst. rename s2 into s, z2 into z.
  eapply type_CongLambda'' ; eassumption.
Defined.

Lemma type_CongApp'' :
  forall {Σ Γ s z nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 A2 B2 v2).
Proof.
  intros Σ Γ s z nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hg hpA hpB hpu hpv hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA]. inversion ipA.
  destruct (istype_type hg hpB) as [? ipB]. inversion ipB.
  destruct (istype_type hg hpu) as [? ipu]. inversion ipu.
  destruct (istype_type hg hpv) as [? ipv]. inversion ipv.
  eapply type_CongApp ; eassumption.
Defined.

Lemma type_CongApp' :
  forall {Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ ,, A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 A2 B2 v2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hg hpA hpB hpu hpv hB1 hB2.
  destruct (prod_sorts hg hpA hpB).
  subst. rename s2 into s, z2 into z.
  eapply type_CongApp'' ; eassumption.
Defined.

Lemma type_CongEq'' :
  forall {Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv :
               sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2).
Proof.
  intros Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv hg hpA hpu hpv.
  destruct (istype_type hg hpA) as [? iA]. inversion iA.
  destruct (istype_type hg hpu) as [? iu]. inversion iu.
  destruct (istype_type hg hpv) as [? iv]. inversion iv.
  eapply type_CongEq.
  all: assumption.
Defined.

Lemma type_CongEq' :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv
             : sHeq (sSort s1) (sEq A1 u1 v1)
                    (sSort s2) (sEq A2 u2 v2).
Proof.
  intros Σ Γ s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv hg hpA hpu hpv.
  destruct (istype_type hg hpA) as [? iA]. inversion iA.
  destruct (istype_type hg hpu) as [? iu]. inversion iu.
  destruct (istype_type hg hpv) as [? iv]. inversion iv.
  subst.
  pose proof (sorts_in_sort H5 H6). subst.
  eapply type_CongEq''.
  all: assumption.
Defined.

Lemma type_CongRefl'' :
  forall {Σ Γ s A1 A2 u1 u2 pA pu},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i sCongRefl pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2).
Proof.
  intros Σ Γ s A1 A2 u1 u2 pA pu hg hpA hpu.
  destruct (istype_type hg hpA) as [? iA]. inversion iA.
  destruct (istype_type hg hpu) as [? iu]. inversion iu.
  eapply type_CongRefl.
  all: eassumption.
Defined.

Lemma type_CongRefl' :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 pA pu},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i sCongRefl pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2).
Proof.
  intros Σ Γ s1 s2 A1 A2 u1 u2 pA pu hg hpA hpu.
  destruct (istype_type hg hpA) as [? iA]. inversion iA.
  destruct (istype_type hg hpu) as [? iu]. inversion iu.
  eapply type_CongRefl'' ; try eassumption.
  eapply heq_sort ; eassumption.
Defined.

Lemma type_EqToHeq' :
  forall {Σ Γ A u v p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i sEqToHeq p : sHeq A u A v.
Proof.
  intros Σ Γ A u v p hg h.
  destruct (istype_type hg h) as [? i]. inversion i.
  eapply type_EqToHeq ; eassumption.
Defined.

Lemma type_ProjT1' :
  forall {Σ Γ A1 A2 p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT1 p : A1.
Proof.
  intros Σ Γ A1 A2 p hg hp.
  destruct (istype_type hg hp) as [? i]. inversion i.
  eapply type_ProjT1 ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_ProjT2' :
  forall {Σ Γ A1 A2 p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT2 p : A2.
Proof.
  intros Σ Γ A1 A2 p hg hp.
  destruct (istype_type hg hp) as [? i]. inversion i.
  eapply type_ProjT2 ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_ProjTe' :
  forall {Σ Γ A1 A2 p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjTe p : sHeq A1 (sProjT1 p) A2 (sProjT2 p).
Proof.
  intros Σ Γ A1 A2 p hg hp.
  destruct (istype_type hg hp) as [? i]. inversion i.
  eapply type_ProjTe ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_Refl' :
  forall {Σ Γ A u},
    type_glob Σ ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u.
Proof.
  intros Σ Γ A u hg h.
  destruct (istype_type hg h) as [? i].
  eapply type_Refl ; eassumption.
Defined.

Lemma type_Transport' :
  forall {Σ Γ s T1 T2 p t},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sEq (sSort s) T1 T2 ->
    Σ ;;; Γ |-i t : T1 ->
    Σ ;;; Γ |-i sTransport T1 T2 p t : T2.
Proof.
  intros Σ Γ s T1 T2 p t hg hp ht.
  destruct (istype_type hg hp) as [? i]. inversion i.
  eapply type_Transport ; eassumption.
Defined.

Lemma type_HeqTypeEq' :
  forall {Σ Γ A u B v p s},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A u B v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i sHeqTypeEq A B p : sEq (sSort s) A B.
Proof.
  intros Σ Γ A u B v p s hg hp hA.
  destruct (istype_type hg hp) as [? i]. inversion i.
  eapply type_HeqTypeEq ; try eassumption.
  pose proof (uniqueness hg H5 hA). subst.
  inversion H9. subst. assumption.
Defined.

Lemma type_Beta' :
  forall {Σ Γ A B t u nx},
    type_glob Σ ->
    Σ;;; Γ,, A |-i t : B ->
    Σ;;; Γ |-i u : A ->
    Σ;;; Γ |-i sBeta A B t u
            : sEq (B {0 := u}) (sApp (sLambda nx A B t) A B u) (t {0 := u}).
Proof.
  intros Σ Γ A B t u nx hg ht hu.
  destruct (istype_type hg ht).
  destruct (istype_type hg hu).
  eapply type_Beta ; eassumption.
Defined.


Notation sArrow A B := (sProd nAnon A (lift0 1 B)).
Notation up := (lift 1 0).
Notation up2 := (lift 2 0).
Notation up3 := (lift 3 0).
Notation up4 := (lift 4 0).

(* Ltac closed_goal := *)
(*   match goal with *)
(*   | |- ?T => assert_fails ltac:(has_evar T) *)
(*   end. *)

Ltac rew1 := cbn; rewrite ?lift_lift, ?liftP3, ?substP3, ?lift00 by omega; cbn.

Tactic Notation "rew1" "in" hyp(X)
  := cbn in X; rewrite ?lift_lift, ?liftP3, ?substP3, ?lift00
       in X by omega; cbn in X.

Ltac tea :=
  match goal with
  | |- _ ;;; _ |-i _ : _ => try eassumption
  | |- wf _ _ => try eassumption
  | |- type_glob _ => try eassumption
  | |- _ < _ => try (cbn; omega)
  | |- _ <= _ => try (cbn; omega)
  | |- sSort ?s1 = sSort ?s2 =>
    rew1; rewrite ?max_id; tryif has_evar s1 + has_evar s2
    then idtac else (try reflexivity)
  | |- ?t1 = ?t2 =>
    rew1; tryif has_evar t1 + has_evar t2 then idtac else (try reflexivity)
  | _ => idtac
  end.

Ltac typ :=
  match goal with
  | |- _ ;;; _ |-i sApp _ _ _ _ : _ =>
    first [refine (type_App _ _ _ _) |
           eapply meta_conv; [refine (type_App _ _ _ _)|] ]
  | |- _ ;;; ?Γ |-i sJ _ _ _ _ _ _ : ?T =>
    first [refine (type_J _ _ _ _ _ _) |
           eapply meta_conv; [refine (type_J _ _ _ _ _ _)|] ]
  | |- ?Σ ;;; ?Γ |-i sRel ?n : ?T =>
    first [refine (type_Rel Σ Γ n _ _) |
           eapply meta_conv; [refine (type_Rel _ _)|] ]
  | |- ?Σ ;;; ?Γ |-i sProd ?n ?A ?B : ?S =>
    first [eapply type_Prod |
           eapply meta_conv; [eapply type_Prod|] ]

  | |- _ ;;; _ |-i up ?T : ?AA =>
    first [eapply typing_lift01 | eapply (typing_lift01 (A:=AA))]
  | h : _ ;;; _ |-i ?T : _ , h' : type_glob _ |- _ ;;; _  |-i up ?T : _ =>
    eapply (typing_lift01 h' h)

  | |- _ ;;; _ |-i up2 ?T : ?AA =>
    first [eapply typing_lift02 | eapply (typing_lift02 (A:=AA))]
  | h : _ ;;; _ |-i ?T : _ , h' : type_glob _ |- _ ;;; _  |-i up2 ?T : _ =>
    eapply (typing_lift02 h' h)

  | |- ?Σ ;;; ?Γ ,, ?A1 ,, ?A2 ,, ?A3 |-i up3 _ : ?T
    => first [refine (@type_lift Σ Γ [A3; A2; A1] nil _ _ _ _ _) |
              refine (@type_lift Σ Γ [A3; A2; A1] nil _ T _ _ _)]

  | |- ?Σ ;;; ?Γ ,, ?A1 ,, ?A2 ,, ?A3 ,, ?A4 |-i up4 _ : ?T
    => first [refine (@type_lift Σ Γ [A4; A3; A2; A1] nil _ _ _ _ _) |
              refine (@type_lift Σ Γ [A4; A3; A2; A1] nil _ T _ _ _)]

  | |- wf _ _ => try (eapply typing_wf; eassumption); econstructor
  | _ => econstructor
  end; tea.

Ltac rtyp := repeat typ.

(* We need to add s *)
Definition sTransport' T1 T2 s p t :=
  sJ (sSort s) T1 (sRel 1) t T2 p.

Definition type_Transport'' {Σ Γ s T1 T2 p t}
           (HΣ : type_glob Σ)
           (HT1 : Σ ;;; Γ |-i T1 : sSort s)
           (HT2 : Σ ;;; Γ |-i T2 : sSort s)
           (Hp : Σ ;;; Γ |-i p : sEq (sSort s) T1 T2)
           (Ht : Σ ;;; Γ |-i t : T1)
  : Σ ;;; Γ |-i sTransport' T1 T2 s p t : T2.
  unfold sTransport'. rtyp. rew1; tea.
Defined.


(* Definition Sym A u v p *)
(*   := sJ A u (sEq (lift0 2 A) (sRel 1) (lift0 2 u)) (sRefl A u) v p. *)

Notation Sym A u v p
  := (sJ A u (sEq (lift0 2 A) (sRel 1) (lift0 2 u)) (sRefl A u) v p).

Definition type_Sym {Σ Γ s A u v p}
           (HΣ : type_glob Σ)
  : Σ ;;; Γ |-i p : sEq A u v ->
    Σ;;; Γ |-i u : A ->
    Σ;;; Γ |-i v : A ->
    Σ;;; Γ |-i A : sSort s ->
    Σ;;; Γ |-i Sym A u v p : sEq A v u.
  intros H H0 H1 H2. rtyp. rew1; typ.
Defined.


Definition Trans A u v w p q
  := sJ A v (sEq (lift0 2 A) (lift0 2 u) (sRel 1)) p w q.

Definition type_Trans {Σ Γ s A u v w p q}
           (HΣ : type_glob Σ)
  : Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i q : sEq A v w ->
    Σ;;; Γ |-i u : A ->
    Σ;;; Γ |-i v : A ->
    Σ;;; Γ |-i w : A ->
    Σ;;; Γ |-i A : sSort s ->
    Σ;;; Γ |-i Trans A u v w p q : sEq A u w.
  intros H H0 H1 H2 H3 H4. unfold Trans. rtyp. rew1; tea.
Defined.

(* to remove? *)
Ltac lift_sort :=
  match goal with
  | |- _ ;;; _ |-i lift ?n ?k ?t : ?S => change S with (lift n k S)
  | |- _ ;;; _ |-i ?t { ?n := ?u } : ?S => change S with (S {n := u})
  end.

Notation "'existsT'  x .. y , P" := (sigT (fun x => .. (sigT (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.



(* Definition ap_transport {A B} (p q : A = B) (x : A) (e : p = q) *)
(*   : transport p x = transport q x. *)
(*   refine (J _ p (fun q' _ => transport p x = transport q' x) _ _ e). *)
(*   reflexivity. *)
(* Defined. *)

Definition sap_transport A u B p q e s
  := sJ (sEq (sSort s) A B) p (sEq (up2 B) (sTransport (up2 A) (up2 B) (up2 p) (up2 u)) (sTransport (up2 A) (up2 B) (sRel 1) (up2 u))) (sRefl B (sTransport A B p u)) q e.

Definition type_ap_transport {Σ Γ A u B p q e s} :
    type_glob Σ ->
    Σ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ;;; Γ |-i q : sEq (sSort s) A B ->
    Σ;;; Γ |-i A : sSort s ->
    Σ;;; Γ |-i B : sSort s ->
    Σ;;; Γ |-i e : sEq (sEq (sSort s) A B) p q ->
    Σ;;; Γ |-i u : A ->
    Σ;;; Γ |-i sap_transport A u B p q e s
             : sEq B (sTransport A B p u) (sTransport A B q u).
  intros X H H0 H1 H2 H3 H4. unfold sap_transport.
  rtyp. rew1; rtyp.
Defined.


Definition pmove_transport_aux {A u B p s} :
  existsT q', forall Σ Γ,
    type_glob Σ ->
    Σ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ;;; Γ |-i A : sSort s ->
    Σ;;; Γ |-i B : sSort s ->
    Σ;;; Γ |-i u : A ->
    Σ;;; Γ |-i q' :
    sProd (nNamed "v") B (sArrow (sEq (up B) (sTransport (up A) (up B) (up p) (up u)) (sRel 0))
    (sEq (up A) (up u) (sTransport (up B) (up A) (Sym (sSort s) (up A) (up B) (up p)) (sRel 0)))).
  econstructor.
  intros Σ Γ H H0 H1 H2 H3.
  simple refine (let XX := type_J _ _ _ _ H0 _ in _); tea.
  5: rtyp. exact s.
  - (* the predicate *)
    exact (sProd (nNamed "v") (sRel 1) (sArrow (sEq (sRel 2) (sTransport (up3 A) (sRel 2) (sRel 1) (up3 u)) (sRel 0))
    (sEq (up3 A) (up3 u) (sTransport (sRel 2) (up3 A) (Sym (sSort s) (up3 A) (sRel 2) (sRel 1)) (sRel 0))))).
  - (* idmap *)
    shelve.
  - (* the predicate is well sorted *)
    rtyp. all: rew1; rtyp.
  - (* idmap inhabit the predicate in refl *)
    rew1.
    eapply type_Lambda.
    + eassumption.
    + rtyp. rew1; rtyp.
    + eapply type_Lambda.
      * rtyp.
      * rtyp. rew1; rtyp.
      * eapply (type_Trans (p := Sym _ _ _ (sTransportRefl (up2 A) (up2 u))));
          tea.
        { eapply type_Sym; rtyp; tea. }
        2-5: rtyp. 2: rew1; rtyp.
        { eapply (type_Trans (p := sRel 0)); tea.
           rtyp. 2-5: rtyp. 2: rew1; rtyp.
           eapply (type_Trans (p := Sym _ _ _
                                        (sTransportRefl (up2 A) (sRel 1)))); tea.
           { eapply type_Sym; rtyp; tea. }
           2-5: rtyp. 2: rew1; rtyp.
           { eapply type_ap_transport; tea.
             1-4: rtyp. rew1; rtyp. 2: rtyp.
             { eapply type_Sym; tea. 2-4: rtyp.
               2: rew1; rtyp.
               refine (let XX := type_JRefl (P := sEq (sSort s) (sRel 1) (up4 A))
                                            _ _ _ _ in _).
               clearbody XX; rew1 in XX. exact XX.
               Unshelve. 6-8: rtyp. 4: rew1; rtyp.
               2-3: econstructor. shelve.
             }}}
  - clearbody XX. rew1 in XX. rew1. exact XX.
Defined.

Definition smove_transport_aux A u B p s
  := Eval cbn in projT1 (@pmove_transport_aux A u B p s).

Definition type_move_transport_aux {A u B p s Σ Γ} H H0 H1 H2 H3
  := projT2 (@pmove_transport_aux A u B p s) Σ Γ H H0 H1 H2 H3.



Definition pmove_transport {A u B v p q s} :
  existsT q', forall Σ Γ,
    type_glob Σ ->
    Σ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ;;; Γ |-i q : sEq B (sTransport A B p u) v ->
    Σ;;; Γ |-i A : sSort s ->
    Σ;;; Γ |-i B : sSort s ->
    Σ;;; Γ |-i u : A ->
    Σ;;; Γ |-i v : B ->
    Σ;;; Γ |-i q' : sEq A u (sTransport B A (Sym (sSort s) A B p) v).
  econstructor. intros Σ Γ HΣ H H0 H1 H2 H3 H4.
  pose proof (type_move_transport_aux HΣ H H1 H2 H3).
  simple refine (let YY := type_App _ _ H5 H4 in _);
    try eassumption.
  - rtyp. all: rew1; rtyp.
  - clearbody YY; cbn in YY. clear H5.
    rew1 in YY.
    simple refine (let ZZ := type_App _ _ YY H0 in _);
      try clear YY; tea.
    1-2: assumption.
    + rtyp.
    + rtyp. all: rew1; rtyp.
    + clearbody ZZ; clear YY. rew1 in ZZ.
      exact ZZ.
Defined.

Definition smove_transport A u B v p q s
  := projT1 (@pmove_transport A u B v p q s).

Definition type_move_transport {Σ Γ A u B v p q s} HΣ H H0 H1 H2 H3 H4
  := projT2 (@pmove_transport A u B v p q s) Σ Γ HΣ H H0 H1 H2 H3 H4.


Definition pHeqSym A a B b p s :
    existsT p', forall Σ Γ , type_glob Σ ->
    Σ;;; Γ |-i A : sSort s ->
    Σ;;; Γ |-i B : sSort s ->
    Σ;;; Γ |-i a : A ->
    Σ;;; Γ |-i b : B ->
    Σ;;; Γ |-i p : sHeq A a B b ->
    Σ;;; Γ |-i p' : sHeq B b A a.
  econstructor. intros Σ Γ X H0 H1 H2 H3 H4. 
  simple refine (let XX := type_HeqTypeEq H4 _ _ _ _ in _); tea.
  simple refine (let YY := type_HeqTermEq H4 _ _ _ _ in _); tea.
  clearbody XX; clearbody YY; clear H4.
  eapply type_HeqConstr; tea.
  - eapply type_Sym; tea. rtyp.
  - eapply type_Sym; tea. 2: rtyp; rew1; rtyp.
    unshelve eapply type_move_transport; tea.
Defined.

Definition sHeqSym A a B b p s := Eval cbn in projT1 (@pHeqSym A a B b p s).

Definition type_HeqSym {Σ Γ A a B b p s} :
    type_glob Σ ->
    Σ;;; Γ |-i A : sSort s ->
    Σ;;; Γ |-i B : sSort s ->
    Σ;;; Γ |-i a : A ->
    Σ;;; Γ |-i b : B ->
    Σ;;; Γ |-i p : sHeq A a B b ->
    Σ;;; Γ |-i sHeqSym A a B b p s : sHeq B b A a
  := projT2 (@pHeqSym A a B b p s) Σ Γ.

Lemma type_HeqSym' {Σ Γ A a B b p s} :
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i sHeqSym A a B b p s : sHeq B b A a.
Proof.
  intros hg h hA.
  destruct (istype_type hg h) as [? hty].
  inversion hty.
  pose proof (uniqueness hg H5 hA).
  inversion H9; subst.
  eapply type_HeqSym; tea.
Defined.

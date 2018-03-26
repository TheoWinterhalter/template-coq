From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SLiftSubst SCommon ITyping ITypingLemmata.

(* We state some admissible typing rules *)
Lemma type_conv' :
  forall {Σ Γ t A B s},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i A = B : sSort s ->
    Σ ;;; Γ |-i t : B.
Proof.
  intros Σ Γ t A B s hg ht eq.
  eapply type_conv.
  - eassumption.
  - apply (eq_typing hg eq).
  - assumption.
Defined.

Lemma heq_sort :
  forall {Σ Γ s1 s2 A B p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq (sSort s1) A (sSort s2) B ->
    Σ ;;; Γ |-i p : sHeq (sSort s1) A (sSort s1) B.
Proof.
  intros Σ Γ s1 s2 A B p hg h.
  destruct (istype_type hg h) as [? i].
  destruct (inversionHeq hg i) as [? [[[[e1 e2] ?] ?] ?]].
  pose proof (sorts_in_sort e2 e1) as eq.
  eapply type_conv'.
  - assumption.
  - eassumption.
  - apply cong_Heq.
    all: try (apply eq_reflexivity ; eassumption).
    assumption.
Defined.

Lemma type_HeqToEq' :
  forall {Σ Γ A u v p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A u A v ->
    Σ ;;; Γ |-i sHeqToEq p : sEq A u v.
Proof.
  intros Σ Γ A u v p hg h.
  destruct (istype_type hg h) as [? i].
  destruct (inversionHeq hg i) as [? [[[[? ?] ?] ?] ?]].
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
  destruct (inversionHeq hg hty) as [? [[[[? ?] ?] ?] ?]].
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

Lemma type_HeqSym' :
  forall {Σ Γ A a B b p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i sHeqSym p : sHeq B b A a.
Proof.
  intros Σ Γ A a B b p hg h.
  destruct (istype_type hg h) as [? hty].
  destruct (inversionHeq hg hty) as [? [[[[? ?] ?] ?] ?]].
  now eapply type_HeqSym.
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
  destruct (inversionHeq hg i1) as [? [[[[? iB1] ?] ?] ?]].
  destruct (istype_type hg h2) as [? i2].
  destruct (inversionHeq hg i2) as [? [[[[iB2 ?] ?] ?] ?]].
  eapply type_HeqTrans. all: try eassumption.
  destruct (uniqueness iB2 iB1) as [? eq].
  eapply type_conv ; [ eassumption | idtac | eassumption ].
  apply (eq_typing hg eq).
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
  destruct (inversionEq hg i) as [? [[[? ?] ?] ?]].
  eapply type_HeqTransport ; eassumption.
Defined.

Lemma type_CongProd'' :
  forall {Σ Γ s z nx ny np A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (max_sort s z)) (sProd nx A1 B1)
         (sSort (max_sort s z)) (sProd ny A2 B2).
Proof.
  intros Σ Γ s z nx ny np A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA].
  destruct (inversionHeq hg ipA) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hg hpB) as [? ipB].
  destruct (inversionHeq hg ipB) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongProd.
  all: eassumption.
Defined.

Lemma prod_sorts :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    ∑ ss zz mm,
      (Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort ss) *
      (Σ ;;; Γ ,, svass ny A2 |-i sSort z2 = sSort z1 : sSort zz) *
      (Σ ;;; Γ |-i sSort (max_sort s1 z1) = sSort (max_sort s2 z2) : sSort mm).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  assert (hs : ∑ ss, Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort ss).
  { destruct (istype_type hg hpA) as [? ipA].
    destruct (inversionHeq hg ipA) as [? [[[[e1 e2] ?] ?] ?]].
    pose proof (sorts_in_sort e1 e2).
    eexists. eassumption.
  }
  destruct hs as [ss hss]. exists ss.
  assert (hz : ∑ zz, Σ;;; Γ,, svass ny A2 |-i sSort z2 = sSort z1 : sSort zz).
  { destruct (istype_type hg hpB) as [? ipB].
    destruct (inversionHeq hg ipB) as [? [[[[f1 f2] ?] ?] ?]].
    pose proof (sorts_in_sort f2 f1).
    eexists. eapply strengthen_sort_eq.
    - eassumption.
    - eapply typing_wf. eassumption.
  }
  destruct hz as [zz hzz]. exists zz.
  assert (hP1 : Σ ;;; Γ |-i sProd nx A1 B1 : sSort (max_sort s1 z1)).
  { destruct (istype_type hg hpA) as [? ipA].
    destruct (inversionHeq hg ipA) as [? [[[[e1 e2] ?] ?] ?]].
    apply type_Prod ; eassumption.
  }
  assert (hP2 : Σ ;;; Γ |-i sProd nx A1 B1 : sSort (max_sort s2 z2)).
  { destruct (istype_type hg hpA) as [? ipA].
    destruct (inversionHeq hg ipA) as [? [[[[e1 e2] ?] ?] ?]].
    apply type_Prod.
    - eapply type_conv' ; eassumption.
    - eapply type_conv'.
      + assumption.
      + eassumption.
      + apply eq_symmetry.
        eapply strengthen_sort_eq.
        * eassumption.
        * eapply typing_wf. eassumption.
  }
  destruct (uniqueness hP1 hP2) as [mm hmm]. exists mm.
  repeat split.
  - assumption.
  - assumption.
  - assumption.
Defined.

Lemma type_CongProd' :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (max_sort s1 z1)) (sProd nx A1 B1)
         (sSort (max_sort s2 z2)) (sProd ny A2 B2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB hg hpA hpB hB1 hB2.
  destruct (prod_sorts hg hpA hpB hB1 hB2) as [ss [zz [mm [[e e0] e1]]]].
  eapply type_conv'.
  - assumption.
  - eapply type_CongProd''.
    + assumption.
    + eapply heq_sort ; eassumption.
    + eapply heq_sort ; eassumption.
    + eassumption.
    + eapply type_conv'.
      * assumption.
      * eassumption.
      * eassumption.
  - apply cong_Heq.
    all: try apply eq_reflexivity.
    + apply type_Sort. eapply typing_wf. eassumption.
    + eapply eq_conv.
      * eassumption.
      * eapply eq_symmetry. eapply inversionSort ; try assumption.
        apply (eq_typing hg e1).
    + destruct (istype_type hg hpA) as [? ipA].
      destruct (inversionHeq hg ipA) as [? [[[[? ?] ?] ?] ?]].
      apply type_Prod ; eassumption.
    + destruct (istype_type hg hpA) as [? ipA].
      destruct (inversionHeq hg ipA) as [? [[[[? ?] ?] ?] ?]].
      apply type_Prod.
      * eapply type_conv'.
        -- assumption.
        -- eassumption.
        -- eapply eq_symmetry. eassumption.
      * eapply type_conv' ; eassumption.
Defined.

Lemma type_CongLambda'' :
  forall {Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ ,, svass nx A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, svass ny A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2).
Proof.
  intros Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt
         hg hpA hpB hpt hB1 hB2 ht1 ht2.
  destruct (istype_type hg hpA) as [? ipA].
  destruct (inversionHeq hg ipA) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hg hpB) as [? ipB].
  destruct (inversionHeq hg ipB) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hg hpt) as [? ipt].
  destruct (inversionHeq hg ipt) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongLambda ; eassumption.
Defined.

Lemma type_CongLambda' :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 t1 t2 pA pB pt},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ ,, svass nx A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, svass ny A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 t1 t2 pA pB pt hg
         hpA hpB hpt hB1 hB2 ht1 ht2.
  destruct (prod_sorts hg hpA hpB hB1 hB2) as [ss [zz [mm [[e e0] e1]]]].
  eapply type_CongLambda''.
  - assumption.
  - eapply heq_sort ; eassumption.
  - eapply heq_sort ; eassumption.
  - eassumption.
  - assumption.
  - eapply type_conv' ; eassumption.
  - assumption.
  - assumption.
Defined.

Lemma type_CongApp'' :
  forall {Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 ny A2 B2 v2).
Proof.
  intros Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hg hpA hpB hpu hpv hB1 hB2.
  destruct (istype_type hg hpA) as [? ipA].
  destruct (inversionHeq hg ipA) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hg hpB) as [? ipB].
  destruct (inversionHeq hg ipB) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hg hpu) as [? ipu].
  destruct (inversionHeq hg ipu) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hg hpv) as [? ipv].
  destruct (inversionHeq hg ipv) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongApp ; eassumption.
Defined.

Lemma type_CongApp' :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    type_glob Σ ->
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 ny A2 B2 v2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hg hpA hpB hpu hpv hB1 hB2.
  destruct (prod_sorts hg hpA hpB hB1 hB2) as [ss [zz [mm [[e e0] e1]]]].
  eapply type_CongApp'' ; try eassumption.
  - eapply heq_sort ; eassumption.
  - eapply heq_sort ; eassumption.
  - eapply type_conv' ; eassumption.
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
  destruct (istype_type hg hpA) as [? iA].
  destruct (istype_type hg hpu) as [? iu].
  destruct (istype_type hg hpv) as [? iv].
  destruct (inversionHeq hg iA) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq hg iu) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq hg iv) as [? [[[[? ?] ?] ?] ?]].
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
  destruct (istype_type hg hpA) as [? iA].
  destruct (istype_type hg hpu) as [? iu].
  destruct (istype_type hg hpv) as [? iv].
  destruct (inversionHeq hg iA) as [? [[[[? hs2] ?] hA2] ?]].
  destruct (inversionHeq hg iu) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq hg iv) as [? [[[[? ?] ?] ?] ?]].
  eapply type_conv'.
  - assumption.
  - eapply type_CongEq''.
    + assumption.
    + eapply heq_sort ; eassumption.
    + eassumption.
    + eassumption.
  - apply cong_Heq.
    all: try (apply eq_reflexivity).
    + eassumption.
    + apply sorts_in_sort ; assumption.
    + apply type_Eq ; assumption.
    + eapply type_conv'.
      * assumption.
      * apply type_Eq ; [ apply hA2 | assumption .. ].
      * eapply sorts_in_sort ; [ apply hs2 | assumption ].
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
  destruct (istype_type hg hpA) as [? iA].
  destruct (istype_type hg hpu) as [? iu].
  destruct (inversionHeq hg iA) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq hg iu) as [? [[[[? ?] ?] ?] ?]].
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
  destruct (istype_type hg hpA) as [? iA].
  destruct (istype_type hg hpu) as [? iu].
  destruct (inversionHeq hg iA) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq hg iu) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongRefl''.
  - assumption.
  - eapply heq_sort ; eassumption.
  - assumption.
Defined.

Lemma type_EqToHeq' :
  forall {Σ Γ A u v p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i sEqToHeq p : sHeq A u A v.
Proof.
  intros Σ Γ A u v p hg h.
  destruct (istype_type hg h) as [? i].
  destruct (inversionEq hg i) as [? [[[? ?] ?] ?]].
  eapply type_EqToHeq ; eassumption.
Defined.

Lemma type_ProjT1' :
  forall {Σ Γ A1 A2 p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT1 p : A1.
Proof.
  intros Σ Γ A1 A2 p hg hp.
  destruct (istype_type hg hp) as [? i].
  destruct (inversionPack hg i) as [s [[? ?] ?]].
  eapply type_ProjT1 ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_ProjT2' :
  forall {Σ Γ A1 A2 p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT2 p : A2.
Proof.
  intros Σ Γ A1 A2 p hg hp.
  destruct (istype_type hg hp) as [? i].
  destruct (inversionPack hg i) as [s [[? ?] ?]].
  eapply type_ProjT2 ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_ProjTe' :
  forall {Σ Γ A1 A2 p},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjTe p : sHeq A1 (sProjT1 p) A2 (sProjT2 p).
Proof.
  intros Σ Γ A1 A2 p hg hp.
  destruct (istype_type hg hp) as [? i].
  destruct (inversionPack hg i) as [s [[? ?] ?]].
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
  destruct (istype_type hg hp) as [? i].
  destruct (inversionEq hg i) as [? [[[? ?] ?] ?]].
  eapply type_Transport ; eassumption.
Defined.

Lemma type_HeqTypeEq' :
  forall {Σ Γ A u B v p s},
    type_glob Σ ->
    Σ ;;; Γ |-i p : sHeq A u B v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i sHeqTypeEq p : sEq (sSort s) A B.
Proof.
  intros Σ Γ A u B v p s hg hp hA.
  destruct (istype_type hg hp) as [? i].
  destruct (inversionHeq hg i) as [? [[[[? ?] ?] ?] ?]].
  eapply type_HeqTypeEq ; try eassumption.
  destruct (uniqueness pi1_ hA).
  eapply type_conv' ; eassumption.
Defined.

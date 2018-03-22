From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils LiftSubst Typing.
From Translation
     Require Import SAst SInduction SLiftSubst SCommon XTyping ITyping
                    ITypingLemmata ITypingMore PackLifts.

Section Translation.

Open Scope type_scope.
Open Scope x_scope.
Open Scope i_scope.

(*! Relation for translated expressions *)

Reserved Notation " t1 ∼ t2 " (at level 20).

Inductive trel : sterm -> sterm -> Type :=
| trel_Rel x :
    sRel x ∼ sRel x

| trel_Transport_l t1 t2 T1 T2 p :
    t1 ∼ t2 ->
    sTransport T1 T2 p t1 ∼ t2

| trel_Transport_r t1 t2 T1 T2 p :
    t1 ∼ t2 ->
    t1 ∼ sTransport T1 T2 p t2

| trel_Prod n1 n2 A1 A2 B1 B2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    sProd n1 A1 B1 ∼ sProd n2 A2 B2

| trel_Eq A1 A2 u1 u2 v1 v2 :
    A1 ∼ A2 ->
    u1 ∼ u2 ->
    v1 ∼ v2 ->
    sEq A1 u1 v1 ∼ sEq A2 u2 v2

| trel_Sort s :
    sSort s ∼ sSort s

| trel_Lambda n1 n2 A1 A2 B1 B2 u1 u2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    u1 ∼ u2 ->
    sLambda n1 A1 B1 u1 ∼ sLambda n2 A2 B2 u2

| trel_App u1 u2 n1 n2 A1 A2 B1 B2 v1 v2 :
    u1 ∼ u2 ->
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    v1 ∼ v2 ->
    sApp u1 n1 A1 B1 v1 ∼ sApp u2 n2 A2 B2 v2

| trel_Refl A1 A2 u1 u2 :
    A1 ∼ A2 ->
    u1 ∼ u2 ->
    sRefl A1 u1 ∼ sRefl A2 u2

| trel_Ind ind :
    sInd ind ∼ sInd ind

| trel_Construct ind i :
    sConstruct ind i ∼ sConstruct ind i

| trel_Case indn p1 p2 c1 c2 brs1 brs2 :
    p1 ∼ p2 ->
    c1 ∼ c2 ->
    ForallT2 (fun '(_,t1) '(_,t2) => t1 ∼ t2) brs1 brs2 ->
    sCase indn p1 c1 brs1 ∼ sCase indn p2 c2 brs2

where " t1 ∼ t2 " := (trel t1 t2).

Derive Signature for trel.

(* We also define a biased relation that only allows transports on one side,
   the idea being that the term on the other side belongs to the source.
   This might be unnecessary as transport isn't typable in the source but
   hopefully this is more straightforward.
 *)
Reserved Notation " t ⊏ t' " (at level 20).

(* The first is in the source, the second in the target. *)
Inductive inrel : sterm -> sterm -> Type :=
| inrel_Rel x :
    sRel x ⊏ sRel x

| inrel_Transport t t' T1 T2 p :
    t ⊏ t' ->
    t ⊏ sTransport T1 T2 p t'

| inrel_Prod n n' A A' B B' :
    A ⊏ A' ->
    B ⊏ B' ->
    sProd n A B ⊏ sProd n' A' B'

| inrel_Eq A A' u u' v v' :
    A ⊏ A' ->
    u ⊏ u' ->
    v ⊏ v' ->
    sEq A u v ⊏ sEq A' u' v'

| inrel_Sort s :
    sSort s ⊏ sSort s

| inrel_Lambda n n' A A' B B' u u' :
    A ⊏ A' ->
    B ⊏ B' ->
    u ⊏ u' ->
    sLambda n A B u ⊏ sLambda n' A' B' u'

| inrel_App u u' n n' A A' B B' v v' :
    u ⊏ u' ->
    A ⊏ A' ->
    B ⊏ B' ->
    v ⊏ v' ->
    sApp u n A B v ⊏ sApp u' n' A' B' v'

| inrel_Refl A A' u u' :
    A ⊏ A' ->
    u ⊏ u' ->
    sRefl A u ⊏ sRefl A' u'

| inrel_Ind ind :
    sInd ind ⊏ sInd ind

| inrel_Construct ind i :
    sConstruct ind i ⊏ sConstruct ind i

| inrel_Case indn p1 p2 c1 c2 brs1 brs2 :
    p1 ⊏ p2 ->
    c1 ⊏ c2 ->
    ForallT2 (fun '(_,t1) '(_,t2) => t1 ⊏ t2) brs1 brs2 ->
    sCase indn p1 c1 brs1 ⊏ sCase indn p2 c2 brs2

where " t ⊏ t' " := (inrel t t').

(* Deriving a strong enough induction principle *)
Definition sCaseBrsT2
  (P : sterm -> sterm -> Type) (brs1 brs2 : list (nat * sterm)) :=
  ForallT2 (fun x y => P (snd x) (snd y)) brs1 brs2.

Lemma inrel_rect_list :
  forall P : forall s s0 : sterm, Type,
    (forall x : nat, P (sRel x) (sRel x)) ->
    (forall (t t' T1 T2 p : sterm) (i : t ⊏ t'), P t t' ->
     P t (sTransport T1 T2 p t')) ->
    (forall (n n' : name) (A A' B B' : sterm) (i : A ⊏ A'),
     P A A' -> forall i0 : B ⊏ B', P B B' ->
     P (sProd n A B) (sProd n' A' B')) ->
    (forall (A A' u u' v v' : sterm) (i : A ⊏ A'), P A A' ->
     forall i0 : u ⊏ u', P u u' ->
     forall i1 : v ⊏ v', P v v' ->
     P (sEq A u v) (sEq A' u' v')) ->
    (forall s : sort, P (sSort s) (sSort s)) ->
    (forall (n n' : name) (A A' B B' u u' : sterm) (i : A ⊏ A'), P A A' ->
     forall i0 : B ⊏ B', P B B' ->
     forall i1 : u ⊏ u', P u u' ->
     P (sLambda n A B u) (sLambda n' A' B' u')) ->
    (forall (u u' : sterm) (n n' : name) (A A' B B' v v' : sterm) (i : u ⊏ u'),
     P u u' ->
     forall i0 : A ⊏ A', P A A' ->
     forall i1 : B ⊏ B', P B B' ->
     forall i2 : v ⊏ v', P v v' ->
     P (sApp u n A B v) (sApp u' n' A' B' v')) ->
    (forall (A A' u u' : sterm) (i : A ⊏ A'), P A A' ->
     forall i0 : u ⊏ u', P u u' ->
     P (sRefl A u) (sRefl A' u')) ->
    (forall ind : inductive, P (sInd ind) (sInd ind)) ->
    (forall (ind : inductive) (i : nat),
     P (sConstruct ind i) (sConstruct ind i)) ->
    (forall (indn : inductive * nat) (p1 p2 c1 c2 : sterm)
       (brs1 brs2 : list (nat * sterm)) (i : p1 ⊏ p2),
     P p1 p2 ->
     forall i0 : c1 ⊏ c2, P c1 c2 ->
     sCaseBrsT2 P brs1 brs2 ->
     P (sCase indn p1 c1 brs1) (sCase indn p2 c2 brs2)) ->
    forall (s s0 : sterm) (i : s ⊏ s0), P s s0.
Proof.
  intros. induction i ; eauto.
  apply X9 ; try assumption.
Abort.

Lemma inrel_trel :
  forall {t t'}, t ⊏ t' -> t ∼ t'.
Proof.
  intros t t' h.
  induction h ; try now constructor.
Defined.

Lemma trel_to_heq' :
  forall {Σ t1 t2},
    type_glob Σ ->
    t1 ∼ t2 ->
    forall {Γ Γ1 Γ2 Γm T1 T2},
      ismix Σ Γ Γ1 Γ2 Γm ->
      Σ ;;; Γ ,,, Γ1 |-i t1 : T1 ->
      Σ ;;; Γ ,,, Γ2 |-i  t2 : T2 ->
      ∑ p,
        Σ ;;; Γ ,,, Γm |-i p : sHeq (llift0 #|Γm| T1)
                                   (llift0 #|Γm| t1)
                                   (rlift0 #|Γm| T2)
                                   (rlift0 #|Γm| t2).
Proof.
  intros Σ t1 t2 hg sim.
  induction sim ; intros Γ Γ1 Γ2 Γm U1 U2 hm h1 h2.

  (* Variable case *)
  - unfold llift at 2. unfold rlift at 2.
    case_eq (x <? 0) ; intro e ; bprop e ; try omega.
    clear e0.
    change (0 + #|Γm|)%nat with #|Γm|.
    case_eq (x <? #|Γm|) ; intro e0 ; bprop e0.
    + exists (sProjTe (sRel x)). apply type_ProjTe' ; try assumption.
      destruct (inversionRel hg h1) as [is1 [s1 hx1]].
      destruct (inversionRel hg h2) as [is2 [s2 hx2]].
      assert (is1' : x < #|Γ1|) by (erewrite mix_length1 in e1 ; eassumption).
      assert (is2' : x < #|Γ2|) by (erewrite mix_length2 in e1 ; eassumption).
      cbn in hx1. erewrite @safe_nth_lt with (isdecl' := is1') in hx1.
      cbn in hx2. erewrite @safe_nth_lt with (isdecl' := is2') in hx2.
      eapply type_conv'.
      * assumption.
      * eapply type_Rel. eapply @wf_llift with (Δ := []) ; try eassumption.
        eapply typing_wf ; eassumption.
      * erewrite safe_nth_lt. erewrite safe_nth_mix by eassumption.
        cbn. eapply cong_Pack.
        -- rewrite lift_llift.
           replace (S x + (#|Γm| - S x))%nat with #|Γm| by omega.
           match goal with
           | |- _ ;;; _ |-i _ = _ : ?S => change S with (llift0 #|Γm| S)
           end.
           eapply cong_llift0 ; eassumption.
        -- rewrite lift_rlift.
           replace (S x + (#|Γm| - S x))%nat with #|Γm| by omega.
           match goal with
           | |- _ ;;; _ |-i _ = _ : ?S => change S with (rlift0 #|Γm| S)
           end.
           eapply cong_rlift0 ; try eassumption.
           destruct (eq_typing hg hx1) as [ht1 _].
           destruct (eq_typing hg hx2) as [ht2 _].
           destruct (ismix_nth_sort hg hm x is1' is2') as [s [ht1' ht2']].
           instantiate (1 := is2').
           destruct (uniqueness ht1' ht1) as [? eq1].
           destruct (uniqueness ht2 ht2') as [z eq2].
           destruct (eq_typing hg eq1) as [hs1 _].
           destruct (eq_typing hg eq2) as [_ hs2].
           assert (hs2' : Σ;;; Γ ,,, Γ1 |-i sSort s : sSort z).
           { eapply strengthen_sort ; [ eassumption |].
             eapply typing_wf ; eassumption.
           }
           destruct (uniqueness hs1 hs2') as [? ?].
           eapply eq_conv ; [ eassumption |].
           eapply eq_transitivity ; [ eassumption |].
           eapply strengthen_sort_eq.
           ++ eapply eq_conv ; eassumption.
           ++ eapply typing_wf ; eassumption.
    + assert (h1' : Σ ;;; Γ ,,, Γm |-i sRel x : llift0 #|Γm| U1).
      { replace (sRel x) with (llift0 #|Γm| (sRel x))
          by (unfold llift ; rewrite e ; rewrite e0 ; reflexivity).
        eapply type_llift0 ; eassumption.
      }
      assert (h2' : Σ ;;; Γ ,,, Γm |-i sRel x : rlift0 #|Γm| U2).
      { replace (sRel x) with (rlift0 #|Γm| (sRel x))
          by (unfold rlift ; rewrite e ; rewrite e0 ; reflexivity).
        eapply type_rlift0 ; eassumption.
      }
      destruct (uniqueness h1' h2') as [s ee].
      destruct (eq_typing hg ee) as [hlU1 hrU2].
      exists (sHeqRefl (llift0 #|Γm| U1) (sRel x)).
      eapply type_conv'.
      * assumption.
      * eapply type_HeqRefl ; eassumption.
      * apply cong_Heq.
        all: try (apply eq_reflexivity).
        all: easy.

  (* Left transport *)
  - destruct (inversionTransport hg h1) as [s [[[[? ht1] hT1] ?] ?]].
    destruct (IHsim _ _ _ _ _ _ hm ht1 h2) as [q hq].
    cbn.
    exists (sHeqTrans (sHeqSym (sHeqTransport (llift0 #|Γm| p) (llift0 #|Γm| t1))) q).
    eapply type_HeqTrans' ; try assumption.
    + eapply type_HeqSym' ; try assumption.
      eapply type_conv.
      * eapply type_HeqTransport' ; try assumption.
        -- eapply type_llift0 ; eassumption.
        -- instantiate (2 := s). instantiate (1 := llift0 #|Γm| T2).
           change (sEq (sSort s) (llift0 #|Γm| T1) (llift0 #|Γm| T2))
             with (llift0 #|Γm| (sEq (sSort s) T1 T2)).
           eapply type_llift0 ; eassumption.
      * instantiate (1 := succ_sort s).
        change (sSort (succ_sort s)) with (llift0 #|Γm| (sSort (succ_sort s))).
        instantiate (1 := llift0 #|Γm| t1).
        instantiate (1 := llift0 #|Γm| T1).
        match goal with
        | |- ?Σ ;;; ?Γ |-i ?T : ?s =>
          change T with (llift0 #|Γm| (sHeq T1 t1 U1 (sTransport T1 T2 p t1)))
        end.
        eapply type_llift0 ; try eassumption.
        cbn. apply type_Heq ; try assumption.
        apply (eq_typing hg pi2_0).
      * apply cong_Heq.
        all: try (apply eq_reflexivity).
        1-3: change (sSort s) with (llift0 #|Γm| (sSort s)).
        1,3: eapply type_llift0 ; try eassumption.
        -- eapply cong_llift0 ; eassumption.
        -- cbn.
           match goal with
           | |- ?Σ ;;; ?Γ |-i ?T : ?s =>
             change T with (llift0 #|Γm| (sTransport T1 T2 p t1))
           end.
           eapply type_llift0 ; try eassumption.
           eapply type_Transport ; eassumption.
    + assumption.

  (* Right transport *)
  - destruct (inversionTransport hg h2) as [s [[[[? ht2] hT1] ?] ?]].
    destruct (IHsim _ _ _ _ _ _ hm h1 ht2) as [q hq].
    cbn.
    exists (sHeqTrans q (sHeqTransport (rlift0 #|Γm| p) (rlift0 #|Γm| t2))).
    eapply type_HeqTrans' ; try assumption.
    + eassumption.
    + eapply type_conv.
      * eapply type_HeqTransport' ; try assumption.
        -- eapply type_rlift0 ; eassumption.
        -- instantiate (2 := s). instantiate (1 := rlift0 #|Γm| T2).
           change (sEq (sSort s) (rlift0 #|Γm| T1) (rlift0 #|Γm| T2))
             with (rlift0 #|Γm| (sEq (sSort s) T1 T2)).
           eapply type_rlift0 ; eassumption.
      * instantiate (1 := succ_sort s).
        change (sSort (succ_sort s)) with (rlift0 #|Γm| (sSort (succ_sort s))).
        match goal with
        | |- ?Σ ;;; ?Γ |-i ?T : ?s =>
          change T with (rlift0 #|Γm| (sHeq T1 t2 U2 (sTransport T1 T2 p t2)))
        end.
        eapply type_rlift0 ; try eassumption.
        cbn. apply type_Heq ; try assumption.
        apply (eq_typing hg pi2_0).
      * apply cong_Heq.
        all: try (apply eq_reflexivity).
        1-3: change (sSort s) with (rlift0 #|Γm| (sSort s)).
        4: match goal with
           | |- ?Σ ;;; ?Γ |-i ?T : ?s =>
             change T with (rlift0 #|Γm| (sTransport T1 T2 p t2))
           end.
        1,3,4: eapply type_rlift0 ; try eassumption.
        -- cbn. eapply type_Transport ; eassumption.
        -- eapply cong_rlift0 ; eassumption.

  (* Prod *)
  - destruct (inversionProd hg h1) as [s1 [z1 [[hA1 hB1] ?]]].
    destruct (inversionProd hg h2) as [s2 [z2 [[hA2 hB2] ?]]].
    destruct (IHsim1 _ _ _ _ _ _ hm hA1 hA2) as [pA hpA].
    destruct (istype_type hg hpA) as [? iA].
    destruct (inversionHeq hg iA) as [ss' [[[[hs1 hs2] ?] ?] ?]].
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, svass n1 A1)
                    (Γ2 ,, svass n2 A2)
                    (Γm ,, svass n1 (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor.
      - assumption.
      - eassumption.
      - cbn in hs1, hs2.
        pose proof (sorts_in_sort hs2 hs1) as hs.
        eapply @type_conv' with (s := ss') ; try eassumption.
        eapply strengthen_sort_eq ; try eassumption.
        eapply typing_wf ; eassumption.
    }
    destruct (IHsim2 _ _ _ _ _ _ hm' hB1 hB2) as [pB hpB].
    exists (sCongProd (llift #|Γm| 1 B1) (rlift #|Γm| 1 B2) pA pB).
    destruct (istype_type hg hpB) as [? iB].
    destruct (inversionHeq hg iB) as [? [[[[? ?] ?] ?] ?]].
    eapply type_conv' ; try assumption.
    + eapply type_CongProd' ; try assumption.
      * eassumption.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * change (sSort z1) with (llift #|Γm| 1 (sSort z1)).
        eapply type_llift1 ; eassumption.
      * change (sSort z2) with (rlift #|Γm| 1 (sSort z2)).
        eapply type_rlift1 ; eassumption.
    + cbn. apply cong_Heq.
      all: try (apply eq_reflexivity).
      * instantiate (1 := succ_sort (max_sort s1 z1)).
        change (sSort (max_sort s1 z1))
          with (llift0 #|Γm| (sSort (max_sort s1 z1))).
        change (sSort (succ_sort (max_sort s1 z1)))
          with (llift0 #|Γm| (sSort (succ_sort (max_sort s1 z1)))).
        eapply cong_llift0 ; eassumption.
      * change (sSort (max_sort s2 z2))
          with (rlift0 #|Γm| (sSort (max_sort s2 z2))).
        change (sSort (succ_sort (max_sort s1 z1)))
          with (rlift0 #|Γm| (sSort (succ_sort (max_sort s1 z1)))).
        eapply cong_rlift0 ; try eassumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        assert (hB1' : Σ;;; Γ ,,, Γm ,, svass n1 (llift0 #|Γm| A1) |-i llift #|Γm| 1 B1 : sSort z1).
        { change (sSort z1) with (llift #|Γm| 1 (sSort z1)).
           eapply type_llift1 ; eassumption.
        }
        assert (hB2' : Σ;;; Γ ,,, Γm ,, svass n2 (rlift0 #|Γm| A2) |-i rlift #|Γm| 1 B2 : sSort z2).
        { change (sSort z2) with (rlift #|Γm| 1 (sSort z2)).
           eapply type_rlift1 ; eassumption.
        }
        destruct (prod_sorts hg hpA hpB hB1' hB2')
          as [ss [zz [mm [[? ?] eqm]]]].
        eapply eq_conv.
        -- eassumption.
        -- eapply strengthen_sort_eq.
           ++ eapply eq_symmetry.
              eapply cong_succ_sort.
              eassumption.
           ++ eapply typing_wf. eassumption.
      * apply type_Prod.
        -- assumption.
        -- change (sSort z1) with (llift #|Γm| 1 (sSort z1)).
           eapply type_llift1 ; eassumption.
      * apply type_Prod.
        -- assumption.
        -- change (sSort z2) with (rlift #|Γm| 1 (sSort z2)).
           eapply type_rlift1 ; eassumption.

  (* Eq *)
  - destruct (inversionEq hg h1) as [s1 [[[hA1 hu1] hv1] eqA]].
    destruct (inversionEq hg h2) as [s2 [[[hA2 hu2] hv2] eqB]].
    destruct (IHsim1 _ _ _ _ _ _ hm hA1 hA2) as [pA hpA].
    destruct (IHsim2 _ _ _ _ _ _ hm hu1 hu2) as [pu hpu].
    destruct (IHsim3 _ _ _ _ _ _ hm hv1 hv2) as [pv hpv].
    exists (sCongEq pA pu pv).
    eapply type_conv' ; try assumption.
    + eapply type_CongEq' ; eassumption.
    + apply cong_Heq.
      * change (sSort s1) with (llift0 #|Γm| (sSort s1)).
        instantiate (1 := (succ_sort s1)).
        change (sSort (succ_sort s1))
          with (llift0 #|Γm| (sSort (succ_sort s1))).
        eapply cong_llift0 ; eassumption.
      * change (sSort s2) with (rlift0 #|Γm| (sSort s2)).
        change (sSort (succ_sort s1))
          with (rlift0 #|Γm| (sSort (succ_sort s1))).
        eapply cong_rlift0 ; try eassumption.
        destruct (istype_type hg hpA) as [? iA].
        destruct (inversionHeq hg iA) as [? [[[[es1 es2] ?] ?] ?]].
        cbn in es1, es2.
        pose proof (sorts_in_sort es2 es1) as ess.
        eapply eq_conv.
        -- eassumption.
        -- eapply cong_succ_sort. eapply strengthen_sort_eq.
           ++ eassumption.
           ++ eapply typing_wf. eassumption.
      * apply eq_reflexivity.
        change (sSort s1) with (llift0 #|Γm| (sSort s1)).
        eapply type_llift0 ; try assumption.
        -- apply type_Eq ; eassumption.
        -- eassumption.
      * apply eq_reflexivity.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)).
        eapply type_rlift0 ; try assumption.
        -- apply type_Eq ; eassumption.
        -- eassumption.

  (* Sort *)
  - pose proof (inversionSort hg h1) as e1.
    pose proof (inversionSort hg h2) as e2.
    exists (sHeqRefl (sSort (succ_sort s)) (sSort s)).
    assert (hwf : wf Σ (Γ ,,, Γm)).
    { eapply @wf_llift with (Δ := []) ; try eassumption.
      eapply typing_wf ; eassumption.
    }
    eapply type_conv' ; try assumption.
    + eapply type_HeqRefl' ; try assumption.
      apply type_Sort. eassumption.
    + cbn. apply cong_Heq.
      * instantiate (1 := succ_sort (succ_sort s)).
        change (sSort (succ_sort s))
          with (llift0 #|Γm| (sSort (succ_sort s))).
        change (sSort (succ_sort (succ_sort s)))
          with (llift0 #|Γm| (sSort (succ_sort (succ_sort s)))).
        eapply cong_llift0 ; eassumption.
      * change (sSort (succ_sort s))
          with (rlift0 #|Γm| (sSort (succ_sort s))).
        change (sSort (succ_sort (succ_sort s)))
          with (rlift0 #|Γm| (sSort (succ_sort (succ_sort s)))).
        eapply cong_rlift0 ; eassumption.
      * apply eq_reflexivity. apply type_Sort. eassumption.
      * apply eq_reflexivity. apply type_Sort. eassumption.

  (* Lambda *)
  - destruct (inversionLambda hg h1) as [s1 [z1 [[[hA1 hB1] hu1] eq1]]].
    destruct (inversionLambda hg h2) as [s2 [z2 [[[hA2 hB2] hu2] eq2]]].
    destruct (IHsim1 _ _ _ _ _ _ hm hA1 hA2) as [pA hpA].
    destruct (istype_type hg hpA) as [? iA].
    destruct (inversionHeq hg iA) as [ss' [[[[hs1 hs2] ?] ?] ?]].
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, svass n1 A1)
                    (Γ2 ,, svass n2 A2)
                    (Γm ,, svass n1 (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor.
      - assumption.
      - eassumption.
      - cbn in hs1, hs2.
        pose proof (sorts_in_sort hs2 hs1) as hs.
        eapply @type_conv' with (s := ss') ; try eassumption.
        eapply strengthen_sort_eq ; try eassumption.
        eapply typing_wf ; eassumption.
    }
    destruct (IHsim2 _ _ _ _ _ _ hm' hB1 hB2) as [pB hpB].
    destruct (IHsim3 _ _ _ _ _ _ hm' hu1 hu2) as [pu hpu].
    exists (sCongLambda (llift #|Γm| 1 B1) (rlift #|Γm| 1 B2)
                   (llift #|Γm| 1 u1) (rlift #|Γm| 1 u2) pA pB pu).
    eapply type_conv' ; try assumption.
    + eapply type_CongLambda' ; try assumption.
      * eassumption.
      * rewrite llift_substProj, rlift_substProj. apply hpB.
      * rewrite !llift_substProj, !rlift_substProj. apply hpu.
      * change (sSort z1) with (llift #|Γm| 1 (sSort z1)).
        eapply type_llift1 ; eassumption.
      * change (sSort z2) with (rlift #|Γm| 1 (sSort z2)).
        eapply type_rlift1 ; eassumption.
      * eapply type_llift1 ; eassumption.
      * eapply type_rlift1 ; eassumption.
    + cbn. apply cong_Heq.
      all: try (apply eq_reflexivity).
      * match goal with
        | |- _ ;;; _ |-i ?T = _ : ?S =>
          change T with (llift0 #|Γm| (sProd n1 A1 B1)) ;
          change S with (llift0 #|Γm| S)
        end.
        eapply cong_llift0 ; eassumption.
      * match goal with
        | |- _ ;;; _ |-i ?T = _ : ?S =>
          change T with (rlift0 #|Γm| (sProd n2 A2 B2)) ;
          change S with (rlift0 #|Γm| S)
        end.
        eapply cong_rlift0 ; try eassumption.
        assert (hB1' : Σ;;; Γ ,,, Γm ,, svass n1 (llift0 #|Γm| A1) |-i llift #|Γm| 1 B1 : sSort z1).
        { change (sSort z1) with (llift #|Γm| 1 (sSort z1)).
          eapply type_llift1 ; eassumption.
        }
        assert (hB2' : Σ;;; Γ ,,, Γm ,, svass n2 (rlift0 #|Γm| A2) |-i rlift #|Γm| 1 B2 : sSort z2).
        { change (sSort z2) with (rlift #|Γm| 1 (sSort z2)).
          eapply type_rlift1 ; eassumption.
        }
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        destruct (prod_sorts hg hpA hpB hB1' hB2') as [ss [zz [mm [[? ?] eqm]]]].
        eapply eq_conv ; try eassumption.
        eapply eq_symmetry. eapply strengthen_sort_eq.
        -- eassumption.
        -- eapply typing_wf. eassumption.
      * match goal with
        | |- _ ;;; _ |-i ?t : ?T =>
          change T with (llift0 #|Γm| (sProd n1 A1 B1)) ;
          change t with (llift0 #|Γm| (sLambda n1 A1 B1 u1))
        end.
        eapply type_llift0 ; try eassumption.
        eapply type_Lambda ; eassumption.
      * match goal with
        | |- _ ;;; _ |-i ?t : ?T =>
          change T with (rlift0 #|Γm| (sProd n2 A2 B2)) ;
          change t with (rlift0 #|Γm| (sLambda n2 A2 B2 u2))
        end.
        eapply type_rlift0 ; try eassumption.
        eapply type_Lambda ; eassumption.

  (* App *)
  - destruct (inversionApp hg h1) as [s1 [z1 [[[[hA1 hB1] hu1] hv1] e1]]].
    destruct (inversionApp hg h2) as [s2 [z2 [[[[hA2 hB2] hu2] hv2] e2]]].
    destruct (IHsim1 _ _ _ _ _ _ hm hu1 hu2) as [pu hpu].
    destruct (IHsim2 _ _ _ _ _ _ hm hA1 hA2) as [pA hpA].
    destruct (istype_type hg hpA) as [? iA].
    destruct (inversionHeq hg iA) as [ss' [[[[hs1 hs2] ?] ?] ?]].
    assert (hm' :
              ismix Σ Γ
                    (Γ1 ,, svass n1 A1)
                    (Γ2 ,, svass n2 A2)
                    (Γm ,, svass n1 (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
    ).
    { econstructor.
      - assumption.
      - eassumption.
      - cbn in hs1, hs2.
        pose proof (sorts_in_sort hs2 hs1) as hs.
        eapply @type_conv' with (s := ss') ; try eassumption.
        eapply strengthen_sort_eq ; try eassumption.
        eapply typing_wf ; eassumption.
    }
    destruct (IHsim3 _ _ _ _ _ _ hm' hB1 hB2) as [pB hpB].
    destruct (IHsim4 _ _ _ _ _ _ hm hv1 hv2) as [pv hpv].
    exists (sCongApp (llift #|Γm| 1 B1) (rlift #|Γm| 1 B2) pu pA pB pv).
    eapply type_conv' ; try assumption.
    + eapply type_CongApp' ; try assumption.
      * apply hpA.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * apply hpu.
      * apply hpv.
      * change (sSort z1) with (llift #|Γm| 1 (sSort z1)).
        eapply type_llift1 ; eassumption.
      * change (sSort z2) with (rlift #|Γm| 1 (sSort z2)).
        eapply type_rlift1 ; eassumption.
    + cbn. apply cong_Heq.
      all: try (apply eq_reflexivity).
      * rewrite <- llift_subst. cbn.
        match goal with
        | |- _ ;;; _ |-i _ = _ : ?S =>
          change S with (llift0 #|Γm| S)
        end.
        eapply cong_llift0 ; eassumption.
      * rewrite <- rlift_subst. cbn.
        match goal with
        | |- _ ;;; _ |-i _ = _ : ?S =>
          change S with (rlift0 #|Γm| S)
        end.
        eapply cong_rlift0 ; try eassumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        assert (hB1' : Σ;;; Γ ,,, Γm ,, svass n1 (llift0 #|Γm| A1) |-i llift #|Γm| 1 B1 : sSort z1).
        { change (sSort z1) with (llift #|Γm| 1 (sSort z1)).
           eapply type_llift1 ; eassumption.
        }
        assert (hB2' : Σ;;;Γ ,,, Γm ,, svass n2 (rlift0 #|Γm| A2) |-i rlift #|Γm| 1 B2 : sSort z2).
        { change (sSort z2) with (rlift #|Γm| 1 (sSort z2)).
           eapply type_rlift1 ; eassumption.
        }
        destruct (prod_sorts hg hpA hpB hB1' hB2')
          as [ss [zz [mm [[? ?] eqm]]]].
        eapply eq_conv.
        -- eassumption.
        -- eapply strengthen_sort_eq.
           ++ eassumption.
           ++ eapply typing_wf. eassumption.
      * rewrite <- llift_subst. cbn.
        match goal with
        | |- _ ;;; _ |-i ?t : _ =>
          change t with (llift0 #|Γm| (sApp u1 n1 A1 B1 v1))
        end.
        eapply type_llift0 ; try eassumption.
        eapply type_App ; eassumption.
      * rewrite <- rlift_subst. cbn.
        match goal with
        | |- _ ;;; _ |-i ?t : _ =>
          change t with (rlift0 #|Γm| (sApp u2 n2 A2 B2 v2))
        end.
        eapply type_rlift0 ; [ assumption | | eassumption ].
        eapply type_App ; eassumption.

  (* Refl *)
  - destruct (inversionRefl hg h1) as [s1 [[hA1 hu1] e1]].
    destruct (inversionRefl hg h2) as [s2 [[hA2 hu2] e2]].
    destruct (IHsim1 _ _ _ _ _ _ hm hA1 hA2) as [pA hpA].
    destruct (IHsim2 _ _ _ _ _ _ hm hu1 hu2) as [pu hpu].
    exists (sCongRefl pA pu).
    eapply type_conv' ; try assumption.
    + eapply type_CongRefl' ; eassumption.
    + apply cong_Heq.
      all: try apply eq_reflexivity.
      * match goal with
        | |- ?Σ ;;; ?Γ |-i ?u = ?v : ?A =>
          change u with (llift0 #|Γm| (sEq A1 u1 u1)) ;
          change A with (llift0 #|Γm| A)
        end.
        eapply cong_llift0 ; try eassumption.
      * match goal with
        | |- ?Σ ;;; ?Γ |-i ?u = ?v : ?A =>
          change u with (rlift0 #|Γm| (sEq A2 u2 u2)) ;
          change A with (rlift0 #|Γm| A)
        end.
        eapply cong_rlift0 ; try assumption.
        -- destruct (istype_type hg hpA) as [? iA].
           destruct (inversionHeq hg iA) as [? [[[[es1 es2] ?] ?] ?]].
           cbn in es1, es2.
           eapply eq_conv.
           ++ eassumption.
           ++ eapply strengthen_sort_eq.
              ** eapply sorts_in_sort ; eassumption.
              ** eapply typing_wf. eassumption.
        -- eassumption.
      * match goal with
        | |- ?Σ ;;; ?Γ |-i ?u : ?A =>
          change A with (llift0 #|Γm| (sEq A1 u1 u1))
        end.
        eapply type_llift0 ; try assumption.
        -- eapply type_Refl ; eassumption.
        -- eassumption.
      * match goal with
        | |- ?Σ ;;; ?Γ |-i ?u : ?A =>
          change A with (rlift0 #|Γm| (sEq A2 u2 u2))
        end.
        eapply type_rlift0 ; try assumption.
        -- eapply type_Refl ; eassumption.
        -- eassumption.

  (* Ind *)
  - destruct (inversionInd hg h1) as [univs1 [decl1 [isdecl1 [s1 e1]]]].
    destruct (inversionInd hg h2) as [univs2 [decl2 [isdecl2 [s2 e2]]]].
    assert (h1' : Σ ;;; Γ ,,, Γm |-i sInd ind : llift0 #|Γm| U1).
    { change (sInd ind) with (llift0 #|Γm| (sInd ind)).
      eapply type_llift0 ; eassumption.
    }
    assert (h2' : Σ ;;; Γ ,,, Γm |-i sInd ind : rlift0 #|Γm| U2).
    { change (sInd ind) with (rlift0 #|Γm| (sInd ind)).
      eapply type_rlift0 ; eassumption.
    }
    destruct (uniqueness h1' h2') as [s ee].
    destruct (eq_typing hg ee) as [hlU1 hrU2].
    exists (sHeqRefl (llift0 #|Γm| U1) (sInd ind)).
    eapply type_conv' ; try assumption.
    + eapply type_HeqRefl ; eassumption.
    + eapply cong_Heq.
      all: try (apply eq_reflexivity).
      all: easy.

  (* Construct *)
  - destruct (inversionConstruct hg h1) as [univs1 [decl1 [isdecl1 [s1 e1]]]].
    destruct (inversionConstruct hg h2) as [univs2 [decl2 [isdecl2 [s2 e2]]]].
    assert (h1' : Σ ;;; Γ ,,, Γm |-i sConstruct ind i : llift0 #|Γm| U1).
    { change (sConstruct ind i) with (llift0 #|Γm| (sConstruct ind i)).
      eapply type_llift0 ; eassumption.
    }
    assert (h2' : Σ ;;; Γ ,,, Γm |-i sConstruct ind i : rlift0 #|Γm| U2).
    { change (sConstruct ind i) with (rlift0 #|Γm| (sConstruct ind i)).
      eapply type_rlift0 ; eassumption.
    }
    destruct (uniqueness h1' h2') as [s ee].
    destruct (eq_typing hg ee) as [hlU1 hrU2].
    exists (sHeqRefl (llift0 #|Γm| U1) (sConstruct ind i)).
    eapply type_conv' ; try assumption.
    + eapply type_HeqRefl ; eassumption.
    + eapply cong_Heq.
      all: try (apply eq_reflexivity).
      all: easy.

  (* Case *)
  -

  Unshelve.
  all: cbn ; try rewrite !length_cat ; omega.
Defined.

Corollary trel_to_heq :
  forall {Σ Γ T1 T2} {t1 t2 : sterm},
    type_glob Σ ->
    t1 ∼ t2 ->
    Σ ;;; Γ |-i t1 : T1 ->
    Σ ;;; Γ |-i t2 : T2 ->
    ∑ p, Σ ;;; Γ |-i p : sHeq T1 t1 T2 t2.
Proof.
  intros Σ Γ T1 T2 t1 t2 hg h h1 h2.
  destruct (@trel_to_heq' _ _ _ hg h _ nil nil _ _ _ (mixnil _ _) h1 h2)
    as [p hp].
  cbn in hp. rewrite !llift00, !rlift00 in hp.
  exists p. apply hp.
Defined.

Lemma inrel_lift :
  forall {t t'},
    t ⊏ t' ->
    forall n k, lift n k t ⊏ lift n k t'.
Proof.
  intros  t t'. induction 1 ; intros m k.
  all: try (cbn ; now constructor).
  cbn. destruct (k <=? x) ; now constructor.
Defined.

Lemma inrel_subst :
  forall {t t'},
    t ⊏ t' ->
    forall {u u'},
      u ⊏ u' ->
      forall n, t{ n := u } ⊏ t'{ n := u' }.
Proof.
  intros t t'. induction 1 ; intros v1 v2 hu m.
  all: try (cbn ; constructor ; easy).
  cbn. destruct (m ?= x).
  - now apply inrel_lift.
  - constructor.
  - constructor.
Defined.

Lemma trel_lift :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall n k, lift n k t1 ∼ lift n k t2.
Proof.
  intros t1 t2. induction 1 ; intros n k.
  all: try (cbn ; now constructor).
  cbn. destruct (k <=? x) ; now constructor.
Defined.

Lemma trel_subst :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall {u1 u2},
      u1 ∼ u2 ->
      forall n, t1{ n := u1 } ∼ t2{ n := u2 }.
Proof.
  intros t1 t2. induction 1 ; intros m1 m2 hu n.
  all: try (cbn ; constructor ; easy).
  unfold subst. destruct (nat_compare n x).
  - now apply trel_lift.
  - apply trel_Rel.
  - apply trel_Rel.
Defined.

(* Reflexivity is restricted to the syntax that makes sense in ETT. *)
Lemma trel_refl :
  forall {t},
    Xcomp t ->
    t ∼ t.
Proof.
  intros t h. dependent induction h.
  all: constructor. all: assumption.
Defined.

Lemma inrel_refl :
  forall {t},
    Xcomp t ->
    t ⊏ t.
Proof.
  intros t h. dependent induction h.
  all: constructor. all: assumption.
Defined.

Lemma trel_sym : forall {t1 t2}, t1 ∼ t2 -> t2 ∼ t1.
Proof.
  intros t1 t2. induction 1 ; (now constructor).
Defined.

Lemma inversion_trel_transport :
  forall {A B p t1 t2},
    sTransport A B p t1 ∼ t2 ->
    t1 ∼ t2.
Proof.
  intros A B p t1 t2 h.
  dependent induction h.
  - assumption.
  - constructor. eapply IHh.
Defined.

Lemma trel_trans :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall {t3},
      t2 ∼ t3 ->
      t1 ∼ t3.
Proof.
  intros t1 t2. induction 1 ; intros t3 h.
  all: try (
    dependent induction h ; [
      constructor ; eapply IHh ; assumption
    | now constructor
    ]
  ).
  - constructor. now apply IHtrel.
  - apply IHtrel. eapply inversion_trel_transport. eassumption.
Defined.

Reserved Notation " Γ ≈ Δ " (at level 19).

Inductive crel : scontext -> scontext -> Type :=
| crel_empty : nil ≈ nil
| crel_snoc Γ Δ n t m u : Γ ≈ Δ -> t ∼ u -> (Γ ,, svass n t) ≈ (Δ ,, svass m u)

where " Γ ≈ Δ " := (crel Γ Δ).

Reserved Notation " Γ ⊂ Γ' " (at level 19).

Inductive increl : scontext -> scontext -> Type :=
| increl_empty : nil ⊂ nil
| increl_snoc Γ Γ' n n' T T' :
    Γ ⊂ Γ' -> T ⊏ T' -> (Γ ,, svass n T) ⊂ (Γ' ,, svass n' T')

where " Γ ⊂ Γ' " := (increl Γ Γ').

(*! Notion of translation *)
Definition trans Σ Γ A t Γ' A' t' :=
  Γ ⊂ Γ' *
  A ⊏ A' *
  t ⊏ t' *
  (Σ ;;; Γ' |-i t' : A').

Notation " Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [ t ] : A ⟧ " :=
  (trans Σ Γ A t Γ' A' t')
    (at level 7) : i_scope.

Definition ctxtrans Σ Γ Γ' :=
  Γ ⊂ Γ' * (wf Σ Γ').

Notation " Σ |--i Γ' # ⟦ Γ ⟧ " := (ctxtrans Σ Γ Γ') (at level 7) : i_scope.

(* Notion of head *)
Inductive head_kind :=
| headRel
| headSort (s : sort)
| headProd
| headLambda
| headApp
| headEq
| headRefl
| headJ
| headTransport
| headHeq
| headOther
.

Definition head (t : sterm) : head_kind :=
  match t with
  | sRel x => headRel
  | sSort s => headSort s
  | sProd n A B => headProd
  | sLambda n A B t => headLambda
  | sApp u n A B v => headApp
  | sEq A u v => headEq
  | sRefl A u => headRefl
  | sJ A u P w v p => headJ
  | sTransport A B p t => headTransport
  | sHeq A a B b => headHeq
  (* We actually only care about type heads in the source *)
  | _ => headOther
  end.

Inductive transport_data :=
| trd (T1 T2 p : sterm).

Definition transport_data_app (td : transport_data) (t : sterm) : sterm :=
  match td with
  | trd T1 T2 p => sTransport T1 T2 p t
  end.

Definition transport_seq := list transport_data.

Definition transport_seq_app (tr : transport_seq) (t : sterm) : sterm :=
  List.fold_right transport_data_app t tr.

Lemma trel_transport_seq :
  forall {A A'},
    A ⊏ A' ->
    ∑ A'' (tseq : transport_seq),
      (head A'' = head A) *
      (A' = transport_seq_app tseq A'') *
      (A ⊏ A'').
Proof.
  intros A A' h.
  induction h.
 all : try (eexists ; exists nil ; split;  [split ; [idtac | reflexivity]| idtac]; [reflexivity | now constructor ]).

  destruct IHh as [A'' [tseq [[hh he] hsub]]].
  exists A'', (trd T1 T2 p :: tseq). split ; [split | idtac].
  assumption.
  cbn. now f_equal.
  assumption.
Defined.

(* We only need it for heads in the source *)
Inductive type_head : head_kind -> Type :=
| type_headSort s : type_head (headSort s)
| type_headProd : type_head headProd
| type_headEq : type_head headEq
.

Lemma inversion_transportType :
  forall {Σ tseq Γ' A' T},
    type_glob Σ ->
    type_head (head A') ->
    Σ ;;; Γ' |-i transport_seq_app tseq A' : T ->
    ∑ s,
      (Σ ;;; Γ' |-i A' : sSort s) *
      (Σ ;;; Γ' |-i T : sSort (succ_sort s)).
Proof.
  intros Σ tseq. induction tseq ; intros Γ' A' T hg hh ht.

  - cbn in *. destruct A' ; try (now inversion hh).
    + exists (succ_sort s). repeat split.
      * apply type_Sort. apply (typing_wf ht).
      * eapply (eq_typing hg (inversionSort hg ht)).
    + destruct (inversionProd hg ht) as [s1 [s2 [[? ?] ?]]].
      exists (max_sort s1 s2). repeat split.
      * now apply type_Prod.
      * eapply (eq_typing hg pi2_0).
    + destruct (inversionEq hg ht) as [s [[[? ?] ?] ?]].
      exists s. repeat split.
      * now apply type_Eq.
      * eapply (eq_typing hg pi2_1).

  - destruct a. cbn in ht.
    change (fold_right transport_data_app A' tseq)
      with (transport_seq_app tseq A') in ht.
    destruct (inversionTransport hg ht) as [s [[[[? hA'] hT1] ?] ?]].
    destruct (IHtseq Γ' A' T1 hg hh hA') as [s' [hAs hT1s]].
    exists s'. repeat split.
    + assumption.
    + destruct (eq_typing hg pi2_0) as [_ hT].
      destruct (uniqueness hT1 hT1s) as [s3 hs3].
      eapply type_conv' ; eassumption.
Defined.

Lemma choose_type' :
  forall {Σ A A'},
    type_glob Σ ->
    type_head (head A) ->
    A ⊏ A' ->
    forall {Γ Γ' t t'},
      Γ ⊂ Γ' ->
      t ⊏ t' ->
      (Σ ;;; Γ' |-i t' : A') ->
      ∑ A'',
        (∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧) *
        (head A'' = head A).
Proof.
  intros Σ A A' hg hth hA Γ Γ' t t' hΓ ht h.
  destruct (trel_transport_seq hA) as [A'' [tseq [[hh heq] hrel]]].
  rewrite heq in h.
  destruct (istype_type hg h) as [s hs].
  assert (hth' : type_head (head A'')) by (now rewrite hh).
  destruct (inversion_transportType hg hth' hs) as [s' [h' hss']].
  exists A''. split.
  - assert (simA : A' ∼ A'').
    { apply trel_sym.
      eapply trel_trans.
      - apply trel_sym. apply inrel_trel. eassumption.
      - apply inrel_trel. assumption.
    }
    pose (thm := @trel_to_heq Σ Γ' (sSort s) (sSort s) A' A'' hg simA).
    rewrite <- heq in hs.
    destruct thm as [p hp].
    + assumption.
    + eapply type_conv.
      * eassumption.
      * eassumption.
      * eapply sorts_in_sort.
        -- apply type_Sort. apply (typing_wf h').
        -- assumption.
    + destruct (sort_heq_ex hg hp) as [q hq].
      exists (sTransport A' A'' q t').
      repeat split.
      * assumption.
      * assumption.
      * constructor. assumption.
      * destruct (istype_type hg hq) as [? hEq].
        destruct (inversionEq hg hEq) as [? [[[? ?] ?] ?]].
        eapply type_Transport.
        -- eassumption.
        -- eassumption.
        -- assumption.
        -- subst. assumption.
  - assumption.
Defined.

Lemma choose_type :
  forall {Σ Γ A t Γ' A' t'},
    type_glob Σ ->
    type_head (head A) ->
    Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [t] : A ⟧ ->
    ∑ A'',
      (∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧) *
      (head A'' = head A).
Proof.
  intros Σ Γ A t Γ' A' t' hg htt [[[hΓ hA] ht] h].
  now eapply choose_type'.
Defined.

Lemma change_type :
  forall {Σ Γ A t Γ' A' t' s A''},
    type_glob Σ ->
    Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [t] : A ⟧ ->
    Σ ;;;; Γ' |--- [ A'' ] : sSort s # ⟦ Γ |--- [A] : sSort s ⟧ ->
    ∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧.
Proof.
  intros Σ Γ A t Γ' A' t' s A'' hg [[[rΓ' rA'] rt'] ht'] [[[rΓ'' _] rA''] hA''].
  assert (simA : A' ∼ A'').
  { eapply trel_trans.
    - eapply trel_sym. eapply inrel_trel. eassumption.
    - eapply inrel_trel. eassumption.
  }
  destruct (istype_type hg ht') as [s2 hA'].
  destruct (@trel_to_heq Σ Γ' (sSort s2) (sSort s) A' A'' hg simA) as [p hp].
  - assumption.
  - assumption.
  - destruct (istype_type hg hp) as [s1 hheq].
    assert (Σ ;;; Γ' |-i sSort s : sSort (succ_sort s)).
    { apply type_Sort. apply (typing_wf hp). }
    destruct (inversionHeq hg hheq) as [? [[[[? hs] ?] ?] ?]].
    assert (hp' : Σ ;;; Γ' |-i p : sHeq (sSort s) A' (sSort s) A'').
    { eapply type_conv.
      - eassumption.
      - apply type_Heq ; try eassumption.
        eapply type_conv' ; try assumption.
        + eassumption.
        + apply sorts_in_sort.
          * eapply type_conv' ; try assumption.
            -- eassumption.
            -- apply eq_symmetry. apply (inversionSort hg hs).
          * assumption.
      - apply cong_Heq ; try (apply eq_reflexivity) ; try assumption.
        apply sorts_in_sort ; assumption.
    }
    destruct (sort_heq_ex hg hp') as [q hq].
    exists (sTransport A' A'' q t').
    repeat split.
    + assumption.
    + assumption.
    + constructor. assumption.
    + apply type_Transport with (s := s) ; try assumption.
      eapply type_conv' ; try assumption.
      * eassumption.
      * apply sorts_in_sort.
        -- eapply type_conv' ; try assumption.
           ++ eassumption.
           ++ apply eq_symmetry. apply (inversionSort hg hs).
        -- apply type_Sort. apply (typing_wf hs).
Defined.


(*! Translation *)

Fact length_increl : forall {Γ Γ'}, Γ ⊂ Γ' -> #|Γ| = #|Γ'|.
Proof.
  intros Γ Γ' h.
  dependent induction h.
  - reflexivity.
  - cbn. now f_equal.
Defined.

Fact nth_increl :
  forall {Γ Γ'},
    Γ ⊂ Γ' ->
    forall {n} { isdecl : n < #|Γ| } { isdecl' : n < #|Γ'| },
      sdecl_type (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl))
    ⊏ sdecl_type (safe_nth Γ' (exist (fun n0 : nat => n0 < #|Γ'|) n isdecl')).
Proof.
  intros Γ Γ' e. induction e ; intros m isdecl isdecl'.
  - exfalso. easy.
  - destruct m.
    + cbn. assumption.
    + cbn. apply IHe.
Defined.

Definition trans_snoc {Σ Γ x A s Γ' A' s'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s' # ⟦ Γ |--- [A] : sSort s ⟧ ->
  Σ |--i Γ' ,, svass x A' # ⟦ Γ ,, svass x A ⟧.
Proof.
  intros hΓ hA.
  split.
  - constructor ; now destruct hA as [[[? ?] ?] ?].
  - econstructor.
    + now destruct hΓ.
    + now destruct hA as [[[? ?] ?] ?].
Defined.

Definition trans_Prod {Σ Γ n A B s1 s2 Γ' A' B'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s1 # ⟦ Γ |--- [A] : sSort s1 ⟧ ->
  Σ ;;;; Γ' ,, svass n A' |--- [B'] : sSort s2
  # ⟦ Γ ,, svass n A |--- [B]: sSort s2 ⟧ ->
  Σ ;;;; Γ' |--- [sProd n A' B']: sSort (max_sort s1 s2)
  # ⟦ Γ |--- [ sProd n A B]: sSort (max_sort s1 s2) ⟧.
Proof.
  intros hΓ hA hB.
  destruct hΓ. destruct hA as [[? ?] ?]. destruct hB as [[? ?] ?].
  repeat split.
  - assumption.
  - constructor.
  - now constructor.
  - now eapply type_Prod.
Defined.

Definition trans_Eq {Σ Γ A u v s Γ' A' u' v'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s # ⟦ Γ |--- [A] : sSort s ⟧ ->
  Σ ;;;; Γ' |--- [u'] : A' # ⟦ Γ |--- [u] : A ⟧ ->
  Σ ;;;; Γ' |--- [v'] : A' # ⟦ Γ |--- [v] : A ⟧ ->
  Σ ;;;; Γ' |--- [sEq A' u' v'] : sSort s # ⟦ Γ |--- [sEq A u v] : sSort s ⟧.
Proof.
  intros hΓ hA hu hv.
  destruct hA as [[[? ?] ?] ?].
  destruct hu as [[[? ?] ?] ?].
  destruct hv as [[[? ?] ?] ?].
  repeat split.
  - assumption.
  - constructor.
  - constructor ; assumption.
  - apply type_Eq ; assumption.
Defined.

(* Maybe put this together with the other translation definitions *)
Definition eqtrans Σ Γ A u v Γ' A' A'' u' v' p' :=
  Γ ⊂ Γ' *
  A ⊏ A' *
  A ⊏ A'' *
  u ⊏ u' *
  v ⊏ v' *
  (Σ ;;; Γ' |-i p' : sHeq A' u' A'' v').

Lemma eqtrans_trans :
  forall {Σ Γ A u v Γ' A' A'' u' v' p'},
    type_glob Σ ->
    eqtrans Σ Γ A u v Γ' A' A'' u' v' p' ->
    (Σ ;;;; Γ' |--- [u'] : A' # ⟦ Γ |--- [u] : A ⟧) *
    (Σ ;;;; Γ' |--- [v'] : A'' # ⟦ Γ |--- [v] : A ⟧).
Proof.
  intros Σ Γ A u v Γ' A' A'' u' v' p' hg h.
  destruct h as [[[[[eΓ eS'] eS''] eA] eB] hp'].
  destruct (istype_type hg hp') as [? hheq].
  destruct (inversionHeq hg hheq) as [? [[[[? ?] ?] ?] ?]].
  repeat split ; assumption.
Defined.

Definition complete_translation {Σ} :
  type_glob Σ ->
  (forall Γ (h : XTyping.wf Σ Γ), ∑ Γ', Σ |--i Γ' # ⟦ Γ ⟧ ) *
  (forall { Γ t A} (h : Σ ;;; Γ |-x t : A)
     {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
      ∑ A' t', Σ ;;;; Γ' |--- [t'] : A' # ⟦ Γ |--- [t] : A ⟧) *
  (forall { Γ u v A} (h : Σ ;;; Γ |-x u = v : A)
     {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
      ∑ A' A'' u' v' p',
        eqtrans Σ Γ A u v Γ' A' A'' u' v' p').
Proof.
  intro hg.
  unshelve refine (typing_all Σ
                     (fun Γ (h : XTyping.wf Σ Γ) =>
                        ∑ Γ', Σ |--i Γ' # ⟦ Γ ⟧ )
                     (fun { Γ t A} (h : Σ ;;; Γ |-x t : A) => forall
                          {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
                          ∑ A' t', Σ ;;;; Γ' |--- [t'] : A' # ⟦ Γ |--- [t] : A ⟧)
                     (fun { Γ u v A} (h : Σ ;;; Γ |-x u = v : A) => forall
                    {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
  ∑ A' A'' u' v' p',
    eqtrans Σ Γ A u v Γ' A' A'' u' v' p')
                     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros.
  (** context_translation **)

    (* wf_nil *)
    + exists nil. split ; constructor.

    (* wf_snoc *)
    + destruct X as [Γ' hΓ'].
      rename t into hA.
      destruct (X0 _ hΓ') as [T [A' hA']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA') as [T' [[A'' hA''] hh]].
      destruct T' ; try (now inversion hh).
      exists (Γ' ,, svass x A''). now eapply trans_snoc.

  (** type_translation **)

    (* type_Rel *)
    + assert (isdecl' : n < #|Γ'|).
      { destruct hΓ as [iΓ _]. now rewrite <- (length_increl iΓ). }
      exists (lift0 (S n) (sdecl_type (safe_nth Γ' (exist _ n isdecl')))), (sRel n).
      repeat split.
      * now destruct hΓ.
      * apply inrel_lift. apply nth_increl. now destruct hΓ.
      * constructor.
      * apply type_Rel. now destruct hΓ.

    (* type_Sort *)
    + exists (sSort (succ_sort s)), (sSort s).
      repeat split.
      * now destruct hΓ.
      * constructor.
      * constructor.
      * apply type_Sort. now destruct hΓ.

    (* type_Prod *)
    + (* Translation of the domain *)
      destruct (X _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ ht''))
        as [S' [b' hb']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hb') as [T' [[b'' hb''] hh]].
      clear hb' b' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we conclude *)
      exists (sSort (max_sort s1 s2)), (sProd n t'' b'').
      now apply trans_Prod.

    (* type_Lambda *)
    + (* Translation of the domain *)
      destruct (X _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ ht''))
        as [S' [bty' hbty']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hbty') as [T' [[bty'' hbty''] hh]].
      clear hbty' bty' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the term *)
      destruct (X1 _ (trans_snoc hΓ ht''))
        as [S' [b' hb']].
      destruct (change_type hg hb' hbty'') as [b'' hb''].
      clear hb' S' b'.
      exists (sProd n' t'' bty''), (sLambda n t'' bty'' b'').
      repeat split.
      * now destruct hΓ.
      * constructor.
        -- now destruct ht'' as [[[? ?] ?] ?].
        -- now destruct hbty'' as [[[? ?] ?] ?].
      * constructor.
        -- now destruct ht'' as [[[? ?] ?] ?].
        -- now destruct hbty'' as [[[? ?] ?] ?].
        -- now destruct hb'' as [[[? ?] ?] ?].
      * eapply type_Lambda.
        -- now destruct ht'' as [[[? ?] ?] ?].
        -- now destruct hbty'' as [[[? ?] ?] ?].
        -- now destruct hb'' as [[[? ?] ?] ?].

    (* type_App *)
    + (* Translation of the domain *)
      destruct (X _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the function *)
      destruct (X1 _ hΓ) as [T'' [t'' ht'']].
      assert (th : type_head (head (sProd n A B))) by constructor.
      destruct (choose_type hg th ht'') as [T' [[t' ht'] hh]].
      clear ht'' t'' T''.
      destruct T' ; inversion hh. subst. clear hh th.
      rename T'1 into A'', T'2 into B''.
      destruct (change_type hg ht' (trans_Prod hΓ hA' hB')) as [t'' ht''].
      clear ht' A'' B'' t'.
      (* Translation of the argument *)
      destruct (X2 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hg hu'' hA') as [u' hu'].
      clear hu'' A'' u''.
      (* We now conclude *)
      exists (B'{ 0 := u' }), (sApp t'' n A' B' u').
      destruct hΓ.
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht'' as [[[? ?] ?] ?].
      destruct hu' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * now apply inrel_subst.
      * now constructor.
      * eapply type_App ; eassumption.

    (* type_Eq *)
    + (* The type *)
      destruct (X _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA'') as [T [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T ; inversion hh. subst. clear hh th.
      (* The first term *)
      destruct (X0 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hg hu'' hA') as [u' hu'].
      clear hu'' u'' A''.
      (* The other term *)
      destruct (X1 _ hΓ) as [A'' [v'' hv'']].
      destruct (change_type hg hv'' hA') as [v' hv'].
      (* Now we conclude *)
      exists (sSort s), (sEq A' u' v').
      apply trans_Eq ; assumption.

    (* type_Refl *)
    + destruct (X0 _ hΓ) as [A' [u' hu']].
      exists (sEq A' u' u'), (sRefl A' u').
      destruct hu' as [[[? ?] ?] hu'].
      destruct hΓ.
      destruct (istype_type hg hu').
      repeat split.
      * assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * eapply type_Refl ; eassumption.

    (* type_Ind *)
    + exists (sind_type decl), (sInd ind).
      repeat split.
      * now destruct hΓ.
      * apply inrel_refl.
        eapply xcomp_ind_type ; eassumption.
      * constructor.
      * eapply type_Ind ; try eassumption.
        now destruct hΓ.

    (* type_Construct *)
    + exists (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl).
      exists (sConstruct ind i).
      repeat split.
      * now destruct hΓ.
      * apply inrel_refl.
        eapply xcomp_type_of_constructor ; eassumption.
      * constructor.
      * eapply type_Construct ; try eassumption.
        now destruct hΓ.

    (* type_conv *)
    + (* Translating the conversion *)
      destruct (X1 _ hΓ)
        as [S' [S'' [A'' [B'' [p' h']]]]].
      destruct (eqtrans_trans hg h') as [hA'' hB''].
      destruct h' as [[[[[eΓ eS'] eS''] eA] eB] hp'].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA'') as [T [[A' hA'] hh]].
      (* clear hA'' eS' eA A'' S'. *)
      destruct T ; inversion hh. subst. clear hh.
      destruct (choose_type hg th hB'') as [T [[B' hB'] hh]].
      (* clear hB'' eS'' eB B'' S''. *)
      destruct T ; inversion hh. subst. clear hh th.
      (* Translating the term *)
      destruct (X _ hΓ) as [A''' [t'' ht'']].
      destruct (change_type hg ht'' hA') as [t' ht'].
      assert (hpA : ∑ pA, Σ ;;; Γ' |-i pA : sHeq (sSort s) A' S' A'').
      { destruct hA' as [[_ eA'] hA'].
        destruct hA'' as [_ hA''].
        assert (hr : A' ∼ A'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hg hr) ; assumption.
      }
      destruct hpA as [pA hpA].
      assert (hpB : ∑ pB, Σ ;;; Γ' |-i pB : sHeq S'' B'' (sSort s) B').
      { destruct hB' as [[_ eB'] hB'].
        destruct hB'' as [_ hB''].
        assert (hr : B'' ∼ B').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hg hr) ; assumption.
      }
      destruct hpB as [pB hpB].
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq (sSort s) A' (sSort s) B').
      { exists (sHeqTrans pA (sHeqTrans p' pB)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hq as [q hq].
      destruct (sort_heq_ex hg hq) as [e' he'].
      (* Now we conclude *)
      exists B', (sTransport A' B' e' t').
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht' as [[[? ?] ?] ?].
      repeat split ; try assumption.
      * constructor. assumption.
      * eapply type_Transport ; eassumption.

  (** eq_translation **)

    (* eq_reflexivity *)
    + destruct (X _ hΓ) as [A' [u' hu']].
      destruct hu' as [[[? ?] ?] hu'].
      destruct (istype_type hg hu') as [s' hA'].
      exists A', A', u', u', (sHeqRefl A' u').
      repeat split ; try assumption.
      eapply type_HeqRefl ; eassumption.

    (* eq_symmetry *)
    + destruct (X _ hΓ)
        as [A' [A'' [u' [v' [p' h']]]]].
      destruct h' as [[[[[? ?] ?] ?] ?] hp'].
      exists A'', A', v', u', (sHeqSym p').
      repeat split ; try assumption.
      eapply type_HeqSym' ; eassumption.

    (* eq_transitivity *)
    + destruct (X _ hΓ)
        as [A1 [A2 [u1 [v1 [p1 h1']]]]].
      destruct (X0 _ hΓ)
        as [A3 [A4 [v2 [w1 [p2 h2']]]]].
      destruct (eqtrans_trans hg h1') as [hu1 hv1].
      destruct (eqtrans_trans hg h2') as [hv2 hw1].
      destruct h1' as [[[[[? ?] ?] ?] ?] hp1].
      destruct h2' as [[[[[? ?] ?] ?] ?] hp2].
      (* We have a missing link between (v1 : A2) and (v2 : A3) *)
      assert (sim : v1 ∼ v2).
      { eapply trel_trans.
        - eapply trel_sym. eapply inrel_trel. eassumption.
        - apply inrel_trel. assumption.
      }
      destruct hv1 as [_ hv1].
      destruct hv2 as [_ hv2].
      destruct (trel_to_heq hg sim hv1 hv2) as [p3 hp3].
      (* We can conclude *)
      exists A1, A4, u1, w1.
      exists (sHeqTrans p1 (sHeqTrans p3 p2)).
      repeat split ; try assumption.
      eapply type_HeqTrans' ; try assumption.
      * eassumption.
      * eapply type_HeqTrans' ; eassumption.

    (* eq_beta *)
    + (* Translation of the domain *)
      destruct (X _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the codomain *)
      destruct (X0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the in-term *)
      destruct (X1 _ (trans_snoc hΓ hA'))
        as [T' [t'' ht'']].
      destruct (change_type hg ht'' hB') as [t' ht'].
      clear ht'' T' t''.
      (* Translation of the argument *)
      destruct (X2 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hg hu'' hA') as [u' hu'].
      clear hu'' A'' u''.
      (* Now we conclude using reflexivity *)
      exists (B'{0 := u'}), (B'{0 := u'}).
      exists (sApp (sLambda n A' B' t') n A' B' u'), (t'{0 := u'}).
      exists (sHeqRefl (B'{0 := u'}) (t'{0 := u'})).
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht' as [[[? ?] ?] ?].
      destruct hu' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * eapply inrel_subst ; assumption.
      * eapply inrel_subst ; assumption.
      * constructor ; try assumption.
        constructor ; assumption.
      * eapply inrel_subst ; assumption.
      * eapply type_conv.
        -- apply @type_HeqRefl with (s := s2).
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ eapply typing_subst ; eassumption.
        -- apply @type_Heq with (s := s2).
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ eapply type_App. all: try eassumption.
              eapply type_Lambda. all: eassumption.
           ++ eapply typing_subst ; eassumption.
        -- apply cong_Heq.
           all: try (apply eq_reflexivity).
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ apply eq_symmetry. eapply eq_beta ; eassumption.
           ++ eapply typing_subst ; eassumption.

    (* eq_conv *)
    + (* Translating the conversion *)
      destruct (X0 _ hΓ)
        as [S' [S'' [T1'' [T2'' [p' h']]]]].
      destruct (eqtrans_trans hg h') as [hT1'' hT2''].
      destruct h' as [[[[[eΓ eS'] eS''] eT1] eT2] hp'].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hT1'') as [T [[T1' hT1'] hh]].
      destruct T ; inversion hh. subst. clear hh.
      destruct (choose_type hg th hT2'') as [T [[T2' hT2'] hh]].
      destruct T ; inversion hh. subst. clear hh th.
      (* Translation the term conversion *)
      destruct (X _ hΓ)
        as [T1''' [T2''' [t1'' [t2'' [q' hq']]]]].
      destruct (eqtrans_trans hg hq') as [ht1'' ht2''].
      destruct (change_type hg ht1'' hT1') as [t1' ht1'].
      destruct (change_type hg ht2'' hT1') as [t2' ht2'].
      (* clear ht1'' ht2'' hq' T1''' T2''' t1'' t2'' q'. *)
      destruct hq' as [[[[[_ eT1'''] eT2'''] et1''] et2''] hq'].
      (* Building the intermediary paths *)
      assert (hpT1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s) T1' S' T1'').
      { destruct hT1' as [[_ eT1'] hT1'].
        destruct hT1'' as [_ hT1''].
        assert (hr : T1' ∼ T1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hg hr) ; assumption.
      }
      destruct hpT1 as [p1 hp1].
      assert (hp2 : ∑ p2, Σ ;;; Γ' |-i p2 : sHeq S'' T2'' (sSort s) T2').
      { destruct hT2' as [[_ eT2'] hT2'].
        destruct hT2'' as [_ hT2''].
        assert (hr : T2'' ∼ T2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hg hr) ; assumption.
      }
      destruct hp2 as [p2 hp2].
      assert (he : ∑ e, Σ ;;; Γ' |-i e : sHeq (sSort s) T1' (sSort s) T2').
      { exists (sHeqTrans p1 (sHeqTrans p' p2)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct he as [e' he'].
      rename e into eqt.
      destruct (sort_heq_ex hg he') as [e he].
      (* Likewise, we build paths for the terms *)
      assert (hq1 : ∑ q1, Σ ;;; Γ' |-i q1 : sHeq T1' t1' T1''' t1'').
      { destruct ht1' as [[_ et1'] ht1'].
        destruct ht1'' as [_ ht1''].
        assert (hr : t1' ∼ t1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hg hr) ; assumption.
      }
      destruct hq1 as [q1 hq1].
      assert (hq2 : ∑ q2, Σ ;;; Γ' |-i q2 : sHeq T2''' t2'' T1' t2').
      { destruct ht2' as [[_ et2'] ht2'].
        destruct ht2'' as [_ ht2''].
        assert (hr : t2'' ∼ t2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hg hr) ; assumption.
      }
      destruct hq2 as [q2 hq2].
      assert (hqq : ∑ qq, Σ ;;; Γ' |-i qq : sHeq T1' t1' T1' t2').
      { exists (sHeqTrans q1 (sHeqTrans q' q2)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqq as [qq hqq].
      assert (hql : ∑ ql, Σ ;;; Γ' |-i ql : sHeq T2' (sTransport T1' T2' e t1') T1' t1').
      { exists (sHeqSym (sHeqTransport e t1')).
        destruct ht1' as [_ ht1'].
        eapply type_HeqSym' ; try assumption.
        eapply type_HeqTransport' ; eassumption.
      }
      destruct hql as [ql hql].
      assert (hqr : ∑ qr, Σ ;;; Γ' |-i qr : sHeq T1' t2' T2' (sTransport T1' T2' e t2')).
      { exists (sHeqTransport e t2').
        destruct ht2' as [_ ht2'].
        eapply type_HeqTransport' ; eassumption.
      }
      destruct hqr as [qr hqr].
      assert (hqf : ∑ qf, Σ ;;; Γ' |-i qf
                                    : sHeq T2' (sTransport T1' T2' e t1')
                                           T2' (sTransport T1' T2' e t2')).
      { exists (sHeqTrans (sHeqTrans ql qq) qr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - assumption.
      }
      destruct hqf as [qf hqf].
      (* Now we conclude *)
      exists T2', T2', (sTransport T1' T2' e t1'), (sTransport T1' T2' e t2').
      exists qf.
      destruct hT1' as [[[? ?] ?] ?].
      destruct hT2' as [[[? ?] ?] ?].
      destruct ht1' as [[[? ?] ?] ?].
      destruct ht2' as [[[? ?] ?] ?].
      repeat split ; try eassumption.
      * econstructor. assumption.
      * econstructor. assumption.

    (* cong_Prod *)
    + (* The domains *)
      destruct (X _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (X0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, svass n1 A1').
      pose (Γ2 := nil ,, svass n2 A2').
      pose (Γm := [ svass n1 (sPack A1' A2') ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil scontext_decl| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil scontext_decl| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X2 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        eapply (trel_to_heq' hg).
        - destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* We can finally conclude! *)
      exists (sSort (max_sort s1 s2)), (sSort (max_sort s1 s2)).
      exists (sProd n1 A1' B1'), (sProd n2 A2' tB2).
      exists (sCongProd B1' tB2 p1 p5).
      destruct hA1' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct htB2 as [[[? ?] ?] ?].
      repeat split.
      all: try constructor. all: try assumption.
      eapply type_CongProd' ; try assumption.
      cbn in hp5. rewrite <- llift_substProj, <- rlift_substProj in hp5.
      rewrite !llift00, !rlift00 in hp5.
      apply hp5.

    (* cong_Lambda *)
    + (* The domains *)
      destruct (X _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (X0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, svass n1 A1').
      pose (Γ2 := nil ,, svass n2 A2').
      pose (Γm := [ svass n1 (sPack A1' A2') ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil scontext_decl| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil scontext_decl| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X3 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        eapply (trel_to_heq' hg).
        - destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* Cleaning *)
      clear hp4 p4 hp3 p3 hp2 p2.
      clear hB2' B2' hB2'' hpB'' hB1'' hpA'' hA1'' hA2''.
      (* clear i8 i7 i6 i5 i4 S1 S2 B1'' B2'' pB. *)
      (* clear i3 i2 i1 i0 i T1 T2 A1'' A2'' pA. *)
      clear pA pB pi2_5 B1'' pi2_6 B2''.
      rename p1 into pA, p5 into pB, hp1 into hpA, hp5 into hpB.
      rename tB2 into B2', htB2 into hB2'.
      (* We can now focus on the function terms *)
      destruct (X1 _ (trans_snoc hΓ hA1'))
        as [B1'' [B1''' [t1'' [t2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [ht1'' ht2''].
      destruct (change_type hg ht1'' hB1') as [t1' ht1'].
      destruct (change_type hg ht2'' hB1') as [t2' ht2'].
      destruct (X5 _ (trans_snoc hΓ hA2'))
        as [B2'' [t2''' ht2''']].
      destruct (change_type hg ht2''' hB2') as [tt2 htt2].
      assert (hq1 : ∑ q1, Σ ;;; Γ' ,, svass n1 A1' |-i q1 : sHeq B1' t1' B1' t2').
      { destruct h3' as [[[[[? ?] ?] ?] ?] hpt''].
        destruct ht1' as [[_ et1'] ht1'].
        destruct ht1'' as [_ ht1''].
        destruct ht2' as [[_ et2'] ht2'].
        destruct ht2'' as [_ ht2''].
        assert (hr : t1' ∼ t1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq hg hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : t2'' ∼ t2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pt) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - assumption.
      }
      destruct hq1 as [q1 hq1].
      assert (hq2 : ∑ q2,
        Σ ;;; Δ |-i q2 : sHeq (llift0 #|Γm| B1') (llift0 #|Γm| t1')
                             (llift0 #|Γm| B1') (llift0 #|Γm| t2')
      ).
      { exists (llift0 #|Γm| q1).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq B1' t1' B1' t2'))
        end.
        eapply type_llift0 ; try eassumption.
        assumption.
      }
      destruct hq2 as [q2 hq2].
      assert (hq3 : ∑ q3,
        Σ ;;; Δ |-i q3 : sHeq (llift0 #|Γm| B1') (llift0 #|Γm| t2')
                             (rlift0 #|Γm| B2') (rlift0 #|Γm| tt2)
      ).
      { eapply (trel_to_heq' hg).
        - destruct htt2 as [[? ?] ?].
          destruct ht2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        - eassumption.
        - destruct ht2' as [[? ?] ?]. assumption.
        - destruct htt2 as [[? ?] ?]. assumption.
      }
      destruct hq3 as [q3 hq3].
      assert (hq4 : ∑ q4,
        Σ ;;; Δ |-i q4 : sHeq (llift0 #|Γm| B1') (llift0 #|Γm| t1')
                             (rlift0 #|Γm| B2') (rlift0 #|Γm| tt2)
      ).
      { exists (sHeqTrans q2 q3).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hq4 as [qt hqt].
      (* We're almost done.
         However, our translation of (sLambda n2 A2 B2 t2) has to live in
         our translation of (sProd n' A1 B1).
         This is where the path between the two types comes into action.
       *)
      assert (hty : ∑ pty,
        Σ ;;; Γ' |-i pty : sHeq (sSort (max_sort s1 s2)) (sProd n2 A2' B2')
                               (sSort (max_sort s1 s2)) (sProd n1 A1' B1')

      ).
      { exists (sHeqSym (sCongProd B1' B2' pA pB)).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply type_HeqSym' ; try assumption.
        eapply type_CongProd' ; try assumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        rewrite !llift00, !rlift00 in hpB.
        apply hpB.
      }
      destruct hty as [pty hty].
      destruct (sort_heq_ex hg hty) as [eT heT].
      (* We move the lambda now. *)
      pose (tλ :=
              sTransport (sProd n2 A2' B2') (sProd n1 A1' B1')
                         eT (sLambda n2 A2' B2' tt2)
      ).
      (* Now we conclude *)
      exists (sProd n1 A1' B1'), (sProd n1 A1' B1').
      exists (sLambda n1 A1' B1' t1'), tλ.
      exists (sHeqTrans (sCongLambda B1' B2' t1' tt2 pA pB qt)
                   (sHeqTransport eT (sLambda n2 A2' B2' tt2))).
      destruct ht1' as [[[? ?] ?] ?].
      destruct htt2 as [[[? ?] ?] ?].
      destruct hA1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hB2' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * constructor. constructor ; assumption.
      * eapply type_HeqTrans' ; try assumption.
        -- eapply type_CongLambda' ; try eassumption.
           ++ cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
              rewrite !llift00, !rlift00 in hpB.
              apply hpB.
           ++ cbn in hqt. rewrite <- !llift_substProj, <- !rlift_substProj in hqt.
              rewrite !llift00, !rlift00 in hqt.
              apply hqt.
        -- eapply type_HeqTransport' ; try assumption.
           ++ eapply type_Lambda ; eassumption.
           ++ eassumption.

    (* cong_App *)
    + (* The domains *)
      destruct (X _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans hg h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type hg th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (X0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans hg h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type hg th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, svass n1 A1').
      pose (Γ2 := nil ,, svass n2 A2').
      pose (Γm := [ svass n1 (sPack A1' A2') ]).
      assert (hm : ismix Σ Γ' Γ1 Γ2 Γm).
      { revert Γm.
        replace A1' with (llift0 #|@nil scontext_decl| A1')
          by (cbn ; now rewrite llift00).
        replace A2' with (rlift0 #|@nil scontext_decl| A2')
          by (cbn ; now rewrite rlift00).
        intros.
        destruct hA1' as [[? ?] ?].
        destruct hA2' as [[? ?] ?].
        econstructor.
        - constructor.
        - eassumption.
        - assumption.
      }
      pose (Δ := Γ' ,,, Γm).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γm| B1')
                                               (sSort s2)
                                               (llift0 #|Γm| B2')
             ).
      { exists (llift0 #|Γm| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γm| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; try easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (X4 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type hg th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γm| B2')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γm| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γm| (sSort s2)) at 2.
        eapply (trel_to_heq' hg).
        - destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        - eassumption.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γm| B1')
                                               (sSort s2) (rlift0 #|Γm| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* Cleaning *)
      clear hp4 p4 hp3 p3 hp2 p2.
      clear hB2' B2' hB2'' hpB'' hB1'' hpA'' hA1'' hA2''.
      (* clear i8 i7 i6 i5 i4 S1 S2 B1'' B2'' pB. *)
      (* clear i3 i2 i1 i0 i T1 T2 A1'' A2'' pA. *)
      clear pA pB pi2_1 pi2_2 A1'' A2''.
      rename p1 into pA, p5 into pB, hp1 into hpA, hp5 into hpB.
      rename tB2 into B2', htB2 into hB2'.
      (* We can now translate the functions. *)
      destruct (X1 _ hΓ)
        as [P1 [P1' [t1'' [t2'' [pt h3']]]]].
      destruct (eqtrans_trans hg h3') as [ht1'' ht2''].
      destruct (change_type hg ht1'' (trans_Prod hΓ hA1' hB1')) as [t1' ht1'].
      destruct (change_type hg ht2'' (trans_Prod hΓ hA1' hB1')) as [t2' ht2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpt].
      destruct (X6 _ hΓ)
        as [P2 [t2''' ht2''']].
      destruct (change_type hg ht2''' (trans_Prod hΓ hA2' hB2')) as [tt2 htt2].
      clear ht2''' t2''' P2.
      assert (hqt : ∑ qt,
        Σ ;;; Γ' |-i qt : sHeq (sProd n1 A1' B1') t1' (sProd n2 A2' B2') tt2
      ).
      { destruct ht1'' as [[[? ?] ?] ?].
        destruct ht2'' as [[[? ?] ?] ?].
        destruct ht1' as [[[? ?] ?] ?].
        destruct ht2' as [[[? ?] ?] ?].
        destruct htt2 as [[[? ?] ?] ?].
        assert (r1 : t1' ∼ t1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq hg r1 ltac:(eassumption) ltac:(eassumption))
          as [pl hpl].
        assert (r2 : t2'' ∼ tt2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq hg r2 ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans pl (sHeqTrans pt pr)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqt as [qt hqt].
      (* We then translate the arguments. *)
      destruct (X2 _ hΓ)
        as [A1'' [A1''' [u1'' [u2'' [pu h4']]]]].
      destruct (eqtrans_trans hg h4') as [hu1'' hu2''].
      destruct (change_type hg hu1'' hA1') as [u1' hu1'].
      destruct h4' as [[[[[? ?] ?] ?] ?] hpu].
      destruct (X8 _ hΓ) as [A2'' [u2''' hu2''']].
      destruct (change_type hg hu2''' hA2') as [tu2 htu2].
      clear hu2''' u2''' A2''.
      assert (hqu : ∑ qu, Σ ;;; Γ' |-i qu : sHeq A1' u1' A2' tu2).
      { destruct hu1'' as [[[? ?] ?] ?].
        destruct hu2'' as [[[? ?] ?] ?].
        destruct hu1' as [[[? ?] ?] ?].
        destruct htu2 as [[[? ?] ?] ?].
        assert (r1 : u1' ∼ u1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq hg r1 ltac:(eassumption) ltac:(eassumption))
          as [pl hpl].
        assert (r2 : u2'' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq hg r2 ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans pl (sHeqTrans pu pr)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqu as [qu hqu].
      (* We have an equality between Apps now *)
      assert (happ : ∑ qapp,
        Σ ;;; Γ' |-i qapp : sHeq (B1'{0 := u1'}) (sApp t1' n1 A1' B1' u1')
                                (B2'{0 := tu2}) (sApp tt2 n2 A2' B2' tu2)
      ).
      { exists (sCongApp B1' B2' qt pA pB qu).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply type_CongApp' ; try eassumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        rewrite !llift00, !rlift00 in hpB.
        apply hpB.
      }
      destruct happ as [qapp happ].
      (* Finally we translate the right App to put it in the left Prod *)
      rename e into eA.
      pose (e := sHeqTypeEq (sHeqSym qapp)).
      pose (tapp := sTransport (B2' {0 := tu2}) (B1'{0 := u1'}) e (sApp tt2 n2 A2' B2' tu2)).
      (* We conclude *)
      exists (B1'{0 := u1'}), (B1'{0 := u1'}).
      exists (sApp t1' n1 A1' B1' u1'), tapp.
      exists (sHeqTrans qapp (sHeqTransport e (sApp tt2 n2 A2' B2' tu2))).
      destruct ht1' as [[[? ?] ?] ?].
      destruct htt2 as [[[? ?] ?] ?].
      destruct hu1' as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct hA1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hB2' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * eapply inrel_subst ; assumption.
      * eapply inrel_subst ; assumption.
      * constructor ; assumption.
      * constructor. constructor ; assumption.
      * eapply type_HeqTrans' ; try eassumption.
        eapply type_HeqTransport' ; try assumption.
        -- eapply type_App ; eassumption.
        -- eapply type_HeqTypeEq' ; try assumption.
           ++ eapply type_HeqSym' ; eassumption.
           ++ match goal with
              | |- _ ;;; _ |-i _ : ?S =>
                change S with (S {0 := tu2})
              end.
              eapply typing_subst ; eassumption.

    (* cong_Eq *)
    + destruct (X _ hΓ)
        as [T1 [T2 [A1' [A2' [pA h1']]]]].
      destruct (X0 _ hΓ)
        as [A1'' [A1''' [u1' [u2' [pu h2']]]]].
      destruct (X1 _ hΓ)
        as [A1'''' [A1''''' [v1' [v2' [pv h3']]]]].
      destruct (eqtrans_trans hg h1') as [hA1' hA2'].
      destruct (eqtrans_trans hg h2') as [hu1' hu2'].
      destruct (eqtrans_trans hg h3') as [hv1' hv2'].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA].
      destruct h2' as [[[[[? ?] ?] ?] ?] hpu].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpv].
      (* We need to chain translations a lot to use sCongEq *)
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA1') as [T' [[tA1 htA1] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA2') as [T' [[tA2 htA2] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      (* For the types we build the missing hequalities *)
      assert (hp : ∑ p, Σ ;;; Γ' |-i p : sHeq (sSort s) tA1 (sSort s) tA2).
      { destruct hA1' as [_ hA1'].
        destruct htA1 as [[[? ?] ?] htA1].
        assert (sim1 : tA1 ∼ A1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim1 htA1 hA1') as [p1 hp1].
        destruct hA2' as [_ hA2'].
        destruct htA2 as [[[? ?] ?] htA2].
        assert (sim2 : A2' ∼ tA2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim2 hA2' htA2) as [p2 hp2].
        exists (sHeqTrans p1 (sHeqTrans pA p2)).
        eapply type_HeqTrans' ; try eassumption.
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp as [qA hqA].
      (* Now we need to do the same for the terms *)
      destruct (change_type hg hu1' htA1) as [tu1 htu1].
      destruct (change_type hg hu2' htA1) as [tu2 htu2].
      destruct (change_type hg hv1' htA1) as [tv1 htv1].
      destruct (change_type hg hv2' htA1) as [tv2 htv2].
      assert (hqu : ∑ qu, Σ ;;; Γ' |-i qu : sHeq tA1 tu1 tA1 tu2).
      { destruct hu1' as [_ hu1'].
        destruct htu1 as [[[? ?] ?] htu1].
        assert (sim1 : tu1 ∼ u1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim1 htu1 hu1') as [pl hpl].
        destruct hu2' as [_ hu2'].
        destruct htu2 as [[[? ?] ?] htu2].
        assert (sim2 : u2' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim2 hu2' htu2) as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pu) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hqu as [qu hqu].
      assert (hqv : ∑ qv, Σ ;;; Γ' |-i qv : sHeq tA1 tv1 tA1 tv2).
      { destruct hv1' as [_ hv1'].
        destruct htv1 as [[[? ?] ?] htv1].
        assert (sim1 : tv1 ∼ v1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim1 htv1 hv1') as [pl hpl].
        destruct hv2' as [_ hv2'].
        destruct htv2 as [[[? ?] ?] htv2].
        assert (sim2 : v2' ∼ tv2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim2 hv2' htv2) as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pv) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hqv as [qv hqv].
      (* We move terms back into tA2 *)
      destruct (sort_heq_ex hg hqA) as [eA heA].
      pose (ttu2 := sTransport tA1 tA2 eA tu2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tu1 tA2 ttu2).
      { exists (sHeqTrans qu (sHeqTransport eA tu2)).
        destruct htu2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTransport ; eassumption.
      }
      destruct hq as [qu' hqu'].
      pose (ttv2 := sTransport tA1 tA2 eA tv2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tv1 tA2 ttv2).
      { exists (sHeqTrans qv (sHeqTransport eA tv2)).
        destruct htv2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTransport ; eassumption.
      }
      destruct hq as [qv' hqv'].
      exists (sSort s), (sSort s), (sEq tA1 tu1 tv1), (sEq tA2 ttu2 ttv2).
      exists (sCongEq qA qu' qv').
      destruct htu1 as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct htA1 as [[[? ?] ?] ?].
      destruct htA2 as [[[? ?] ?] ?].
      destruct htv1 as [[[? ?] ?] ?].
      destruct htv2 as [[[? ?] ?] ?].
      repeat split ; try eassumption.
      * econstructor ; assumption.
      * econstructor ; try assumption.
        -- econstructor ; eassumption.
        -- econstructor ; eassumption.
      * eapply type_CongEq' ; assumption.

    (* cong_Refl *)
    + destruct (X _ hΓ)
        as [T1 [T2 [A1' [A2' [pA h1']]]]].
      destruct (X0 _ hΓ)
        as [A1'' [A1''' [u1' [u2' [pu h2']]]]].
      destruct (eqtrans_trans hg h1') as [hA1' hA2'].
      destruct (eqtrans_trans hg h2') as [hu1' hu2'].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA].
      destruct h2' as [[[[[? ?] ?] ?] ?] hpu].
      (* The types *)
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA1') as [T' [[tA1 htA1] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type hg th hA2') as [T' [[tA2 htA2] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (hp : ∑ p, Σ ;;; Γ' |-i p : sHeq (sSort s) tA1 (sSort s) tA2).
      { destruct hA1' as [_ hA1'].
        destruct htA1 as [[[? ?] ?] htA1].
        assert (sim1 : tA1 ∼ A1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim1 htA1 hA1') as [p1 hp1].
        destruct hA2' as [_ hA2'].
        destruct htA2 as [[[? ?] ?] htA2].
        assert (sim2 : A2' ∼ tA2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim2 hA2' htA2) as [p2 hp2].
        exists (sHeqTrans p1 (sHeqTrans pA p2)).
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hp as [qA hqA].
      (* The terms *)
      destruct (change_type hg hu1' htA1) as [tu1 htu1].
      destruct (change_type hg hu2' htA1) as [tu2 htu2].
      assert (hqu : ∑ qu, Σ ;;; Γ' |-i qu : sHeq tA1 tu1 tA1 tu2).
      { destruct hu1' as [_ hu1'].
        destruct htu1 as [[[? ?] ?] htu1].
        assert (sim1 : tu1 ∼ u1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim1 htu1 hu1') as [pl hpl].
        destruct hu2' as [_ hu2'].
        destruct htu2 as [[[? ?] ?] htu2].
        assert (sim2 : u2' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hg sim2 hu2' htu2) as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pu) pr).
        eapply type_HeqTrans' ; try assumption.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hqu as [qu hqu].
      (* tu2 isn't in the right place, so we need to chain one last equality. *)
      destruct (sort_heq_ex hg hqA) as [eA heA].
      pose (ttu2 := sTransport tA1 tA2 eA tu2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tu1 tA2 ttu2).
      { exists (sHeqTrans qu (sHeqTransport eA tu2)).
        destruct htu2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply type_HeqTrans' ; try assumption.
        - eassumption.
        - eapply type_HeqTransport ; eassumption.
      }
      destruct hq as [q hq].
      (* We're still not there yet as we need to have two translations of the
         same type. *)
      assert (pE : ∑ pE, Σ ;;; Γ' |-i pE : sHeq (sSort s) (sEq tA2 ttu2 ttu2)
                                               (sSort s) (sEq tA1 tu1 tu1)).
      { exists (sHeqSym (sCongEq qA q q)).
        eapply type_HeqSym' ; try assumption.
        eapply type_CongEq' ; eassumption.
      }
      destruct pE as [pE hpE].
      assert (eE : ∑ eE, Σ ;;; Γ' |-i eE : sEq (sSort s) (sEq tA2 ttu2 ttu2)
                                              (sEq tA1 tu1 tu1)).
      { eapply (sort_heq_ex hg hpE). }
      destruct eE as [eE hE].
      pose (trefl2 := sTransport (sEq tA2 ttu2 ttu2)
                                 (sEq tA1 tu1 tu1)
                                 eE (sRefl tA2 ttu2)
           ).
      exists (sEq tA1 tu1 tu1), (sEq tA1 tu1 tu1).
      exists (sRefl tA1 tu1), trefl2.
      exists (sHeqTrans (sCongRefl qA q) (sHeqTransport eE (sRefl tA2 ttu2))).
      destruct htu1 as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct htA1 as [[[? ?] ?] ?].
      destruct htA2 as [[[? ?] ?] ?].
      repeat split.
      all: try assumption.
      all: try (econstructor ; eassumption).
      * econstructor. econstructor.
        -- assumption.
        -- econstructor. assumption.
      * eapply type_HeqTrans' ; try assumption.
        -- eapply type_CongRefl' ; eassumption.
        -- eapply type_HeqTransport' ; try assumption.
           ++ eapply type_Refl' ; try assumption.
              eapply type_Transport' ; eassumption.
           ++ eassumption.

    (* reflection *)
    + destruct (X _ hΓ) as [T' [e'' he'']].
      assert (th : type_head (head (sEq A u v))) by constructor.
      destruct (choose_type hg th he'') as [T'' [[e' he'] hh]].
      destruct T'' ; try (now inversion hh).
      rename T''1 into A', T''2 into u', T''3 into v'.
      clear hh he'' e'' he'' T' th.
      destruct he' as [[[? ieq] ?] he'].
      destruct (istype_type hg he') as [? heq].
      destruct (inversionEq hg heq) as [s [[[? ?] ?] ?]].
      exists A', A', u', v'.
      exists (sEqToHeq e').
      inversion ieq. subst.
      repeat split ; try eassumption.
      eapply type_EqToHeq' ; assumption.

Defined.

End Translation.
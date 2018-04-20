(* Lifts for packing *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils LiftSubst Typing.
From Translation
Require Import util SAst SInduction SLiftSubst Equality SCommon XTyping
               ITyping ITypingLemmata ITypingAdmissible.

(* In order to do things properly we need to extend the context heterogenously,
   this is done by extending the context with packed triples
   (x : A, y : B, e : heq A x B y).
   We call Γm the mix of Γ1 and Γ2.
   We also need to define correspond lifts.

   If Γ, Γ1, Δ |- t : T then
   Γ, Γm, Δ↑ |- llift #|Γm| #|Δ| t : llift #|Γm| #|Δ| T
   If Γ, Γ2, Δ |- t : T then
   Γ, Γm, Δ↑ |- rlift #|Γm| #|Δ| t : rlift #|Γm| #|Δ| T
 *)

Fixpoint llift γ δ (t:sterm)  : sterm :=
  match t with
  | sRel i =>
    if i <? δ
    then sRel i
    else if i <? δ + γ
         then sProjT1 (sRel i)
         else sRel i
  | sLambda na A B b =>
    sLambda na (llift γ δ A) (llift γ (S δ) B) (llift γ (S δ) b)
  | sApp u A B v =>
    sApp (llift γ δ u) (llift γ δ A) (llift γ (S δ) B) (llift γ δ v)
  | sProd na A B => sProd na (llift γ δ A) (llift γ (S δ) B)
  | sEq A u v => sEq (llift γ δ A) (llift γ δ u) (llift γ δ v)
  | sRefl A u => sRefl (llift γ δ A) (llift γ δ u)
  | sJ A u P w v p =>
    sJ (llift γ δ A)
       (llift γ δ u)
       (llift γ (S (S δ)) P)
       (llift γ δ w)
       (llift γ δ v)
       (llift γ δ p)
  | sTransport A B p t =>
    sTransport (llift γ δ A) (llift γ δ B) (llift γ δ p) (llift γ δ t)
  | sHeq s A a B b =>
    sHeq s (llift γ δ A) (llift γ δ a) (llift γ δ B) (llift γ δ b)
  | sHeqToEq p => sHeqToEq (llift γ δ p)
  | sHeqConstr A B a b p q =>
    sHeqConstr (llift γ δ A) (llift γ δ B)
               (llift γ δ a) (llift γ δ b)
               (llift γ δ p) (llift γ δ q)
  | sHeqRefl A a => sHeqRefl (llift γ δ A) (llift γ δ a)
  | sHeqTrans p q => sHeqTrans (llift γ δ p) (llift γ δ q)
  | sHeqTransport p t => sHeqTransport (llift γ δ p) (llift γ δ t)
  | sCongProd B1 B2 p q =>
    sCongProd (llift γ (S δ) B1) (llift γ (S δ) B2)
              (llift γ δ p) (llift γ (S δ) q)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    sCongLambda (llift γ (S δ) B1) (llift γ (S δ) B2)
                (llift γ (S δ) t1) (llift γ (S δ) t2)
                (llift γ δ pA) (llift γ (S δ) pB) (llift γ (S δ) pt)
  | sCongApp B1 B2 pu pA pB pv =>
    sCongApp (llift γ (S δ) B1) (llift γ (S δ) B2)
             (llift γ δ pu) (llift γ δ pA) (llift γ (S δ) pB) (llift γ δ pv)
  | sCongEq pA pu pv => sCongEq (llift γ δ pA) (llift γ δ pu) (llift γ δ pv)
  | sCongRefl pA pu => sCongRefl (llift γ δ pA) (llift γ δ pu)
  | sEqToHeq p => sEqToHeq (llift γ δ p)
  | sHeqTypeEq A B p => sHeqTypeEq (llift γ δ A) (llift γ δ B) (llift γ δ p)
  | sHeqTermEq A B a b p =>
    sHeqTermEq (llift γ δ A) (llift γ δ B)
               (llift γ δ a) (llift γ δ b) (llift γ δ p)
  | sSort x => sSort x
  | sPack A B => sPack (llift γ δ A) (llift γ δ B)
  | sProjT1 x => sProjT1 (llift γ δ x)
  | sProjT2 x => sProjT2 (llift γ δ x)
  | sProjTe x => sProjTe (llift γ δ x)
  | sInd ind => sInd ind
  | sConstruct ind i => sConstruct ind i
  | sCase indn p c brs =>
    let brs' := List.map (on_snd (llift γ δ)) brs in
    sCase indn (llift γ δ p) (llift γ δ c) brs'
  | sBeta A B f u =>
    sBeta (llift γ δ A) (llift γ (S δ) B)
          (llift γ (S δ) f) (llift γ δ u)
  | sJRefl A u P w =>
    sJRefl (llift γ δ A) (llift γ δ u)
           (llift γ (S (S δ)) P) (llift γ δ w)
  | sTransportRefl A u => sTransportRefl (llift γ δ A) (llift γ δ u)
  end.

Notation llift0 γ t := (llift γ 0 t).

Fixpoint rlift γ δ t : sterm :=
  match t with
  | sRel i =>
    if i <? δ
    then sRel i
    else if i <? δ + γ
         then sProjT2 (sRel i)
         else sRel i
  | sLambda na A B b =>
    sLambda na (rlift γ δ A) (rlift γ (S δ) B) (rlift γ (S δ) b)
  | sApp u A B v =>
    sApp (rlift γ δ u) (rlift γ δ A) (rlift γ (S δ) B) (rlift γ δ v)
  | sProd na A B => sProd na (rlift γ δ A) (rlift γ (S δ) B)
  | sEq A u v => sEq (rlift γ δ A) (rlift γ δ u) (rlift γ δ v)
  | sRefl A u => sRefl (rlift γ δ A) (rlift γ δ u)
  | sJ A u P w v p =>
    sJ (rlift γ δ A)
       (rlift γ δ u)
       (rlift γ (S (S δ)) P)
       (rlift γ δ w)
       (rlift γ δ v)
       (rlift γ δ p)
  | sTransport A B p t =>
    sTransport (rlift γ δ A) (rlift γ δ B) (rlift γ δ p) (rlift γ δ t)
  | sHeq s A a B b =>
    sHeq s (rlift γ δ A) (rlift γ δ a) (rlift γ δ B) (rlift γ δ b)
  | sHeqToEq p => sHeqToEq (rlift γ δ p)
  | sHeqConstr A B a b p q =>
    sHeqConstr (rlift γ δ A) (rlift γ δ B)
               (rlift γ δ a) (rlift γ δ b)
               (rlift γ δ p) (rlift γ δ q)
  | sHeqRefl A a => sHeqRefl (rlift γ δ A) (rlift γ δ a)
  | sHeqTrans p q => sHeqTrans (rlift γ δ p) (rlift γ δ q)
  | sHeqTransport p t => sHeqTransport (rlift γ δ p) (rlift γ δ t)
  | sCongProd B1 B2 p q =>
    sCongProd (rlift γ (S δ) B1) (rlift γ (S δ) B2)
              (rlift γ δ p) (rlift γ (S δ) q)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    sCongLambda (rlift γ (S δ) B1) (rlift γ (S δ) B2)
                (rlift γ (S δ) t1) (rlift γ (S δ) t2)
                (rlift γ δ pA) (rlift γ (S δ) pB) (rlift γ (S δ) pt)
  | sCongApp B1 B2 pu pA pB pv =>
    sCongApp (rlift γ (S δ) B1) (rlift γ (S δ) B2)
             (rlift γ δ pu) (rlift γ δ pA) (rlift γ (S δ) pB) (rlift γ δ pv)
  | sCongEq pA pu pv => sCongEq (rlift γ δ pA) (rlift γ δ pu) (rlift γ δ pv)
  | sCongRefl pA pu => sCongRefl (rlift γ δ pA) (rlift γ δ pu)
  | sEqToHeq p => sEqToHeq (rlift γ δ p)
  | sHeqTypeEq A B p => sHeqTypeEq (rlift γ δ A) (rlift γ δ B) (rlift γ δ p)
  | sHeqTermEq A B a b p =>
    sHeqTermEq (rlift γ δ A) (rlift γ δ B)
               (rlift γ δ a) (rlift γ δ b) (rlift γ δ p)
  | sSort x => sSort x
  | sPack A B => sPack (rlift γ δ A) (rlift γ δ B)
  | sProjT1 x => sProjT1 (rlift γ δ x)
  | sProjT2 x => sProjT2 (rlift γ δ x)
  | sProjTe x => sProjTe (rlift γ δ x)
  | sInd ind => sInd ind
  | sConstruct ind i => sConstruct ind i
  | sCase indn p c brs =>
    let brs' := List.map (on_snd (rlift γ δ)) brs in
    sCase indn (rlift γ δ p) (rlift γ δ c) brs'
  | sBeta A B f u =>
    sBeta (rlift γ δ A) (rlift γ (S δ) B)
          (rlift γ (S δ) f) (rlift γ δ u)
  | sJRefl A u P w =>
    sJRefl (rlift γ δ A) (rlift γ δ u)
           (rlift γ (S (S δ)) P) (rlift γ δ w)
  | sTransportRefl A u => sTransportRefl (rlift γ δ A) (rlift γ δ u)
  end.

Notation rlift0 γ t := (rlift γ 0 t).

Inductive ismix Σ Γ : forall (Γ1 Γ2 Γm : scontext), Type :=
| mixnil : ismix Σ Γ [] [] []
| mixsnoc Γ1 Γ2 Γm s A1 A2 :
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γ1 |-i A1 : sSort s ->
    Σ ;;; Γ ,,, Γ2 |-i A2 : sSort s ->
    ismix Σ Γ
          (Γ1 ,, A1)
          (Γ2 ,, A2)
          (Γm ,, (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
.

Fact mix_length1 :
  forall {Σ Γ Γ1 Γ2 Γm},
    ismix Σ Γ Γ1 Γ2 Γm ->
    #|Γm| = #|Γ1|.
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact mix_length2 :
  forall {Σ Γ Γ1 Γ2 Γm},
    ismix Σ Γ Γ1 Γ2 Γm ->
    #|Γm| = #|Γ2|.
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_mix :
  forall {Σ} {Γ Γ1 Γ2 Γm : scontext},
    ismix Σ Γ Γ1 Γ2 Γm ->
    forall {n isdecl isdecl1 isdecl2},
      safe_nth Γm (exist _ n isdecl) =
      sPack (llift0 (#|Γm| - S n)
                    (safe_nth Γ1 (exist _ n isdecl1)))
            (rlift0 (#|Γm| - S n)
                    (safe_nth Γ2 (exist _ n isdecl2))).
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - cbn. easy.
  - intro n. destruct n ; intros isdecl isdecl1 isdecl2.
    + cbn. replace (#|Γm| - 0) with #|Γm| by omega. reflexivity.
    + cbn. erewrite IHhm. reflexivity.
Defined.

Lemma llift00 :
  forall {t δ}, llift 0 δ t = t.
Proof.
  intro t.
  induction t using sterm_rect_list ; intro δ.
  all: try (cbn ; f_equal ; easy).
  - cbn. case_eq δ.
    + intro h. cbn. f_equal.
    + intros m h. case_eq (n <=? m).
      * intro. reflexivity.
      * intro nlm. cbn.
        replace (m+0)%nat with m by omega.
        rewrite nlm. f_equal.
  - cbn. f_equal ; try easy.
    rewrite <- map_on_snd_id.
    eapply (case_brs_map_spec X).
    intros x h. apply h.
Defined.

Lemma rlift00 :
  forall {t δ}, rlift 0 δ t = t.
Proof.
  intro t.
  induction t using sterm_rect_list ; intro δ.
  all: try (cbn ; f_equal ; easy).
  - cbn. case_eq δ.
    + intro h. cbn. f_equal.
    + intros m h. case_eq (n <=? m).
      * intro. reflexivity.
      * intro nlm. cbn.
        replace (m+0)%nat with m by omega.
        rewrite nlm. f_equal.
  - cbn. f_equal ; try easy.
    rewrite <- map_on_snd_id.
    eapply (case_brs_map_spec X).
    intros x h. apply h.
Defined.

Lemma lift_llift :
  forall {t i j k},
    lift i k (llift j k t) = llift (i+j) k (lift i k t).
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k.
  all: try (cbn ; f_equal ; easy).
  { unfold llift at 1. case_eq (n <? k) ; intro e ; bprop e.
    - unfold lift. case_eq (k <=? n) ; intro e1 ; bprop e1 ; try omega.
      unfold llift. rewrite e. reflexivity.
    - case_eq (n <? k + j) ; intro e1 ; bprop e1.
      + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold llift. case_eq (i + n <? k) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? k + (i+j)) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
      + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold llift. case_eq (i + n <? k) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? k + (i + j)) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. apply h.
  }
Defined.

Lemma lift_llift' :
  forall {t i j k},
    lift i k (llift j k t) = llift j (k+i) (lift i k t).
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k.
  all: try (cbn ; f_equal ;
            try replace (S (S (k + i))) with ((S (S k)) + i)%nat by omega ;
            try replace (S (k + i)) with ((S k) + i)%nat by omega ;
            easy).
  { unfold llift at 1. case_eq (n <? k) ; intro e ; bprop e.
    - unfold lift. case_eq (k <=? n) ; intro e1 ; bprop e1 ; try omega.
      unfold llift. case_eq (n <? k + i) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
    - case_eq (n <? k + j) ; intro e1 ; bprop e1.
      + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold llift.
        case_eq (i + n <? k + i) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? k + i + j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
      + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold llift.
        case_eq (i + n <? k + i) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? k + i + j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. apply h.
  }
Defined.

Lemma lift_llift3 :
  forall {t i j k l},
    l <= k ->
    lift i l (llift j k t) = llift j (i+k) (lift i l t).
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k l h.
  all: try (cbn ; f_equal ;
            try replace (S (S (i + k))) with (i + (S (S k)))%nat by omega ;
            try replace (S (i + k)) with (i + (S k))%nat by omega ;
            easy).
  { unfold llift at 1.
    case_eq (n <? k) ; intro e ; bprop e.
    - cbn. case_eq (l <=? n) ; intro e1 ; bprop e1.
      + unfold llift. case_eq (i + n <? i + k) ; intro e3 ; bprop e3 ; try omega.
        reflexivity.
      + unfold llift. case_eq (n <? i + k) ; intro e3 ; bprop e3 ; try omega.
        reflexivity.
    - case_eq (n <? k + j) ; intro e1 ; bprop e1.
      + cbn. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold llift.
        case_eq (i + n <? i + k) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? i + k + j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
      + cbn. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold llift. case_eq (i+n <? i+k) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i+n <? i+k+j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x hh. apply hh. assumption.
  }
Defined.

Lemma lift_llift4 :
  forall {t i j k l},
    k < i ->
    i <= k + j ->
    lift i l (llift (j - (i - k)) l t) = llift j (k+l) (lift i l t).
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k l h1 h2.
  all: try (cbn ; f_equal ;
            try replace (S (S (k + l))) with (k + (S (S l)))%nat by omega ;
            try replace (S (k + l)) with (k + (S l))%nat by omega ;
            easy).
  { unfold llift at 1.
    case_eq (n <? l) ; intro e ; bprop e ; try omega.
    - unfold lift. case_eq (l <=? n) ; intro e1 ; bprop e1 ; try omega.
      unfold llift. case_eq (n <? k + l) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
    - case_eq (n <? l + (j - (i - k))) ; intro e1 ; bprop e1 ; try omega.
      + unfold lift. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold llift. case_eq (i+n <? k+l) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i+n <? k+l+j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
      + unfold lift. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold llift. case_eq (i+n <? k+l) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i+n <? k+l+j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. apply h ; assumption.
  }
Defined.

Lemma lift_llift5 :
  forall {t i j k l},
    j + k <= i + l ->
    l <= k ->
    llift j k (lift i l t) = lift i l t.
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k l h1 h2.
  all: try (cbn ; f_equal ; easy).
  { unfold lift. case_eq (l <=? n) ; intro e ; bprop e.
    - unfold llift. case_eq (i+n <? k) ; intro e1 ; bprop e1 ; try omega.
      case_eq (i+n <? k+j) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
    - unfold llift. case_eq (n <? k) ; intro e1 ; bprop e1 ; try omega.
      reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. apply h ; assumption.
  }
Defined.

Lemma lift_rlift :
  forall {t i j k},
    lift i k (rlift j k t) = rlift (i+j) k (lift i k t).
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k.
  all: try (cbn ; f_equal ; easy).
  { unfold rlift at 1. case_eq (n <? k) ; intro e ; bprop e.
    - unfold lift. case_eq (k <=? n) ; intro e1 ; bprop e1 ; try omega.
      unfold rlift. rewrite e. reflexivity.
    - case_eq (n <? k + j) ; intro e1 ; bprop e1.
      + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold rlift. case_eq (i + n <? k) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? k + (i+j)) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
      + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold rlift. case_eq (i + n <? k) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? k + (i + j)) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. apply h.
  }
Defined.

Lemma lift_rlift' :
  forall {t i j k},
    lift i k (rlift j k t) = rlift j (k+i) (lift i k t).
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k.
  all: try (cbn ; f_equal ;
            try replace (S (S (k + i))) with ((S (S k)) + i)%nat by omega ;
            try replace (S (k + i)) with ((S k) + i)%nat by omega ;
            easy).
  { unfold rlift at 1. case_eq (n <? k) ; intro e ; bprop e.
    - unfold lift. case_eq (k <=? n) ; intro e1 ; bprop e1 ; try omega.
      unfold rlift. case_eq (n <? k + i) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
    - case_eq (n <? k + j) ; intro e1 ; bprop e1.
      + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold rlift.
        case_eq (i + n <? k + i) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? k + i + j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
      + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold rlift.
        case_eq (i + n <? k + i) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? k + i + j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. apply h.
  }
Defined.

Lemma lift_rlift3 :
  forall {t i j k l},
    l <= k ->
    lift i l (rlift j k t) = rlift j (i+k) (lift i l t).
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k l h.
  all: try (cbn ; f_equal ;
            try replace (S (S (i + k))) with (i + (S (S k)))%nat by omega ;
            try replace (S (i + k)) with (i + (S k))%nat by omega ;
            easy).
  { unfold rlift at 1.
    case_eq (n <? k) ; intro e ; bprop e.
    - cbn. case_eq (l <=? n) ; intro e1 ; bprop e1.
      + unfold rlift. case_eq (i + n <? i + k) ; intro e3 ; bprop e3 ; try omega.
        reflexivity.
      + unfold rlift. case_eq (n <? i + k) ; intro e3 ; bprop e3 ; try omega.
        reflexivity.
    - case_eq (n <? k + j) ; intro e1 ; bprop e1.
      + cbn. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold rlift.
        case_eq (i + n <? i + k) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i + n <? i + k + j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
      + cbn. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold rlift. case_eq (i+n <? i+k) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i+n <? i+k+j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x hh. apply hh. assumption.
  }
Defined.

Lemma lift_rlift4 :
  forall {t i j k l},
    k < i ->
    i <= k + j ->
    lift i l (rlift (j - (i - k)) l t) = rlift j (k+l) (lift i l t).
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k l h1 h2.
  all: try (cbn ; f_equal ;
            try replace (S (S (k + l))) with (k + (S (S l)))%nat by omega ;
            try replace (S (k + l)) with (k + (S l))%nat by omega ;
            easy).
  { unfold rlift at 1.
    case_eq (n <? l) ; intro e ; bprop e ; try omega.
    - unfold lift. case_eq (l <=? n) ; intro e1 ; bprop e1 ; try omega.
      unfold rlift. case_eq (n <? k + l) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
    - case_eq (n <? l + (j - (i - k))) ; intro e1 ; bprop e1 ; try omega.
      + unfold lift. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold rlift. case_eq (i+n <? k+l) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i+n <? k+l+j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
      + unfold lift. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
        unfold rlift. case_eq (i+n <? k+l) ; intro e5 ; bprop e5 ; try omega.
        case_eq (i+n <? k+l+j) ; intro e7 ; bprop e7 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. apply h ; assumption.
  }
Defined.

Lemma lift_rlift5 :
  forall {t i j k l},
    j + k <= i + l ->
    l <= k ->
    rlift j k (lift i l t) = lift i l t.
Proof.
  intro t. induction t using sterm_rect_list ; intros i j k l h1 h2.
  all: try (cbn ; f_equal ; easy).
  { unfold lift. case_eq (l <=? n) ; intro e ; bprop e.
    - unfold rlift. case_eq (i+n <? k) ; intro e1 ; bprop e1 ; try omega.
      case_eq (i+n <? k+j) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
    - unfold rlift. case_eq (n <? k) ; intro e1 ; bprop e1 ; try omega.
      reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. apply h ; assumption.
  }
Defined.

Fixpoint llift_context n (Δ : scontext) : scontext :=
  match Δ with
  | nil => nil
  | A :: Δ => (llift n #|Δ| A) :: (llift_context n Δ)
  end.

Fact llift_context_length :
  forall {n Δ}, #|llift_context n Δ| = #|Δ|.
Proof.
  intros n Δ.
  induction Δ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact llift_context0 :
  forall {Γ}, llift_context 0 Γ = Γ.
Proof.
  intro Γ. induction Γ.
  - reflexivity.
  - cbn. rewrite llift00. rewrite IHΓ. reflexivity.
Defined.

Fixpoint rlift_context n (Δ : scontext) : scontext :=
  match Δ with
  | nil => nil
  | A :: Δ => (rlift n #|Δ| A) :: (rlift_context n Δ)
  end.

Fact rlift_context_length :
  forall {n Δ}, #|rlift_context n Δ| = #|Δ|.
Proof.
  intros n Δ.
  induction Δ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact rlift_context0 :
  forall {Γ}, rlift_context 0 Γ = Γ.
Proof.
  intro Γ. induction Γ.
  - reflexivity.
  - cbn. rewrite rlift00. rewrite IHΓ. reflexivity.
Defined.

(* We introduce an alternate version of ismix that will be implied by ismix but
   will be used as an intermediary for the proof.
 *)
Inductive ismix' Σ Γ : forall (Γ1 Γ2 Γm : scontext), Type :=
| mixnil' : ismix' Σ Γ [] [] []
| mixsnoc' Γ1 Γ2 Γm s A1 A2 :
    ismix' Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm |-i llift0 #|Γm| A1 : sSort s ->
    Σ ;;; Γ ,,, Γm |-i rlift0 #|Γm|A2 : sSort s ->
    ismix' Σ Γ
          (Γ1 ,, A1)
          (Γ2 ,, A2)
          (Γm ,, (sPack (llift0 #|Γm| A1) (rlift0 #|Γm| A2)))
.

Lemma wf_mix {Σ Γ Γ1 Γ2 Γm} (h : wf Σ Γ) :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  wf Σ (Γ ,,, Γm).
Proof.
  intro hm. induction hm.
  - cbn. assumption.
  - cbn. econstructor.
    + assumption.
    + eapply (type_Pack (s := s)) ; assumption.
Defined.

Fact mix'_length1 :
  forall {Σ Γ Γ1 Γ2 Γm},
    ismix' Σ Γ Γ1 Γ2 Γm ->
    #|Γm| = #|Γ1|.
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact mix'_length2 :
  forall {Σ Γ Γ1 Γ2 Γm},
    ismix' Σ Γ Γ1 Γ2 Γm ->
    #|Γm| = #|Γ2|.
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_mix' :
  forall {Σ} {Γ Γ1 Γ2 Γm : scontext},
    ismix' Σ Γ Γ1 Γ2 Γm ->
    forall {n isdecl isdecl1 isdecl2},
      (safe_nth Γm (exist _ n isdecl)) =
      sPack (llift0 (#|Γm| - S n)
                    (safe_nth Γ1 (exist _ n isdecl1)))
            (rlift0 (#|Γm| - S n)
                    (safe_nth Γ2 (exist _ n isdecl2))).
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - cbn. easy.
  - intro n. destruct n ; intros isdecl isdecl1 isdecl2.
    + cbn. replace (#|Γm| - 0) with #|Γm| by omega. reflexivity.
    + cbn. erewrite IHhm. reflexivity.
Defined.

Definition llift_subst :
  forall (u t : sterm) (i j m : nat),
    llift j (i+m) (u {m := t}) = (llift j (S i+m) u) {m := llift j i t}.
Proof.
  induction u using sterm_rect_list ; intros t i j m.
  all: try (cbn ; f_equal;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by omega ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by omega ;
            try replace (S (j + m))%nat with (j + (S m))%nat by omega ;
            try replace (S (S (S (i + m))))%nat with (i + (S (S (S m))))%nat by omega ;
            try replace (S (S (i + m)))%nat with (i + (S (S m)))%nat by omega ;
            try replace (S (i + m))%nat with (i + (S m))%nat by omega;
            try  (rewrite IHu; cbn; repeat f_equal; omega);
            try  (rewrite IHu1; cbn; repeat f_equal; omega);
            try  (rewrite IHu2; cbn; repeat f_equal; omega);
            try  (rewrite IHu3; cbn; repeat f_equal; omega);
            try  (rewrite IHu4; cbn; repeat f_equal; omega);
            try  (rewrite IHu5; cbn; repeat f_equal; omega);
            try  (rewrite IHu6; cbn; repeat f_equal; omega);
            try  (rewrite IHu7; cbn; repeat f_equal; omega);
            try  (rewrite IHu8; cbn; repeat f_equal; omega)).
  { case_eq (m ?= n) ; intro e ; bprop e.
    - subst. case_eq (n <=? i + n) ; intro e1 ; bprop e1 ; try omega.
      cbn. rewrite e. rewrite lift_llift3 by omega.
      f_equal. omega.
    - case_eq (n <=? i + m) ; intro e1 ; bprop e1.
      + unfold llift at 1.
        case_eq (Init.Nat.pred n <? i + m) ; intro e3 ; bprop e3 ; try omega.
        cbn. rewrite e. reflexivity.
      + case_eq (n <=? i+m+j) ; intro e3 ; bprop e3.
        * unfold llift at 1.
          case_eq (Init.Nat.pred n <? i + m) ; intro e5 ; bprop e5 ; try omega.
          case_eq (Init.Nat.pred n <? i+m+j) ; intro e7 ; bprop e7 ; try omega.
          cbn. rewrite e. reflexivity.
        * unfold llift at 1.
          case_eq (Init.Nat.pred n <? i + m) ; intro e5 ; bprop e5 ; try omega.
          case_eq (Init.Nat.pred n <? i+m+j) ; intro e7 ; bprop e7 ; try omega.
          cbn. rewrite e. reflexivity.
    - case_eq (n <=? i+m) ; intro e1 ; bprop e1 ; try omega.
      unfold llift at 1.
      case_eq (n <? i+m) ; intro e3 ; bprop e3 ; try omega.
      cbn. rewrite e. reflexivity.
  }
  { rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. unfold compose. rewrite h. f_equal. f_equal. omega.
  }
Defined.

Definition rlift_subst :
  forall (u t : sterm) (i j m : nat),
    rlift j (i+m) (u {m := t}) = (rlift j (S i+m) u) {m := rlift j i t}.
Proof.
  induction u using sterm_rect_list ; intros t i j m.
  all: try (cbn ; f_equal;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by omega ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by omega ;
            try replace (S (j + m))%nat with (j + (S m))%nat by omega ;
            try replace (S (S (S (i + m))))%nat with (i + (S (S (S m))))%nat by omega ;
            try replace (S (S (i + m)))%nat with (i + (S (S m)))%nat by omega ;
            try replace (S (i + m))%nat with (i + (S m))%nat by omega;
            try  (rewrite IHu; cbn; repeat f_equal; omega);
            try  (rewrite IHu1; cbn; repeat f_equal; omega);
            try  (rewrite IHu2; cbn; repeat f_equal; omega);
            try  (rewrite IHu3; cbn; repeat f_equal; omega);
            try  (rewrite IHu4; cbn; repeat f_equal; omega);
            try  (rewrite IHu5; cbn; repeat f_equal; omega);
            try  (rewrite IHu6; cbn; repeat f_equal; omega);
            try  (rewrite IHu7; cbn; repeat f_equal; omega);
            try  (rewrite IHu8; cbn; repeat f_equal; omega)).
  { case_eq (m ?= n) ; intro e ; bprop e.
    - subst. case_eq (n <=? i + n) ; intro e1 ; bprop e1 ; try omega.
      cbn. rewrite e. rewrite lift_rlift3 by omega.
      f_equal. omega.
    - case_eq (n <=? i + m) ; intro e1 ; bprop e1.
      + unfold rlift at 1.
        case_eq (Init.Nat.pred n <? i + m) ; intro e3 ; bprop e3 ; try omega.
        cbn. rewrite e. reflexivity.
      + case_eq (n <=? i+m+j) ; intro e3 ; bprop e3.
        * unfold rlift at 1.
          case_eq (Init.Nat.pred n <? i + m) ; intro e5 ; bprop e5 ; try omega.
          case_eq (Init.Nat.pred n <? i+m+j) ; intro e7 ; bprop e7 ; try omega.
          cbn. rewrite e. reflexivity.
        * unfold rlift at 1.
          case_eq (Init.Nat.pred n <? i + m) ; intro e5 ; bprop e5 ; try omega.
          case_eq (Init.Nat.pred n <? i+m+j) ; intro e7 ; bprop e7 ; try omega.
          cbn. rewrite e. reflexivity.
    - case_eq (n <=? i+m) ; intro e1 ; bprop e1 ; try omega.
      unfold rlift at 1.
      case_eq (n <? i+m) ; intro e3 ; bprop e3 ; try omega.
      cbn. rewrite e. reflexivity.
  }
  { rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x h. unfold compose. rewrite h. f_equal. f_equal. omega.
  }
Defined.

Fact safe_nth_llift :
  forall {Δ Γm : scontext} {n is1 is2},
    safe_nth (llift_context #|Γm| Δ) (exist _ n is1) =
    llift #|Γm| (#|Δ| - S n) (safe_nth Δ (exist _ n is2)).
Proof.
  intro Δ. induction Δ.
  - cbn. easy.
  - intro Γm. destruct n ; intros is1 is2.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Fact safe_nth_rlift :
  forall {Δ Γm : scontext} {n is1 is2},
    safe_nth (rlift_context #|Γm| Δ) (exist _ n is1) =
    rlift #|Γm| (#|Δ| - S n) (safe_nth Δ (exist _ n is2)).
Proof.
  intro Δ. induction Δ.
  - cbn. easy.
  - intro Γm. destruct n ; intros is1 is2.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

(* Should be somewhere else. *)
Lemma inversion_wf_cat :
  forall {Σ Δ Γ},
    wf Σ (Γ ,,, Δ) ->
    wf Σ Γ.
Proof.
  intros Σ Δ. induction Δ ; intros Γ h.
  - assumption.
  - dependent destruction h.
    apply IHΔ. assumption.
Defined.

Fact nil_eq_cat :
  forall {Δ Γ},
    [] = Γ ,,, Δ ->
    ([] = Γ) * ([] = Δ).
Proof.
  intro Δ ; destruct Δ ; intros Γ e.
  - rewrite cat_nil in e. split ; easy.
  - cbn in e. inversion e.
Defined.

(* llift/rlift and closedness *)

Fact closed_above_llift_id :
  forall t n k l,
    closed_above l t = true ->
    k >= l ->
    llift n k t = t.
Proof.
  intro t. induction t using sterm_rect_list ; intros m k l clo h.
  all: try (cbn ; cbn in clo ; repeat destruct_andb ;
            repeat erewrite_close_above_lift_id ;
            reflexivity).
  - unfold closed in clo. unfold closed_above in clo.
    bprop clo. unfold llift.
    case_eq (n <? k) ; intro e ; bprop e ; try omega.
    reflexivity.
  - cbn. cbn in clo. repeat destruct_andb.
    repeat erewrite_close_above_lift_id.
    f_equal.
    rewrite <- map_on_snd_id.
    eapply (case_brs_forallb_map_spec X H0).
    intros x hh ?. eapply hh ; eassumption.
Defined.

Fact closed_llift :
  forall t n k,
    closed t ->
    llift n k t = t.
Proof.
  intros t n k h.
  unfold closed in h.
  eapply closed_above_llift_id.
  - eassumption.
  - omega.
Defined.

Fact llift_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      forall n k,
        llift n k (sind_type decl) = sind_type decl.
Proof.
  intros Σ hg ind decl univs h n k.
  destruct (typed_ind_type hg h).
  eapply closed_llift.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Fact llift_type_of_constructor :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind i decl univs}
      {isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl},
      forall n k,
        llift n k (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl) =
        stype_of_constructor (fst Σ) (ind, i) univs decl isdecl.
Proof.
  intros Σ hg ind i decl univs isdecl n k.
  destruct (typed_type_of_constructor hg isdecl).
  eapply closed_llift.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Fact closed_above_rlift_id :
  forall t n k l,
    closed_above l t = true ->
    k >= l ->
    rlift n k t = t.
Proof.
  intro t. induction t using sterm_rect_list ; intros m k l clo h.
  all: try (cbn ; cbn in clo ; repeat destruct_andb ;
            repeat erewrite_close_above_lift_id ;
            reflexivity).
  - unfold closed in clo. unfold closed_above in clo.
    bprop clo. unfold rlift.
    case_eq (n <? k) ; intro e ; bprop e ; try omega.
    reflexivity.
  - cbn. cbn in clo. repeat destruct_andb.
    repeat erewrite_close_above_lift_id.
    f_equal.
    rewrite <- map_on_snd_id.
    eapply (case_brs_forallb_map_spec X H0).
    intros x hh ?. eapply hh ; eassumption.
Defined.

Fact closed_rlift :
  forall t n k,
    closed t ->
    rlift n k t = t.
Proof.
  intros t n k h.
  unfold closed in h.
  eapply closed_above_rlift_id.
  - eassumption.
  - omega.
Defined.

Fact rlift_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      forall n k,
        rlift n k (sind_type decl) = sind_type decl.
Proof.
  intros Σ hg ind decl univs h n k.
  destruct (typed_ind_type hg h).
  eapply closed_rlift.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Fact rlift_type_of_constructor :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind i decl univs}
      {isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl},
      forall n k,
        rlift n k (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl) =
        stype_of_constructor (fst Σ) (ind, i) univs decl isdecl.
Proof.
  intros Σ hg ind i decl univs isdecl n k.
  destruct (typed_type_of_constructor hg isdecl).
  eapply closed_rlift.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Lemma nl_llift :
  forall {t u n k},
    nl t = nl u ->
    nl (llift n k t) = nl (llift n k u).
Proof.
  intros t u n k.
  case (nl_dec (nl t) (nl u)).
  - intros e _.
    revert u e n k.
    induction t using sterm_rect_list ;
    intros u e m k ; destruct u ; cbn in e ; try discriminate e.
    all:
      try (cbn ; inversion e ;
           repeat (erewrite_assumption by eassumption) ; reflexivity).
    cbn. inversion e.
    repeat erewrite_assumption by eassumption.
    f_equal. rewrite !map_map_compose, !compose_on_snd.
    clear - X H3. revert brs0 H3.
    induction X.
    + cbn. intros [|? ?] h ; cbn in h ; try discriminate h. reflexivity.
    + cbn. intros [| [n b] brs'] h ; cbn in h ; try discriminate h.
      cbn. f_equal.
      * destruct x as [x xs]. unfold on_snd in h. unfold on_snd.
        inversion h. subst. f_equal. unfold compose. apply p. cbn. assumption.
      * apply IHX. now inversion h.
  - intros h e. exfalso. apply h. apply e.
Defined.

Lemma nl_rlift :
  forall {t u n k},
    nl t = nl u ->
    nl (rlift n k t) = nl (rlift n k u).
Proof.
  intros t u n k.
  case (nl_dec (nl t) (nl u)).
  - intros e _.
    revert u e n k.
    induction t using sterm_rect_list ;
    intros u e m k ; destruct u ; cbn in e ; try discriminate e.
    all:
      try (cbn ; inversion e ;
           repeat (erewrite_assumption by eassumption) ; reflexivity).
    cbn. inversion e.
    repeat erewrite_assumption by eassumption.
    f_equal. rewrite !map_map_compose, !compose_on_snd.
    clear - X H3. revert brs0 H3.
    induction X.
    + cbn. intros [|? ?] h ; cbn in h ; try discriminate h. reflexivity.
    + cbn. intros [| [n b] brs'] h ; cbn in h ; try discriminate h.
      cbn. f_equal.
      * destruct x as [x xs]. unfold on_snd in h. unfold on_snd.
        inversion h. subst. f_equal. unfold compose. apply p. cbn. assumption.
      * apply IHX. now inversion h.
  - intros h e. exfalso. apply h. apply e.
Defined.

Ltac lh h :=
  lazymatch goal with
  | [ type_llift' :
        forall (Σ : sglobal_context) (Γ Γ1 Γ2 Γm Δ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Γ1 ,,, Δ |-i t : A ->
          type_glob Σ ->
          ismix' Σ Γ Γ1 Γ2 Γm ->
          Σ;;; Γ ,,, Γm ,,, llift_context #|Γm| Δ
          |-i llift #|Γm| #|Δ| t : llift #|Γm| #|Δ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Γ1' ,,, ?Δ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_llift' with (Γ := Γ') (Γ1 := Γ1') (Δ := Δ') (A := T') ; [
            exact h
          | eassumption
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ1' ,,, ?Δ'),, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_llift' with (Γ := Γ') (Γ1 := Γ1') (Δ := Δ',, d') (A := T') ; [
            exact h
          | eassumption
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ1' ,,, ?Δ'),, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_llift' with (Γ := Γ') (Γ1 := Γ1') (Δ := (Δ',, d'),, d'') (A := T') ; [
            exact h
          | eassumption
          | eassumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_llift'"
  end.

Ltac rh h :=
  lazymatch goal with
  | [ type_rlift' :
        forall (Σ : sglobal_context) (Γ Γ1 Γ2 Γm Δ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Γ2 ,,, Δ |-i t : A ->
          type_glob Σ ->
          ismix' Σ Γ Γ1 Γ2 Γm ->
          Σ;;; Γ ,,, Γm ,,, rlift_context #|Γm| Δ
          |-i rlift #|Γm| #|Δ| t : rlift #|Γm| #|Δ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Γ2' ,,, ?Δ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_rlift' with (Γ := Γ') (Γ2 := Γ2') (Δ := Δ') (A := T') ; [
            exact h
          | eassumption
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ2' ,,, ?Δ'),, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_rlift' with (Γ := Γ') (Γ2 := Γ2') (Δ := Δ',, d') (A := T') ; [
            exact h
          | eassumption
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ2' ,,, ?Δ'),, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_rlift' with (Γ := Γ') (Γ2 := Γ2') (Δ := (Δ',, d'),, d'') (A := T') ; [
            exact h
          | eassumption
          | eassumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_rlift'"
  end.

Ltac emh :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i llift _ _ ?t : _ => lh h
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i rlift _ _ ?t : _ => rh h
  | _ => fail "Not a case for emh"
  end.

Fixpoint type_llift' {Σ Γ Γ1 Γ2 Γm Δ t A}
  (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t : A) {struct h} :
  type_glob Σ ->
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, llift_context #|Γm| Δ
  |-i llift #|Γm| #|Δ| t : llift #|Γm| #|Δ| A

with type_rlift' {Σ Γ Γ1 Γ2 Γm Δ t A}
  (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t : A) {struct h} :
  type_glob Σ ->
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γm| Δ
  |-i rlift #|Γm| #|Δ| t : rlift #|Γm| #|Δ| A

with wf_llift' {Σ Γ Γ1 Γ2 Γm Δ} (h : wf Σ (Γ ,,, Γ1 ,,, Δ)) {struct h} :
  type_glob Σ ->
  ismix' Σ Γ Γ1 Γ2 Γm ->
  wf Σ (Γ ,,, Γm ,,, llift_context #|Γm| Δ)

with wf_rlift' {Σ Γ Γ1 Γ2 Γm Δ} (h : wf Σ (Γ ,,, Γ2 ,,, Δ)) {struct h} :
  type_glob Σ ->
  ismix' Σ Γ Γ1 Γ2 Γm ->
  wf Σ (Γ ,,, Γm ,,, rlift_context #|Γm| Δ)
.
Proof.
  (* type_llift' *)
  - { dependent destruction h ; intros hg hm.
      - unfold llift at 1.
        case_eq (n <? #|Δ|) ; intro e ; bprop e.
        + erewrite @safe_nth_lt with (isdecl' := e0).
          eapply meta_conv.
          * eapply type_Rel. eapply wf_llift' ; eassumption.
          * erewrite safe_nth_lt. erewrite safe_nth_llift.
            rewrite lift_llift3 by omega.
            f_equal. omega.
        + case_eq (n <? #|Δ| + #|Γm|) ; intro e1 ; bprop e1.
          * erewrite safe_nth_ge'. erewrite safe_nth_lt.
            eapply type_ProjT1' ; try assumption.
            eapply meta_conv.
            -- eapply type_Rel.
               eapply wf_llift' ; eassumption.
            -- erewrite safe_nth_ge'. erewrite safe_nth_lt.
               erewrite safe_nth_mix' by eassumption.
               cbn. f_equal.
               replace (S (n - #|llift_context #|Γm| Δ|))
                 with ((S n) - #|Δ|)
                 by (rewrite llift_context_length ; omega).
               rewrite lift_llift4 by omega. f_equal.
               ++ omega.
               ++ f_equal. eapply safe_nth_cong_irr.
                  rewrite llift_context_length. reflexivity.
          * erewrite safe_nth_ge'. erewrite safe_nth_ge'.
            eapply meta_conv.
            -- eapply type_Rel.
               eapply wf_llift' ; eassumption.
            -- erewrite safe_nth_ge'. erewrite safe_nth_ge'.
               rewrite lift_llift5 by omega.
               f_equal. eapply safe_nth_cong_irr.
               rewrite llift_context_length. rewrite (mix'_length1 hm). omega.
      - cbn. eapply type_Sort. eapply wf_llift' ; eassumption.
      - cbn. eapply type_Prod ; emh.
      - cbn. eapply type_Lambda ; emh.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite llift_subst. cbn.
        replace (#|Δ| + 0)%nat with #|Δ| by omega.
        eapply type_App ; emh.
      - cbn. eapply type_Eq ; emh.
      - cbn. eapply type_Refl ; emh.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite llift_subst.
        replace (S #|Δ| + 0)%nat with (#|Δ| + 1)%nat by omega.
        rewrite llift_subst.
        cbn. replace (#|Δ| + 0)%nat with #|Δ| by omega.
        replace (S (#|Δ| + 1))%nat with (S (S #|Δ|)) by omega.
        eapply type_J ; emh.
        + cbn. unfold ssnoc. cbn. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            rewrite lift_llift3 by omega. reflexivity.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            rewrite lift_llift3 by omega. reflexivity.
        + replace (S (S #|Δ|)) with ((S #|Δ|) + 1)%nat by omega.
          rewrite <- llift_subst.
          change (sRefl (llift #|Γm| #|Δ| A0) (llift #|Γm| #|Δ| u))
            with (llift #|Γm| #|Δ| (sRefl A0 u)).
          replace (#|Δ| + 1)%nat with (S #|Δ| + 0)%nat by omega.
          rewrite <- llift_subst. f_equal. omega.
      - cbn. eapply type_Transport ; emh.
      - cbn. eapply type_Heq ; emh.
      - cbn. eapply type_HeqToEq ; emh.
      - cbn. eapply type_HeqConstr ; emh.
      - cbn. eapply type_HeqRefl ; emh.
      - cbn.
        eapply @type_HeqTrans
          with (B := llift #|Γm| #|Δ| B) (b := llift #|Γm| #|Δ| b) ; emh.
      - cbn. eapply type_HeqTransport ; emh.
      - cbn. eapply type_CongProd ; emh.
        cbn. f_equal.
        + rewrite lift_llift3 by omega.
          replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
          rewrite llift_subst. cbn. reflexivity.
        + rewrite lift_llift3 by omega.
          replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
          rewrite llift_subst. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; emh.
        + cbn. f_equal.
          * rewrite lift_llift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite llift_subst. cbn. reflexivity.
          * rewrite lift_llift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite llift_subst. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite lift_llift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite llift_subst. cbn. reflexivity.
          * rewrite lift_llift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite llift_subst. cbn. reflexivity.
          * rewrite lift_llift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite llift_subst. cbn. reflexivity.
          * rewrite lift_llift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite llift_subst. cbn. reflexivity.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite 2!llift_subst. cbn.
        replace (#|Δ| + 0)%nat with #|Δ| by omega.
        eapply type_CongApp ; emh.
        cbn. f_equal.
        + rewrite lift_llift3 by omega.
          replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
          rewrite llift_subst. cbn. reflexivity.
        + rewrite lift_llift3 by omega.
          replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
          rewrite llift_subst. cbn. reflexivity.
      - cbn. eapply type_CongEq ; emh.
      - cbn. eapply type_CongRefl ; emh.
      - cbn. eapply type_EqToHeq ; emh.
      - cbn. eapply type_HeqTypeEq ; emh.
      - cbn. eapply type_HeqTermEq ; emh.
      - cbn. eapply type_Pack ; emh.
      - cbn. eapply @type_ProjT1 with (A2 := llift #|Γm| #|Δ| A2) ; emh.
      - cbn. eapply @type_ProjT2 with (A1 := llift #|Γm| #|Δ| A1) ; emh.
      - cbn. eapply type_ProjTe ; emh.
      - cbn. erewrite llift_ind_type by eassumption.
        eapply type_Ind.
        + eapply wf_llift' ; eassumption.
        + eassumption.
      - cbn. erewrite llift_type_of_constructor by eassumption.
        eapply type_Construct. eapply wf_llift' ; eassumption.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite !llift_subst. cbn.
        replace (#|Δ| + 0)%nat with #|Δ| by omega.
        eapply type_Beta ; emh.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite llift_subst.
        replace (S #|Δ| + 0)%nat with (#|Δ| + 1)%nat by omega.
        rewrite llift_subst.
        cbn. replace (#|Δ| + 0)%nat with #|Δ| by omega.
        replace (S (#|Δ| + 1))%nat with (S (S #|Δ|)) by omega.
        eapply type_JRefl ; emh.
        + cbn. unfold ssnoc. cbn. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            rewrite lift_llift3 by omega. reflexivity.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            rewrite lift_llift3 by omega. reflexivity.
        + replace (S (S #|Δ|)) with ((S #|Δ|) + 1)%nat by omega.
          rewrite <- llift_subst.
          change (sRefl (llift #|Γm| #|Δ| A0) (llift #|Γm| #|Δ| u))
            with (llift #|Γm| #|Δ| (sRefl A0 u)).
          replace (#|Δ| + 1)%nat with (S #|Δ| + 0)%nat by omega.
          rewrite <- llift_subst. f_equal. omega.
      - cbn. eapply type_TransportRefl ; emh.
    }

  (* type_rlift' *)
  - { dependent destruction h ; intros hg hm.
      - unfold rlift at 1.
        case_eq (n <? #|Δ|) ; intro e ; bprop e.
        + erewrite @safe_nth_lt with (isdecl' := e0).
          eapply meta_conv.
          * eapply type_Rel. eapply wf_rlift' ; eassumption.
          * erewrite safe_nth_lt. erewrite safe_nth_rlift.
            rewrite lift_rlift3 by omega.
            f_equal. omega.
        + case_eq (n <? #|Δ| + #|Γm|) ; intro e1 ; bprop e1.
          * erewrite safe_nth_ge'. erewrite safe_nth_lt.
            eapply type_ProjT2' ; try assumption.
            eapply meta_conv.
            -- eapply type_Rel.
               eapply wf_rlift' ; eassumption.
            -- erewrite safe_nth_ge'. erewrite safe_nth_lt.
               erewrite safe_nth_mix' by eassumption.
               cbn. f_equal.
               replace (S (n - #|rlift_context #|Γm| Δ|))
                 with ((S n) - #|Δ|)
                 by (rewrite rlift_context_length ; omega).
               rewrite lift_rlift4 by omega. f_equal.
               ++ omega.
               ++ f_equal. eapply safe_nth_cong_irr.
                  rewrite rlift_context_length. reflexivity.
          * erewrite safe_nth_ge'. erewrite safe_nth_ge'.
            eapply meta_conv.
            -- eapply type_Rel.
               eapply wf_rlift' ; eassumption.
            -- erewrite safe_nth_ge'. erewrite safe_nth_ge'.
               rewrite lift_rlift5 by omega.
               f_equal. eapply safe_nth_cong_irr.
               rewrite rlift_context_length. rewrite (mix'_length2 hm). omega.
      - cbn. eapply type_Sort. eapply wf_rlift' ; eassumption.
      - cbn. eapply type_Prod ; emh.
      - cbn. eapply type_Lambda ; emh.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite rlift_subst. cbn.
        replace (#|Δ| + 0)%nat with #|Δ| by omega.
        eapply type_App ; emh.
      - cbn. eapply type_Eq ; emh.
      - cbn. eapply type_Refl ; emh.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite rlift_subst.
        replace (S #|Δ| + 0)%nat with (#|Δ| + 1)%nat by omega.
        rewrite rlift_subst.
        cbn. replace (#|Δ| + 0)%nat with #|Δ| by omega.
        replace (S (#|Δ| + 1))%nat with (S (S #|Δ|)) by omega.
        eapply type_J ; emh.
        + cbn. unfold ssnoc. cbn. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            rewrite lift_rlift3 by omega. reflexivity.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            rewrite lift_rlift3 by omega. reflexivity.
        + replace (S (S #|Δ|)) with ((S #|Δ|) + 1)%nat by omega.
          rewrite <- rlift_subst.
          change (sRefl (rlift #|Γm| #|Δ| A0) (rlift #|Γm| #|Δ| u))
            with (rlift #|Γm| #|Δ| (sRefl A0 u)).
          replace (#|Δ| + 1)%nat with (S #|Δ| + 0)%nat by omega.
          rewrite <- rlift_subst. f_equal. omega.
      - cbn. eapply type_Transport ; emh.
      - cbn. eapply type_Heq ; emh.
      - cbn. eapply type_HeqToEq ; emh.
      - cbn. eapply type_HeqConstr ; emh.
      - cbn. eapply type_HeqRefl ; emh.
      - cbn.
        eapply @type_HeqTrans
          with (B := rlift #|Γm| #|Δ| B) (b := rlift #|Γm| #|Δ| b) ; emh.
      - cbn. eapply type_HeqTransport ; emh.
      - cbn. eapply type_CongProd ; emh.
        cbn. f_equal.
        + rewrite lift_rlift3 by omega.
          replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
          rewrite rlift_subst. cbn. reflexivity.
        + rewrite lift_rlift3 by omega.
          replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
          rewrite rlift_subst. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; emh.
        + cbn. f_equal.
          * rewrite lift_rlift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite rlift_subst. cbn. reflexivity.
          * rewrite lift_rlift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite rlift_subst. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite lift_rlift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite rlift_subst. cbn. reflexivity.
          * rewrite lift_rlift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite rlift_subst. cbn. reflexivity.
          * rewrite lift_rlift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite rlift_subst. cbn. reflexivity.
          * rewrite lift_rlift3 by omega.
            replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
            rewrite rlift_subst. cbn. reflexivity.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite 2!rlift_subst. cbn.
        replace (#|Δ| + 0)%nat with #|Δ| by omega.
        eapply type_CongApp ; emh.
        cbn. f_equal.
        + rewrite lift_rlift3 by omega.
          replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
          rewrite rlift_subst. cbn. reflexivity.
        + rewrite lift_rlift3 by omega.
          replace (S #|Δ|) with ((S #|Δ|) + 0)%nat by omega.
          rewrite rlift_subst. cbn. reflexivity.
      - cbn. eapply type_CongEq ; emh.
      - cbn. eapply type_CongRefl ; emh.
      - cbn. eapply type_EqToHeq ; emh.
      - cbn. eapply type_HeqTypeEq ; emh.
      - cbn. eapply type_HeqTermEq ; emh.
      - cbn. eapply type_Pack ; emh.
      - cbn. eapply @type_ProjT1 with (A2 := rlift #|Γm| #|Δ| A2) ; emh.
      - cbn. eapply @type_ProjT2 with (A1 := rlift #|Γm| #|Δ| A1) ; emh.
      - cbn. eapply type_ProjTe ; emh.
      - cbn. erewrite rlift_ind_type by eassumption.
        eapply type_Ind.
        + eapply wf_rlift' ; eassumption.
        + eassumption.
      - cbn. erewrite rlift_type_of_constructor by eassumption.
        eapply type_Construct. eapply wf_rlift' ; eassumption.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite !rlift_subst. cbn.
        replace (#|Δ| + 0)%nat with #|Δ| by omega.
        eapply type_Beta ; emh.
      - cbn. replace #|Δ| with (#|Δ| + 0)%nat by omega.
        rewrite rlift_subst.
        replace (S #|Δ| + 0)%nat with (#|Δ| + 1)%nat by omega.
        rewrite rlift_subst.
        cbn. replace (#|Δ| + 0)%nat with #|Δ| by omega.
        replace (S (#|Δ| + 1))%nat with (S (S #|Δ|)) by omega.
        eapply type_JRefl ; emh.
        + cbn. unfold ssnoc. cbn. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            rewrite lift_rlift3 by omega. reflexivity.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            rewrite lift_rlift3 by omega. reflexivity.
        + replace (S (S #|Δ|)) with ((S #|Δ|) + 1)%nat by omega.
          rewrite <- rlift_subst.
          change (sRefl (rlift #|Γm| #|Δ| A0) (rlift #|Γm| #|Δ| u))
            with (rlift #|Γm| #|Δ| (sRefl A0 u)).
          replace (#|Δ| + 1)%nat with (S #|Δ| + 0)%nat by omega.
          rewrite <- rlift_subst. f_equal. omega.
      - cbn. eapply type_TransportRefl ; emh.
    }

  (* wf_llift' *)
  - { destruct Δ.
      - cbn. rewrite cat_nil in h.
        intros hg hm. eapply wf_mix.
        + eapply inversion_wf_cat. eassumption.
        + eassumption.
      - cbn. intros hg hm. dependent destruction h.
        econstructor.
        + eapply wf_llift' ; eassumption.
        + eapply type_llift' with (A := sSort s0) ; eassumption.
    }

  (* wf_rlift' *)
  - { destruct Δ.
      - cbn. rewrite cat_nil in h.
        intros hg hm. eapply wf_mix.
        + eapply inversion_wf_cat. eassumption.
        + eassumption.
      - cbn. intros hg hm. dependent destruction h.
        econstructor.
        + eapply wf_rlift' ; eassumption.
        + eapply type_rlift' with (A := sSort s0) ; eassumption.
    }

  Unshelve.
  all: pose (mix'_length1 hm) ;
       pose (mix'_length2 hm) ;
       cbn ; try rewrite !length_cat ;
       try rewrite !llift_context_length ;
       try rewrite !rlift_context_length ;
       try rewrite !length_cat in isdecl ;
       try omega.
Defined.

Lemma ismix_ismix' :
  forall {Σ Γ Γ1 Γ2 Γm},
    type_glob Σ ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    ismix' Σ Γ Γ1 Γ2 Γm.
Proof.
  intros Σ Γ Γ1 Γ2 Γm hg h.
  dependent induction h.
  - constructor.
  - econstructor.
    + assumption.
    + eapply @type_llift' with (A := sSort s) (Δ := []) ; eassumption.
    + eapply @type_rlift' with (A := sSort s) (Δ := []) ; eassumption.
Defined.

Corollary type_llift :
  forall {Σ Γ Γ1 Γ2 Γm Δ t A},
    type_glob Σ ->
    Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,,, llift_context #|Γm| Δ
    |-i llift #|Γm| #|Δ| t : llift #|Γm| #|Δ| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ t A hg ht hm.
  eapply type_llift'.
  - eassumption.
  - assumption.
  - eapply ismix_ismix' ; eassumption.
Defined.

Corollary wf_llift :
  forall {Σ Γ Γ1 Γ2 Γm Δ},
    type_glob Σ ->
    wf Σ (Γ ,,, Γ1 ,,, Δ) ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    wf Σ (Γ ,,, Γm ,,, llift_context #|Γm| Δ).
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ hg hw hm.
  eapply wf_llift'.
  - eassumption.
  - assumption.
  - eapply ismix_ismix' ; eassumption.
Defined.

Corollary type_rlift :
  forall {Σ Γ Γ1 Γ2 Γm Δ t A},
    type_glob Σ ->
    Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γm| Δ
    |-i rlift #|Γm| #|Δ| t : rlift #|Γm| #|Δ| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ t A hg ht hm.
  eapply type_rlift'.
  - eassumption.
  - assumption.
  - eapply ismix_ismix' ; eassumption.
Defined.

Corollary wf_rlift :
  forall {Σ Γ Γ1 Γ2 Γm Δ},
    type_glob Σ ->
    wf Σ (Γ ,,, Γ2 ,,, Δ) ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    wf Σ (Γ ,,, Γm ,,, rlift_context #|Γm| Δ).
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ hg hw hm.
  eapply wf_rlift'.
  - eassumption.
  - assumption.
  - eapply ismix_ismix' ; eassumption.
Defined.

(* Lemma to use ismix knowledge about sorting. *)
Lemma ismix_nth_sort :
  forall {Σ Γ Γ1 Γ2 Γm},
    type_glob Σ ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    forall x is1 is2,
      ∑ s,
        (Σ;;; Γ ,,, Γ1
         |-i lift0 (S x) (safe_nth Γ1 (exist _ x is1)) : sSort s) *
        (Σ;;; Γ ,,, Γ2
         |-i lift0 (S x) (safe_nth Γ2 (exist _ x is2)) : sSort s).
Proof.
  intros Σ Γ Γ1 Γ2 Γm hg hm.
  dependent induction hm.
  - intros x is1. cbn in is1. easy.
  - intro x. destruct x ; intros is1 is2.
    + cbn. exists s. split ; eapply @typing_lift01 with (A := sSort s) ; eassumption.
    + cbn. cbn in is1, is2.
      set (is1' := gt_le_S x #|Γ1| (gt_S_le (S x) #|Γ1| is1)).
      set (is2' := gt_le_S x #|Γ2| (gt_S_le (S x) #|Γ2| is2)).
      destruct (IHhm x is1' is2') as [s' [h1 h2]].
      exists s'. split.
      * replace (S (S x)) with (1 + (S x))%nat by omega.
        rewrite <- liftP3 with (k := 0) by omega.
        eapply @typing_lift01 with (A := sSort s') ; eassumption.
      * replace (S (S x)) with (1 + (S x))%nat by omega.
        rewrite <- liftP3 with (k := 0) by omega.
        eapply @typing_lift01 with (A := sSort s') ; eassumption.
Defined.

(* Simpler to use corollaries *)

Corollary type_llift0 :
  forall {Σ Γ Γ1 Γ2 Γm t A},
    type_glob Σ ->
    Σ ;;; Γ ,,, Γ1 |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm |-i llift0 #|Γm| t : llift0 #|Γm| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t A hg ? ?.
  eapply @type_llift with (Δ := nil) ; eassumption.
Defined.

Corollary type_llift1 :
  forall {Σ Γ Γ1 Γ2 Γm t A B},
    type_glob Σ ->
    Σ ;;; (Γ ,,, Γ1) ,, B |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,, (llift0 #|Γm| B)
    |-i llift #|Γm| 1 t : llift #|Γm| 1 A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t A B hg ht hm.
  eapply @type_llift with (Δ := [ B ]).
  - assumption.
  - exact ht.
  - eassumption.
Defined.

Corollary type_rlift0 :
  forall {Σ Γ Γ1 Γ2 Γm t A},
    type_glob Σ ->
    Σ ;;; Γ ,,, Γ2 |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm |-i rlift0 #|Γm| t : rlift0 #|Γm| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t A ? ? ?.
  eapply @type_rlift with (Δ := nil) ; eassumption.
Defined.

Corollary type_rlift1 :
  forall {Σ Γ Γ1 Γ2 Γm t A B},
    type_glob Σ ->
    Σ ;;; (Γ ,,, Γ2) ,, B |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,, (rlift0 #|Γm| B)
    |-i rlift #|Γm| 1 t : rlift #|Γm| 1 A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t A B hg ht hm.
  eapply @type_rlift with (Δ := [ B ]).
  - assumption.
  - exact ht.
  - eassumption.
Defined.

(* More lemmata about exchange.
   They should go above with the others.
 *)

Lemma llift_substProj :
  forall {t γ l},
    (lift 1 (S l) (llift γ (S l) t)) {l := sProjT1 (sRel 0)} = llift (S γ) l t.
Proof.
  intro t. induction t using sterm_rect_list ; intros γ l.
  all: try (cbn ; f_equal ; easy).
  { unfold llift.
    case_eq (n <? S l) ; intro e ; bprop e ; try omega.
    - case_eq (n <? l) ; intro e1 ; bprop e1 ; try omega.
      + unfold lift. case_eq (S l <=? n) ; intro e3 ; bprop e3 ; try omega.
        cbn. case_eq (l ?= n) ; intro e5 ; bprop e5 ; try omega.
        reflexivity.
      + case_eq (n <? l + S γ) ; intro e3 ; bprop e3 ; try omega.
        unfold lift. case_eq (S l <=? n) ; intro e5 ; bprop e5 ; try omega.
        cbn. case_eq (l ?= n) ; intro e7 ; bprop e7 ; try omega.
        f_equal. f_equal. omega.
    - case_eq (n <? l) ; intro e1 ; bprop e1 ; try omega.
      case_eq (n <? S l + γ) ; intro e3 ; bprop e3 ; try omega.
      + case_eq (n <? l + S γ) ; intro e5 ; bprop e5 ; try omega.
        unfold lift. case_eq (S l <=? n) ; intro e7 ; bprop e7 ; try omega.
        cbn. case_eq (l ?= S n) ; intro e9 ; bprop e9 ; try omega.
        reflexivity.
      + case_eq (n <? l + S γ) ; intro e5 ; bprop e5 ; try omega.
        unfold lift. case_eq (S l <=? n) ; intro e7 ; bprop e7 ; try omega.
        cbn. case_eq (l ?= S n) ; intro e9 ; bprop e9 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x hh. apply hh.
  }
Defined.

Lemma rlift_substProj :
  forall {t γ l},
    (lift 1 (S l) (rlift γ (S l) t)) {l := sProjT2 (sRel 0)} = rlift (S γ) l t.
Proof.
  intro t. induction t using sterm_rect_list ; intros γ l.
  all: try (cbn ; f_equal ; easy).
  { unfold rlift.
    case_eq (n <? S l) ; intro e ; bprop e ; try omega.
    - case_eq (n <? l) ; intro e1 ; bprop e1 ; try omega.
      + unfold lift. case_eq (S l <=? n) ; intro e3 ; bprop e3 ; try omega.
        cbn. case_eq (l ?= n) ; intro e5 ; bprop e5 ; try omega.
        reflexivity.
      + case_eq (n <? l + S γ) ; intro e3 ; bprop e3 ; try omega.
        unfold lift. case_eq (S l <=? n) ; intro e5 ; bprop e5 ; try omega.
        cbn. case_eq (l ?= n) ; intro e7 ; bprop e7 ; try omega.
        f_equal. f_equal. omega.
    - case_eq (n <? l) ; intro e1 ; bprop e1 ; try omega.
      case_eq (n <? S l + γ) ; intro e3 ; bprop e3 ; try omega.
      + case_eq (n <? l + S γ) ; intro e5 ; bprop e5 ; try omega.
        unfold lift. case_eq (S l <=? n) ; intro e7 ; bprop e7 ; try omega.
        cbn. case_eq (l ?= S n) ; intro e9 ; bprop e9 ; try omega.
        reflexivity.
      + case_eq (n <? l + S γ) ; intro e5 ; bprop e5 ; try omega.
        unfold lift. case_eq (S l <=? n) ; intro e7 ; bprop e7 ; try omega.
        cbn. case_eq (l ?= S n) ; intro e9 ; bprop e9 ; try omega.
        reflexivity.
  }
  { cbn. f_equal ; try easy.
    rewrite !map_map_compose, !compose_on_snd.
    eapply (case_brs_map_spec X).
    intros x hh. apply hh.
  }
Defined.
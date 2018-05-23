(*! General utilities to build ETT derivations and terms *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import util Quotes SAst SLiftSubst SCommon ITyping
     ITypingInversions ITypingLemmata ITypingAdmissible XTyping
     FundamentalLemma Translation Reduction FinalTranslation FullQuote.

(* The context for Template Coq *)

(* Definition axiom_nat : *)
(*   ∑ (N : Type) (zero : N) (succ : N -> N), *)
(*     forall P, P zero -> (forall n, P n -> P (succ n)) -> forall n, P n. *)
(* Proof. *)
(*   exists nat, 0, S. exact nat_rect. *)
(* Defined. *)

Definition axiom_nat_ty := ltac:(let t := type of axiom_nat in exact t).

(* We define a term that mentions everything that the global context should
   have. *)
Definition glob_term :=
  let _ := @pp_sigT in
  let _ := @epair in
  let _ := @pi1 in
  let _ := @pi2 in
  let _ := @eq in
  let _ := @transport in
  let _ := @K in
  let _ := @funext in
  let _ := @heq in
  let _ := @heq_to_eq in
  let _ := @heq_refl in
  let _ := @heq_sym in
  let _ := @heq_trans in
  let _ := @heq_transport in
  let _ := @Pack in
  let _ := @ProjT1 in
  let _ := @ProjT2 in
  let _ := @ProjTe in
  let _ := @cong_prod in
  let _ := @cong_app in
  let _ := @cong_lambda in
  let _ := @cong_sum in
  let _ := @cong_pair in
  let _ := @cong_pi1 in
  let _ := @cong_pi2 in
  let _ := @cong_eq in
  let _ := @cong_refl in
  let _ := @eq_to_heq in
  let _ := @heq_type_eq in
  (* More for the sake of examples *)
  let _ := @nat in
  let _ := @bool in
  let _ := @vec in
  let _ := @axiom_nat in
  let _ := @axiom_nat_ty in
  let _ := @axiom_bool in
  let _ := @axiom_vec in
  Type.

Quote Recursively Definition glob_prog := @glob_term.
Definition Σ : global_context :=
  (* reconstruct_global_context (fst glob_prog). *)
  pair (Datatypes.fst glob_prog) init_graph.

Arguments Σ : simpl never.

Open Scope string_scope.

Module IT := ITyping.
Module IL := ITypingLemmata.

(* The context for ITT *)

Definition decl := Build_glob_decl.

Fixpoint Sums (L : list (name * sterm)) (T : sterm) :=
  match L with
  | (na,A) :: L => sSum na A (Sums L T)
  | [] => T
  end.

Fixpoint Prods (L : list (name * sterm)) (T : sterm) :=
  match L with
  | (na,A) :: L => sProd na A (Prods L T)
  | [] => T
  end.

Definition Arrow A B := sProd nAnon A (lift0 1 B).
Notation "A ==> B" := (Arrow A B) (at level 20).

(* Definition Σi : sglobal_context := [ *)
(*   decl "nat" (Sums [ *)
(*     (nNamed "nat", sSort 0) ; *)
(*     (nNamed "zero", sRel 0) ; *)
(*     (nNamed "succ", sRel 1 ==> sRel 1) ; *)
(*     (nNamed "ind", Prods [ *)
(*       (nNamed "P", sRel 3 ==> sSort 0) ; *)
(*       (nNamed "Pz", sApp (sRel 0) (sRel 4) (sSort 0) (sRel 3)) ; *)
(*       (nNamed "Ps", *)
(*        sProd (nNamed "n") (sRel 5) *)
(*              ((sApp (sRel 3) (sRel 7) (sSort 0) (sRel 0)) ==> *)
(*               (sApp ? ? ? ?))) *)
(*     ] ?) *)
(*   ] ?) *)
(* ]. *)

(* Some admissible lemmata to do memoisation in a way. *)
Lemma type_Prod' :
  forall {Σ Γ n A B s1 s2},
    Σ ;;; Γ |-i A : sSort s1 ->
    (IT.wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-i B : sSort s2) ->
    Σ ;;; Γ |-i sProd n A B : sSort (max_sort s1 s2).
Proof.
  intros Σ' Γ n A B s1 s2 hA hB.
  eapply IT.type_Prod.
  - assumption.
  - apply hB. econstructor ; try eassumption.
    eapply IL.typing_wf. eassumption.
Defined.

Lemma type_Lambda' :
  forall {Σ Γ n n' A B t s},
    type_glob Σ ->
    Σ ;;; Γ |-i A : sSort s ->
    (IT.wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-i t : B) ->
    Σ ;;; Γ |-i sLambda n A B t : sProd n' A B.
Proof.
  intros Σ Γ n n' A B t s hg hA ht.
  assert (hw : IT.wf Σ (Γ ,, A)).
  { econstructor ; try eassumption.
    eapply IL.typing_wf. eassumption.
  }
  specialize (ht hw). destruct (istype_type hg ht).
  eapply IT.type_Lambda ; eassumption.
Defined.

Lemma type_App' :
  forall {Σ Γ n t A B u},
    type_glob Σ ->
    Σ ;;; Γ |-i t : sProd n A B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sApp t A B u : (B{0 := u})%s.
Proof.
  intros Σ Γ n t A B u hg ht hu.
  destruct (istype_type hg ht).
  destruct (istype_type hg hu).
  ttinv H.
  eapply IT.type_App ; eassumption.
Defined.

Lemma type_Sum' :
  forall {Σ Γ n A B s1 s2},
    Σ ;;; Γ |-i A : sSort s1 ->
    (IT.wf Σ (Γ ,, A) -> Σ ;;; Γ ,, A |-i B : sSort s2) ->
    Σ ;;; Γ |-i sSum n A B : sSort (max_sort s1 s2).
Proof.
  intros Σ' Γ n A B s1 s2 hA hB.
  eapply IT.type_Sum.
  - assumption.
  - apply hB. econstructor ; try eassumption.
    eapply IL.typing_wf. eassumption.
Defined.

Lemma type_Refl' :
  forall {Σ Γ A u},
    type_glob Σ ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u.
Proof.
  intros Σ Γ A u hg h.
  destruct (istype_type hg h).
  eapply IT.type_Refl ; eassumption.
Defined.

(* Maybe move somewhere else *)
Ltac ittintro :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-i ?t : ?T =>
    lazymatch t with
    | sRel ?n => refine (IT.type_Rel _ _ n _ _)
    | sSort _ => eapply IT.type_Sort
    | sProd _ _ _ => eapply type_Prod' ; [| intro ]
    | sLambda _ _ _ _ => eapply type_Lambda' ; [ .. | intro ]
    | sApp _ _ _ _ => eapply type_App'
    | sSum _ _ _ => eapply type_Sum' ; [| intro ]
    | sPair _ _ _ _ => eapply type_Pair'
    | sPi1 _ _ _ => eapply type_Pi1'
    | sPi2 _ _ _ => eapply type_Pi2'
    | sEq _ _ _ => eapply IT.type_Eq
    | sRefl _ _ => eapply type_Refl'
    | _ => fail "No introduction rule for" t
    end
  | _ => fail "Not applicable"
  end.

Ltac ittcheck1 :=
  lazymatch goal with
  | |- ?Σ ;;; ?Γ |-i ?t : ?T =>
    first [
      eapply meta_conv ; [ ittintro | lazy ; try reflexivity ]
    | eapply meta_ctx_conv ; [
        eapply meta_conv ; [ ittintro | lazy ; try reflexivity ]
      | cbn ; try reflexivity
      ]
    ]
  | |- IT.wf ?Σ ?Γ => first [ assumption | econstructor ]
  | |- sSort _ = sSort _ => first [ lazy ; reflexivity | shelve ]
  | |- type_glob _ => first [ assumption | constructor ]
  | _ => fail "Not applicable"
  end.

Ltac ittcheck' := ittcheck1 ; try (lazy ; omega).

Ltac ittcheck := repeat ittcheck'.

(* Getting axiom_nat as an axiom for ITT/ETT *)
Quote Recursively Definition taxiom_nat_ty := axiom_nat_ty.
Definition ttaxiom_nat_ty :=
  let t := Datatypes.snd taxiom_nat_ty in
  match hnf Σ [] t with
  | Checked t => t
  | _ => tRel 0
  end.
Definition rtaxiom_nat_ty :=
  ltac:(let u := eval lazy in ttaxiom_nat_ty in exact u).

  (* Variable axf' : nat -> sort. *)

Definition axf (i : nat) :=
  match i with
  | 4 => 1
  | 15 => 1
  | 69 => 1
  | 70 => 1
  | 71 => 1
  | 3 => 1
  | 2 => 1
  | 72 => 1
  | i => 0
  end.
Definition fq_ax_nat_ty :=
  fullquote (2 ^ 18) Σ [] rtaxiom_nat_ty axf 0.
Definition rfq_ax_nat_ty :=
  ltac:(let u := eval lazy in fq_ax_nat_ty in exact u).
Definition ax_nat_ty :=
  match rfq_ax_nat_ty with
  | Success (t,_) => t
  | _ => sRel 0
  end.
Definition rtax_nat_ty :=
  ltac:(let u := eval lazy in ax_nat_ty in exact u).

Definition Σi : sglobal_context := [
  decl "nat" rtax_nat_ty
].

Fact hΣi : type_glob Σi.
Proof.
  Opaque max. Opaque max_sort.
  repeat (eapply type_glob_cons) ; try apply type_glob_nil.
  - constructor.
  - eexists. lazy. ittcheck.
  - repeat constructor.
    Unshelve. all: exact nAnon.
Defined.

(* Now some useful lemmata *)

Lemma xmeta_conv :
  forall (Σ : sglobal_context) (Γ : scontext) (t A B : sterm),
    Σ;;; Γ |-x t : A ->
    A = B ->
    Σ;;; Γ |-x t : B.
Proof.
  intros Σ Γ t A B h e.
  destruct e. assumption.
Defined.

Definition pn := nNamed "pppp".

Fixpoint multiProd (bl : list sterm) :=
  match bl with
  | [] => sSort (succ_sort 0)
  | [ A ] => A
  | A :: bl => sProd pn A (multiProd bl)
  end.

Fixpoint multiLam (bl : list sterm) (t : sterm) :=
  match bl with
  | [] => sSort 0
  | [ A ] => t
  | A :: bl => sLambda pn A (multiProd bl) (multiLam bl t)
  end.

Inductive wfb : scontext -> list sterm -> Type :=
| wfb_nil Γ : wfb Γ []
| wfb_cons Γ A s bl :
    Σi ;;; Γ |-x A : sSort s ->
    wfb (A :: Γ) bl ->
    wfb Γ (A :: bl).

Derive Signature for wfb.

Lemma type_multiProd :
  forall {bl Γ},
    wf Σi Γ ->
    wfb Γ bl ->
    ∑ s,
      Σi ;;; Γ |-x multiProd bl : sSort s.
Proof.
  intro bl. induction bl ; intros Γ hwf h.
  - cbn. exists (succ_sort (succ_sort 0)). apply type_Sort. assumption.
  - destruct bl.
    + cbn. dependent destruction h.
      eexists. eassumption.
    + change (multiProd (a :: s :: bl))
        with (sProd pn a (multiProd (s :: bl))).
      dependent destruction h.
      dependent destruction h.
      destruct (IHbl (ssnoc Γ0 A)) as [z hz].
      * econstructor.
        -- assumption.
        -- eassumption.
      * econstructor.
        -- eassumption.
        -- assumption.
      * eexists. eapply type_Prod.
        -- eassumption.
        -- exact hz.
Defined.

Inductive wbtm : scontext -> list sterm -> sterm -> Type :=
| wbtm_nil Γ t : wbtm Γ [] t
| wbtm_one Γ A s t :
    Σi ;;; Γ |-x A : sSort s ->
    Σi ;;; Γ |-x t : A ->
    wbtm Γ [ A ] t
| wbtm_cons Γ A B s bl t :
    Σi ;;; Γ |-x A : sSort s ->
    wbtm (A :: Γ) (B :: bl) t ->
    wbtm Γ (A :: B :: bl) t.

Derive Signature for wbtm.

Lemma wbtm_wfb :
  forall {bl Γ t},
    wbtm Γ bl t ->
    wfb Γ bl.
Proof.
  intro bl. induction bl ; intros Γ t h.
  - constructor.
  - destruct bl.
    + dependent destruction h.
      econstructor.
      * eassumption.
      * constructor.
    + dependent destruction h.
      econstructor.
      * eassumption.
      * eapply IHbl. eassumption.
Defined.

Lemma type_multiLam :
  forall {bl Γ t},
    wf Σi Γ ->
    wbtm Γ bl t ->
    Σi ;;; Γ |-x multiLam bl t : multiProd bl.
Proof.
  intro bl. induction bl ; intros Γ t hwf hwb.
  - cbn. apply type_Sort. assumption.
  - destruct bl.
    + cbn. dependent destruction hwb. assumption.
    + change (multiProd (a :: s :: bl))
        with (sProd pn a (multiProd (s :: bl))).
      change (multiLam (a :: s :: bl) t)
        with (sLambda pn a (multiProd (s :: bl)) (multiLam (s :: bl) t)).
      dependent destruction hwb.
      destruct (@type_multiProd (B :: bl0) (ssnoc Γ0 A)) as [z hz].
      * econstructor.
        -- assumption.
        -- eassumption.
      * eapply wbtm_wfb. eassumption.
      * eapply type_Lambda.
        -- eassumption.
        -- eassumption.
        -- eapply IHbl.
           ++ econstructor.
              ** assumption.
              ** eassumption.
           ++ assumption.
Defined.

Lemma type_conv'' :
  forall {Γ t A B s},
    Σi ;;; Γ |-x t : A ->
    Σi ;;; Γ |-x A = B : sSort s ->
    Σi ;;; Γ |-x B : sSort s ->
    Σi ;;; Γ |-x t : B.
Proof.
  intros Γ t A B s H H0 H1.
  eapply type_conv ; eassumption.
Defined.

Fact istrans_nil :
  ctxtrans Σi nil nil.
Proof.
  split.
  - constructor.
  - constructor.
Defined.

Definition type_translation {Γ t A} h {Γ'} hΓ :=
  pi2_ (pi1_ (@complete_translation Σi hΣi)) Γ t A h Γ' hΓ.



(* Getting the usual nat from axiom *)
Lemma ex_type_Nat :
  ∑ sNat,
    forall {Γ},
      IT.wf Σi Γ ->
      Σi ;;; Γ |-i sNat : sSort 0.
Proof.
  eexists. intros Γ hw.
  eapply type_Pi1' ; try apply hΣi.
  eapply IT.type_Ax with (id := "nat") ; try assumption.
  lazy. reflexivity.
Defined.

Definition sNat := pi1 ex_type_Nat.
Lemma type_Nat :
  forall {Γ},
    IT.wf Σi Γ ->
    Σi ;;; Γ |-i sNat : sSort 0.
Proof.
  apply (pi2 ex_type_Nat).
Defined.

Lemma ex_type_Zero :
  ∑ sZero,
    forall {Γ},
      IT.wf Σi Γ ->
      Σi ;;; Γ |-i sZero : sNat.
Proof.
  eexists. intros Γ hw.
  eapply meta_conv.
  - eapply type_Pi2' ; try apply hΣi.
    eapply IT.type_Ax with (id := "nat") ; try assumption.
    lazy. reflexivity.
  - lazy. Fail reflexivity.
Abort.


(* We actually want them in ETT *)
Lemma ex_Nat :
  ∑ sNat,
    forall {Γ},
      wf Σi Γ ->
      Σi ;;; Γ |-x sNat : sSort 0.
Proof.
  eexists. intros Γ hw.
  eapply type_Pi1.
  - eapply type_Ax with (id := "nat") ; try assumption.
    lazy. reflexivity.
  - econstructor. assumption.
  - admit.
Admitted.

Definition xNat := pi1 ex_Nat.
Lemma type_xNat :
  forall {Γ},
    wf Σi Γ ->
    Σi ;;; Γ |-x xNat : sSort 0.
Proof.
  apply (pi2 ex_Nat).
Defined.
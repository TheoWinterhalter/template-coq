(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".
Require Import ssreflect.
From Equations Require Import Equations.
From Coq Require Import String Bool List Utf8 Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping
  PCUICReduction PCUICWeakening PCUICEquality PCUICUnivSubstitution
  PCUICParallelReduction PCUICParallelReductionConfluence PCUICInduction
  PCUICRW PCUICPattern.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Import MonadNotation.

Set Asymmetric Patterns.

Set Default Goal Selector "!".

(** EXAMPLES OF REWRITE RULES

Here are some examples of rewrite rules that are handled by the system.
This also illustrates how modular it is.

*)

Open Scope string_scope.

Existing Instance config.default_checker_flags.

Definition nouniv :=
  Monomorphic_ctx (
    {| LS.this := [] ; LS.is_ok := LevelSet.Raw.empty_ok |},
    {| CS.this := [] ; CS.is_ok := ConstraintSet.Raw.empty_ok |}
  ).

(** Natural numbers *)
Definition natpath := MPfile [ "nat" ].

Definition natdecl :=
  InductiveDecl {|
    ind_finite := Finite ;
    ind_npars  := 0 ;
    ind_params := [] ;
    ind_bodies := [
      {|
        ind_name := "nat" ;
        ind_type := tSort {|
          Universe.t_set := {|
            UnivExprSet.this := [ UnivExpr.npe (NoPropLevel.lSet, false) ] ;
            UnivExprSet.is_ok :=
              UnivExprSet.Raw.singleton_ok
                (UnivExpr.npe (NoPropLevel.lSet, false))
          |} ;
          Universe.t_ne := eq_refl
        |} ;
        ind_kelim := InType ;
        ind_ctors := [
          ("O", tRel 0, 0) ;
          ("S", tProd nAnon (tRel 0) (tRel 1), 1)
        ] ;
        ind_projs := []
      |}
    ] ;
    ind_universes := Monomorphic_ctx (
      {| LS.this := [] ; LS.is_ok := LevelSet.Raw.empty_ok |},
      {| CS.this := [] ; CS.is_ok := ConstraintSet.Raw.empty_ok |}
    ) ;
    ind_variance := None
  |}.

Definition Σnat := [ ((natpath, "nat"), natdecl) ].

Lemma on_nat :
  on_global_decl (PCUICEnvTyping.lift_typing typing) ([], nouniv)
    (natpath, "nat") natdecl.
Proof.
  cbn. constructor.
  - constructor. 2: constructor.
    econstructor.
    + instantiate (2 := []). cbn. reflexivity.
    + cbn. eexists. (* eapply type_Sort. *) admit.
    + cbn. admit.
    + cbn. contradiction.
    + cbn. admit.
  - cbn. constructor.
  - cbn. reflexivity.
  - admit.
Admitted.

Lemma wf_Σnat :
  wf Σnat.
Proof.
  constructor.
  - constructor.
  - constructor.
  - red. cbn. intuition auto.
    + red. intros l h1 h2. inversion h1.
    + red. intros [[? ?] ?] h. inversion h.
    + red. red. eexists. red. red.
      intros [[? ?] ?] h. inversion h.
  - apply on_nat.
  Unshelve. constructor.
  + intro. exact BinNums.xH.
  + intro. auto.
Qed.

Lemma confluenv_Σnat :
  confluenv Σnat.
Proof.
  constructor.
  - constructor.
  - constructor.
Qed.

(** Parallel plus

pplus : nat → nat → nat
-----------------------------------------
n,m : nat ⊢ pplus (S n) m ↦ S (pplus n m)
n,m : nat ⊢ pplus n (S m) ↦ S (pplus n m)
m : nat   ⊢ pplus 0 m     ↦ m
n : nat   ⊢ pplus n 0     ↦ n

To prove the local triangle property we add the following parallel rule:

n,m : nat ⊢ pplus (S n) (S m) ↦ S (S (plus n m))

*)

Definition pplus_path := MPfile [ "pplus" ].

Definition tArrow A B :=
  tProd nAnon A (lift0 1 B).

Definition tNat :=
  tInd {|
    inductive_mind := (natpath, "nat") ;
    inductive_ind := 0
  |} Instance.empty.

Definition t0 :=
  tConstruct {|
    inductive_mind := (natpath, "nat") ;
    inductive_ind := 0
  |} 0 Instance.empty.

Definition cS :=
  tConstruct {|
    inductive_mind := (natpath, "nat") ;
    inductive_ind := 0
  |} 1 Instance.empty.

Definition tS (t : term) :=
  tApp cS t.

Definition pplus_decl :=
  RewriteDecl {|
    symbols := [ tArrow tNat (tArrow tNat tNat) ] ;
    rules := [
      {|
        pat_context := [] ,, vass (nNamed "n") tNat ,, vass (nNamed "m") tNat ;
        head := 0 ;
        elims := [ eApp (tS (tRel 1)) ; eApp (tRel 0) ] ;
        rhs := tS (mkApps (tRel 2) [ tRel 1 ; tRel 0 ])
      |} ;
      {|
        pat_context := [] ,, vass (nNamed "n") tNat ,, vass (nNamed "m") tNat ;
        head := 0 ;
        elims := [ eApp (tRel 1) ; eApp (tS (tRel 0)) ] ;
        rhs := tS (mkApps (tRel 2) [ tRel 1 ; tRel 0 ])
      |} ;
      {|
        pat_context := [] ,, vass (nNamed "m") tNat ;
        head := 0 ;
        elims := [ eApp t0 ; eApp (tRel 0) ] ;
        rhs := tRel 0
      |} ;
      {|
        pat_context := [] ,, vass (nNamed "n") tNat ;
        head := 0 ;
        elims := [ eApp (tRel 0) ; eApp t0 ] ;
        rhs := tRel 0
      |}
    ] ;
    prules := [
      {|
        pat_context := [] ,, vass (nNamed "n") tNat ,, vass (nNamed "m") tNat ;
        head := 0 ;
        elims := [ eApp (tS (tRel 1)) ; eApp (tS (tRel 0)) ] ;
        rhs := tS (tS (mkApps (tRel 2) [ tRel 1 ; tRel 0 ]))
      |}
    ] ;
    rew_universes := nouniv
  |}.

Definition Σpplus := ((pplus_path, "pplus"), pplus_decl) :: Σnat.

Lemma tApp_mkApps :
  ∀ u v,
    tApp u v = mkApps u [ v ].
Proof.
  cbn. reflexivity.
Qed.

Lemma noApp_mkApps :
  ∀ t, t = mkApps t [].
Proof.
  reflexivity.
Qed.

Lemma meta_conv :
  ∀ Σ Γ t A B,
    Σ ;;; Γ |- t : A →
    A = B →
    Σ ;;; Γ |- t : B.
Proof.
  intros Σ Γ t A B h []. exact h.
Qed.

Lemma type_Nat :
  ∀ Σ Γ,
    wf_local Σ Γ →
    lookup_env Σ (natpath, "nat") = Some natdecl →
    Σ ;;; Γ |- tNat :
    tSort (Universe.make' (UnivExpr.npe (NoPropLevel.lSet, false))).
Proof.
  intros Σ Γ hΓ hΣ.
  eapply meta_conv.
  - econstructor.
    + assumption.
    + red. cbn. unfold declared_minductive.
      rewrite hΣ.
      intuition eauto.
    + cbn. reflexivity.
  - cbn. reflexivity.
Qed.

Lemma type_0 :
  ∀ Σ Γ,
    wf_local Σ Γ →
    lookup_env Σ (natpath, "nat") = Some natdecl →
    Σ ;;; Γ |- t0 : tNat.
Proof.
  intros Σ Γ hΓ hΣ.
  eapply meta_conv.
  - econstructor.
    + assumption.
    + red. cbn. unfold declared_inductive. cbn.
      unfold declared_minductive. rewrite hΣ.
      intuition eauto.
    + cbn. reflexivity.
  - cbn. reflexivity.
Qed.

Lemma type_cS :
  ∀ Σ Γ,
    wf_local Σ Γ →
    lookup_env Σ (natpath, "nat") = Some natdecl →
    Σ ;;; Γ |- cS : tArrow tNat tNat.
Proof.
  intros Σ Γ hΓ hΣ.
  eapply meta_conv.
  - econstructor.
    + assumption.
    + red. cbn. unfold declared_inductive. cbn.
      unfold declared_minductive. rewrite hΣ.
      intuition eauto.
    + cbn. reflexivity.
  - cbn. reflexivity.
Qed.

Lemma type_S :
  ∀ Σ Γ n,
    wf_local Σ Γ →
    lookup_env Σ (natpath, "nat") = Some natdecl →
    Σ ;;; Γ |- n : tNat →
    Σ ;;; Γ |- tS n : tNat.
Proof.
  intros Σ Γ n hΓ hΣ h.
  eapply meta_conv.
  - econstructor.
    + eapply type_cS. all: auto.
    + assumption.
  - cbn. reflexivity.
Qed.

Ltac minicheck :=
  lazymatch goal with
  | |- _ ;;; _ |- tNat : _ =>
    first [
      eapply type_Nat ; [
        minicheck
      | reflexivity
      ]
    | eapply meta_conv ; [
        eapply type_Nat ; [
          minicheck
        | reflexivity
        ]
      | cbn ; reflexivity
      ]
    ]
  | |- _ ;;; _ |- tInd _ _ : _ =>
    first [
      eapply type_Nat ; [
        minicheck
      | reflexivity
      ]
    | eapply meta_conv ; [
        eapply type_Nat ; [
          minicheck
        | reflexivity
        ]
      | cbn ; reflexivity
      ]
    ]
  | |- _ ;;; _ |- tRel _ : _ =>
    eapply meta_conv ; [
      cbn ; econstructor ; [
        cbn ; minicheck
      | cbn ; reflexivity
      ]
    | cbn ; reflexivity
    ]
  | |- _ ;;; _ |- t0 : _ =>
    eapply meta_conv ; [
      cbn ; eapply type_0 ; [
        minicheck
      | reflexivity
      ]
    | cbn ; reflexivity
    ]
  | |- _ ;;; _ |- cS : _ =>
    eapply meta_conv ; [
      cbn ; eapply type_cS ; [
        minicheck
      | reflexivity
      ]
    | cbn ; reflexivity
    ]
  | |- _ ;;; _ |- tS _ : _ =>
    eapply meta_conv ; [
      cbn ; eapply type_S ; [
        minicheck
      | reflexivity
      | cbn ; minicheck
      ]
    | cbn ; reflexivity
    ]
  | |- _ ;;; _ |- _ : _ =>
    eapply meta_conv ; [
      cbn ; econstructor ; minicheck
    | cbn ; reflexivity
    ]
  | |- wf_local _ [] =>
    constructor
  | |- wf_local _ _ =>
    econstructor ; [
      minicheck
    | cbn ; try eexists ; minicheck
    ]
  | |- _ =>
    eauto
  end.

Lemma on_pplus :
  on_global_decl (PCUICEnvTyping.lift_typing typing) (Σnat, nouniv)
    (pplus_path, "pplus") pplus_decl.
Proof.
  cbn. red. intuition idtac.
  - cbn. red. minicheck.
  - cbn. constructor. 2: constructor. 3: constructor. 4: constructor. 5: auto.
    + exists tNat. all: cbn. all: auto.
      * minicheck.
      * minicheck.
      * {
        constructor. 2: constructor. 3: constructor.
        - constructor. unfold tS. rewrite tApp_mkApps.
          constructor. constructor. 2: constructor.
          constructor. auto.
        - constructor. constructor. auto.
      }
      * constructor. constructor. constructor.
    + exists tNat. all: cbn. all: auto.
      * minicheck.
      * minicheck.
      * {
        constructor. 2: constructor. 3: constructor.
        - constructor. constructor. auto.
        - constructor. unfold tS. rewrite tApp_mkApps.
          constructor. constructor. 2: constructor.
          constructor. auto.
      }
      * constructor. constructor. constructor.
    + exists tNat. all: cbn. all: auto.
      * minicheck.
      * minicheck.
      * {
        constructor. 2: constructor. 3: constructor.
        - constructor. unfold t0. erewrite noApp_mkApps.
          constructor. constructor.
        - constructor. constructor. auto.
      }
      * constructor. constructor.
    + exists tNat. all: cbn. all: auto.
      * minicheck.
      * minicheck.
      * {
        constructor. 2: constructor. 3: constructor.
        - constructor. constructor. auto.
        - constructor. unfold t0. erewrite noApp_mkApps.
          constructor. constructor.
      }
      * constructor. constructor.
  - cbn. constructor. 2: constructor.
    exists tNat. all: cbn. all: auto.
    + minicheck.
    + minicheck.
    + constructor. 2: constructor. 3: constructor.
      * constructor. unfold tS. rewrite tApp_mkApps.
        constructor. constructor. 2: constructor.
        constructor. auto.
      * constructor. unfold tS. rewrite tApp_mkApps.
        constructor. constructor. 2: constructor.
        constructor. auto.
    + constructor. constructor. constructor.
  - cbn. constructor. 2: constructor.
    red. cbn. red.
    intro ui.
    eapply trans_trans.
    + eapply trans_step. right.
      eexists _, _, PCUICPosition.Empty. split.
      * cbn. eapply red1_rules_rewrite_rule with (n := 0) (s := [ _ ; _ ]).
        1: cbn. 1: reflexivity.
        constructor. constructor. constructor.
      * cbn. rewrite !lift0_id.
        intuition eauto.
    + eapply trans_step. right.
      eexists _, _, (PCUICPosition.coApp _ PCUICPosition.Empty). cbn.
      split.
      * eapply red1_rules_rewrite_rule with (n := 1) (s := [ _ ; _ ]).
        1: cbn. 1: reflexivity.
        constructor. constructor. constructor.
      * cbn. rewrite !lift0_id.
        intuition eauto.
Qed.

Lemma wf_Σpplus :
  wf Σpplus.
Proof.
  constructor.
  - apply wf_Σnat.
  - constructor. 2: constructor.
    discriminate.
  - red. cbn. intuition auto.
    + red. intros l h1 h2. inversion h1.
    + red. intros [[? ?] ?] h. inversion h.
    + red. red. eexists. red. red.
      intros [[? ?] ?] h. inversion h.
  - apply on_pplus.
  Unshelve. constructor.
  + intro. exact BinNums.xH.
  + intro. auto.
Qed.

Lemma confluenv_Σpplus :
  confluenv Σpplus.
Proof.
  constructor.
  - apply confluenv_Σnat.
  - constructor.
    + red. admit.
    + red. admit.
Admitted.
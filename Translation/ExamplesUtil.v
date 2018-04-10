(*! General utilities to build ETT derivations and terms *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import util SAst SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingAdmissible XTyping
                                Translation Reduction FinalTranslation.

Open Scope string_scope.

Module IT := ITyping.

(** We first create a global context for ITT. *)

Definition iNat :=
  {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}.

Definition sNat :=
  sInd iNat.

Definition sZero :=
  sConstruct iNat 0.

Definition sSuc :=
  sConstruct iNat 1.

Definition iVec :=
  {| inductive_mind := "Translation.Quotes.vec"; inductive_ind := 0 |}.

Definition sVec :=
  sInd iVec.

Definition iBool :=
  {| inductive_mind := "Coq.Init.Datatypes.bool"; inductive_ind := 0 |}.

Definition sBool :=
  sInd iBool.

Definition vec_cod :=
  sProd nAnon sNat (sSort 0).

Definition vec_type :=
  sProd (nNamed "A") (sSort 0) vec_cod.

Ltac unsafe_tdecl :=
  repeat econstructor;
  try (simpl; omega); try trivial.

(* Instead of doing econstructor, we're doing something slightly smarter. *)
Ltac econstr :=
  match goal with
  | |- _ ;;; _ |-i sApp _ _ _ _ : _ =>
    refine (IT.type_App _ _ _ _ _ _ _ _ _ _ _ _ _)
  | |- _ ;;; _ |-i sRel _ : _ =>
    refine (IT.type_Rel _ _ _ _ _)
  | _ => econstructor
  end.

Ltac tdecl :=
  match goal with
  | |- sdeclared_inductive _ _ _ _ => unsafe_tdecl
  | |- sdeclared_constructor _ _ _ _ => unsafe_tdecl
  end.

Ltac iind tac :=
  eapply meta_conv ; [
    eapply IT.type_Ind ; [
      tac
    | tdecl
    ]
  | cbn ; reflexivity
  ].

Ltac iconstruct :=
  eapply meta_conv ; [
    unshelve (eapply IT.type_Construct) ; [
      shelve
    | shelve
    | tdecl
    | idtac
    ]
  | cbn ; reflexivity
  ].

Ltac lom := cbn ; omega.

Ltac reo :=
  unshelve (repeat econstr) ; lom.

Ltac rind := iind reo.

Ltac idind := iind idtac.

Ltac magic :=
  (* unshelve (repeat (try assumption ; try rind ; try idind ; try tdecl ; try econstr)) ; try tdecl ; try lom. *)
  unshelve (repeat (try assumption ; try iconstruct ; try idind ; try tdecl ; try econstr)) ; try tdecl ; try lom.

Definition lΣi := [
  SInductiveDecl "Translation.Quotes.vec" {|
    sind_npars := 1;
    sind_bodies := [
      {| sind_name := "vec";
         sind_type := vec_type ;
         sind_kelim := [InProp; InSet; InType];
         sind_ctors := [
           ("vnil",
            sProd (nNamed "A")
                  (sSort 0)
                  (sApp (sApp (sRel 1)
                              (sSort 0) vec_cod
                              (sRel 0))
                        sNat (sSort 0)
                        sZero),
            0) ;
           ("vcons",
            sProd (nNamed "A") (sSort 0)
                  (sProd nAnon (sRel 0)
                         (sProd (nNamed "n") sNat
                                (sProd nAnon
                                       (sApp (sApp (sRel 3)
                                                   (sSort 0)
                                                   vec_cod
                                                   (sRel 2))
                                             sNat (sSort 0)
                                             (sRel 0))
                                       (sApp (sApp (sRel 4)
                                                   (sSort 0)
                                                   vec_cod
                                                   (sRel 3))
                                             sNat (sSort 0)
                                             (sApp sSuc
                                                   sNat sNat
                                                   (sRel 1)))))),
            3)
         ] ;
         sind_projs := [] |}
    ];
    sind_universes :=
      Monomorphic_ctx (pair [] {|
        Constraint.this := [] ;
        Constraint.is_ok := Constraint.Raw.empty_ok
      |})
  |} ;
  SInductiveDecl "Coq.Init.Datatypes.nat" {|
    sind_npars := 0;
    sind_bodies := [
      {| sind_name := "nat";
         sind_type := sSort 0 ;
         sind_kelim := [InProp; InSet; InType];
         sind_ctors := [
           ("O", sRel 0, 0) ;
           ("S", sProd nAnon (sRel 0) (sRel 1), 1)
         ] ;
         sind_projs := [] |}
    ];
    sind_universes :=
      Monomorphic_ctx (pair [] {|
        Constraint.this := [] ;
        Constraint.is_ok := Constraint.Raw.empty_ok
      |})
  |} ;
  SInductiveDecl "Coq.Init.Datatypes.bool" {|
    sind_npars := 0;
    sind_bodies := [
      {| sind_name := "bool";
         sind_type := sSort 0 ;
         sind_kelim := [InProp; InSet; InType];
         sind_ctors := [
           ("true", sRel 0, 0) ;
           ("false", sRel 0, 0)
         ] ;
         sind_projs := [] |}
    ];
    sind_universes :=
      Monomorphic_ctx (pair [] {|
        Constraint.this := [] ;
        Constraint.is_ok := Constraint.Raw.empty_ok
      |})
  |}
].

Ltac tenv :=
  unfold type_glob ; cbn ;
  repeat eapply globenv_decl ; [ eapply globenv_nil | .. ] ;
  repeat (cbn ; try eapply fresh_global_cons ;
          try eapply fresh_global_nil ; try discriminate).

Ltac xcomp :=
  match goal with
  | |- Xcomp _ => repeat econstructor
  end.

Ltac tind :=
  cbn ; constructor ; [
    idtac
  | repeat constructor
  | cbn ; repeat eapply type_cnstrs_cons ; [ .. | eapply type_cnstrs_nil ]
    ; try xcomp
  | cbn ; constructor
  | cbn ; constructor
  ].

Definition Σi := (lΣi, init_graph).

Fact hΣi : type_glob Σi.
(* Proof. *)
  tenv.
  (* bool *)
  - tind.
    + exists 1. repeat econstr.
    + exists 0. repeat econstr.
    + exists 0. repeat econstr.
  (* nat *)
  - tind.
    + exists 1. constructor. constructor.
    + exists 0. magic.
    + exists (max 0 0). magic.
  (* vec *)
  - tind.
    + exists (max_sort 1 (max 0 1)). magic.
    + exists (max_sort 1 0).
      econstr.
      * magic.
      * econstr.
        -- magic.
        -- magic.
        -- magic.
        -- econstr.
           ++ magic.
           ++ magic.
           ++ magic.
    + exists (max 1 (max 0 (max 0 (max 0 0)))).
      match goal with
      | |- ?Σ' ;;; _ |-i _ : _ => set (Σ := Σ')
      end.
      set (Γ1 := [vec_type]).
      set (Γ2 := Γ1,,(sSort 0)).
      set (Γ3 := Γ2,, (sRel 0)).
      set (Γ4 := Γ3,, sNat).
      set (Γ5 := Γ4,, sNat).
      set (Γ5' := Γ4,, (sSort 0)).
      set (Γ6' := Γ5',, sNat).
      set (Γ5'' := Γ4,,
                     (sApp
                          (sApp (sRel 3)
                                (sSort 0)
                                vec_cod (sRel 2))
                          sNat (sSort 0) (sRel 0))).
      assert (IT.wf Σ Γ1) by magic.
      assert (IT.wf Σ Γ2) by magic.
      assert (IT.wf Σ Γ3) by magic.
      assert (IT.wf Σ Γ4) by magic.
      assert (IT.wf Σ Γ5) by magic.
      assert (IT.wf Σ Γ5') by magic.
      assert (IT.wf Σ Γ6') by magic.
      assert (IT.wf Σ Γ5'') by magic.
      magic.
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
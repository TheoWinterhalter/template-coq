From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SInduction SLiftSubst SCommon Conversion
               ITyping ITypingInversions.

(* Lemmata about typing *)

Open Scope type_scope.
Open Scope i_scope.

(* Typing up to equality *)
Lemma meta_ctx_conv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-i t : A ->
    Γ = Δ ->
    Σ ;;; Δ |-i t : A.
Proof.
  intros Σ Γ Δ t A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_conv :
  forall {Σ Γ t A B},
    Σ ;;; Γ |-i t : A ->
    A = B ->
    Σ ;;; Γ |-i t : B.
Proof.
  intros Σ Γ t A B h e.
  rewrite <- e. exact h.
Defined.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

Lemma type_Prods :
  forall {Σ Γ Δ T},
    istype_nctx Σ Γ Δ T ->
    isType Σ Γ (Prods Δ T).
Proof.
  intros Σ Γ Δ T h. induction h.
  - cbn. eexists. eassumption.
  - cbn. destruct IHh as [s' ih].
    eexists. eapply type_Prod ; eassumption.
Defined.

Lemma istype_nctx_wf :
  forall {Σ Γ L T},
    istype_nctx Σ Γ L T ->
    wf Σ Γ.
Proof.
  intros Σ Γ L T h.
  induction h.
  - eapply typing_wf. eassumption.
  - dependent destruction IHh.
    assumption.
Defined.

(* TODO MOVE *)
Fact nlctx_cons :
  forall {nx A L},
    nlctx ((nx, A) :: L) = [ A ] ,,, nlctx L.
Proof.
  intros nx A L.
  unfold nlctx.
  rewrite rev_map_cons. unfold sapp_context, ssnoc.
  simpl. reflexivity.
Defined.

(* TODO MOVE *)
Fact cat_cons :
  forall {Γ A Δ},
    Γ ,,, ([ A ] ,,, Δ) = Γ ,, A ,,, Δ.
Proof.
  intros Γ A Δ.
  unfold ssnoc, sapp_context.
  rewrite <- app_assoc. reflexivity.
Defined.

Lemma istype_nctx_spec :
  forall {Σ Γ L T},
    istype_nctx Σ Γ L T <-> isType Σ (Γ ,,, nlctx L) T.
Proof.
  intros Σ Γ L T. split.
  - intro h. induction h.
    + cbn. eexists. eassumption.
    + rewrite nlctx_cons, cat_cons. assumption.
  - intro h. revert Γ T h.
    induction L as [| [nx A] L ih] ; intros Γ T h.
    + cbn in h. destruct h.
      econstructor. eassumption.
    + assert (hh : istype_nctx Σ (Γ,, A) L T).
      { eapply ih. rewrite nlctx_cons, cat_cons in h.
        assumption.
      }
      pose proof (istype_nctx_wf hh) as hw.
      dependent destruction hw.
      econstructor ; eassumption.
Defined.

(* Lemma type_Lams : *)
(*   forall {Σ Γ Δ t T}, *)
(*     Σ ;;; Γ,,, nlctx Δ |-i t : T -> *)
(*     isType Σ (Γ,,, nlctx Δ) T -> *)
(*     Σ ;;; Γ |-i Lams Δ T t : Prods Δ T. *)
(* Proof. *)
(*   intros Σ Γ Δ t T h1 h2. revert Γ t T h1 h2. *)
(*   induction Δ as [| [nx A] Δ ih] ; intros Γ t T h1 h2. *)
(*   - cbn in *. assumption. *)
(*   - simpl in *. eapply ih. *)
(*     + pose proof (typing_wf h1) as hw. *)
(*       dependent destruction hw. *)
(*       destruct h2 as [s' h2]. *)
(*       eapply type_Lambda ; eassumption. *)
(*     + pose proof (typing_wf h1) as hw. *)
(*       dependent destruction hw. *)
(*       destruct h2 as [s' h2]. *)
(*       eexists. econstructor ; eassumption. *)
(* Defined. *)

Fact type_ctx_closed_above :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    closed_above #|Γ| t = true.
Proof.
  intros Σ Γ t T h.
  dependent induction h.
  all: try (cbn in * ; repeat (erewrite_assumption by omega) ; reflexivity).
  unfold closed_above. case_eq (n <? #|Γ|) ; intro e ; bprop e ; try omega.
  reflexivity.
Defined.

Fact type_ctxempty_closed :
  forall {Σ t T},
    Σ ;;; [] |-i t : T ->
    closed t.
Proof.
  intros Σ t T h.
  unfold closed. eapply @type_ctx_closed_above with (Γ := []). eassumption.
Defined.

Fact isArity_ind_type' :
  forall {Σ : sglobal_context} {decl'},
    type_inductive Σ decl'.(sind_params) (sind_bodies decl') ->
    forall {n decl},
      nth_error (sind_bodies decl') n = Some decl ->
      isArity Σ decl'.(sind_params) decl.(sind_indices)
              decl.(sind_sort) (sind_type decl).
Proof.
  intros Σ decl' [hx hind].
  induction hind.
  - intros n decl h.
    destruct n ; cbn in h ; inversion h.
  - intros n decl h.
    destruct n.
    + cbn in h. inversion h as [ e ]. subst. clear h.
      cbn. assumption.
    + cbn in h. eapply IHhind.
      eassumption.
Defined.

Fact ident_neq_fresh :
  forall {Σ ind decl' d},
    slookup_env Σ (inductive_mind ind) =
    Some (SInductiveDecl (inductive_mind ind) decl') ->
    fresh_global (sglobal_decl_ident d) Σ ->
    ident_eq (inductive_mind ind) (sglobal_decl_ident d) = false.
Proof.
  intro Σ. induction Σ.
  - intros ind decl' d h1 h2.
    cbn in h1. inversion h1.
  - intros ind decl' d h1 h2.
    cbn in h1.
    set (id1 := inductive_mind ind) in *.
    set (id2 := sglobal_decl_ident d) in *.
    set (id3 := sglobal_decl_ident a) in *.
    dependent destruction h2.
    case_eq (ident_eq id1 id3) ;
      intro e ; rewrite e in h1.
    + inversion h1 as [ h1' ]. subst. clear h1 e.
      cbn in *.
      destruct (ident_eq_spec id1 id2) ; easy.
    + eapply IHΣ ; eassumption.
Defined.

Lemma stype_of_constructor_eq :
  forall {Σ id' decl' ind i univs decl}
    {isdecl : sdeclared_constructor ((SInductiveDecl id' decl') :: Σ) (ind, i) univs decl},
    ident_eq (inductive_mind ind) id' = true ->
    let '(id, trm, args, _) := decl in
    stype_of_constructor ((SInductiveDecl id' decl') :: Σ) (ind, i) univs decl isdecl =
    substl (sinds (inductive_mind ind) decl'.(sind_bodies)) trm.
Proof.
  intros Σ id' decl' ind i univs decl isdecl h.
  funelim (stype_of_constructor (SInductiveDecl id' decl' :: Σ) (ind, i) univs decl isdecl)
  ; try bang.
  cbn. cbn in H. rewrite h in H. inversion H. subst. reflexivity.
Defined.

Lemma stype_of_constructor_cons :
  forall {Σ d ind i univs decl}
    {isdecl : sdeclared_constructor Σ (ind, i) univs decl}
    {isdecl' : sdeclared_constructor (d :: Σ) (ind, i) univs decl},
    fresh_global (sglobal_decl_ident d) Σ ->
    stype_of_constructor (d :: Σ) (ind, i) univs decl isdecl' =
    stype_of_constructor Σ (ind, i) univs decl isdecl.
Proof.
  intros Σ d ind i univs decl isdecl isdecl' fresh.
  assert (eq : slookup_env (d :: Σ) (inductive_mind (fst (ind, i))) = slookup_env Σ (inductive_mind ind)).
  { cbn.
    destruct isdecl as [decl' [[d' [[h1 h2] h3]] h4]].
    pose proof (ident_neq_fresh h1 fresh) as neq.
    rewrite neq. reflexivity.
  }
  funelim (stype_of_constructor (d :: Σ) (ind, i) univs decl isdecl')
  ; try bang.
  funelim (stype_of_constructor Σ0 (ind, i) univs decl isdecl) ; try bang.
  rewrite <- eq in H. inversion H. subst. reflexivity.
Defined.

Fixpoint weak_glob_red1 {Σ d t1 t2} (h : Σ |-i t1 ▷ t2) :
  (d::Σ) |-i t1 ▷ t2

with weak_glob_redbrs1 {Σ d b1 b2} (h : redbrs1 Σ b1 b2) :
  redbrs1 (d::Σ) b1 b2.
Proof.
  - induction h ; try (econstructor ; eassumption).
    econstructor. eapply weak_glob_redbrs1. assumption.
  - destruct h.
    + econstructor. eapply weak_glob_red1. assumption.
    + econstructor. eapply weak_glob_redbrs1. assumption.
Defined.

Lemma weak_glob_conv :
  forall {Σ ϕ d t1 t2},
    (Σ, ϕ) |-i t1 = t2 ->
    (d::Σ, ϕ) |-i t1 = t2.
Proof.
  intros Σ ϕ d t1 t2 h. induction h.
  all: try (econstructor ; eassumption).
  - cbn in *. eapply conv_red_l ; try eassumption.
    cbn. eapply weak_glob_red1. assumption.
  - cbn in *. eapply conv_red_r ; try eassumption.
    cbn. eapply weak_glob_red1. assumption.
Defined.

Fixpoint weak_glob_type {Σ ϕ Γ t A} (h : (Σ,ϕ) ;;; Γ |-i t : A) :
  forall {d},
    fresh_global (sglobal_decl_ident d) Σ ->
    (d::Σ, ϕ) ;;; Γ |-i t : A

with weak_glob_wf {Σ ϕ Γ} (h : wf (Σ,ϕ) Γ) :
  forall {d},
    fresh_global (sglobal_decl_ident d) Σ ->
    wf (d::Σ, ϕ) Γ.
Proof.
  (* weak_glob_type *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                try apply weak_glob_conv ;
                eassumption
               ).
      - eapply type_HeqTrans with (B := B) (b := b).
        all: apply weak_glob_type ; eassumption.
      - eapply type_ProjT2 with (A1 := A1).
        all: apply weak_glob_type ; eassumption.
      - eapply type_Ind with (univs := univs).
        + apply weak_glob_wf ; assumption.
        + destruct isdecl as [decl' [[h1 h2] h3]].
          exists decl'. repeat split.
          * cbn in *. unfold sdeclared_minductive in *.
            cbn. erewrite ident_neq_fresh by eassumption.
            assumption.
          * assumption.
          * assumption.
      - cbn in *.
        destruct isdecl as [decl' [[d' [[h1 h2] h3]] h4]] eqn:eq.
        rewrite <- eq.
        assert (isdecl' : sdeclared_constructor (d :: Σ) (ind, i) univs decl).
        { exists decl'. split.
          - exists d'. repeat split.
            + unfold sdeclared_minductive in *.
              cbn. erewrite ident_neq_fresh by eassumption.
              assumption.
            + assumption.
            + assumption.
          - assumption.
        }
        eapply meta_conv.
        + eapply type_Construct.
          apply weak_glob_wf ; assumption.
        + instantiate (3 := univs).
          instantiate (2 := decl).
          instantiate (1 := isdecl').
          cbn in *.
          eapply stype_of_constructor_cons. assumption.
    }

  (* weak_glob_wf *)
  - { dependent destruction h ; intros fd.
      - constructor.
      - econstructor.
        + apply weak_glob_wf ; assumption.
        + apply weak_glob_type ; eassumption.
    }
Defined.

Corollary weak_glob_isType :
  forall {Σ ϕ Γ A} (h : isType (Σ,ϕ) Γ A) {d},
    fresh_global (sglobal_decl_ident d) Σ ->
    isType (d::Σ, ϕ) Γ A.
Proof.
  intros Σ ϕ Γ A h d hf.
  destruct h as [s h].
  exists s. eapply weak_glob_type ; eassumption.
Defined.

Fact isArity_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs}
      (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
      isArity Σ (indpars isdecl) (sind_indices decl)
              (sind_sort decl) (sind_type decl).
Proof.
  intros Σ hg. destruct Σ as [Σ ϕ].
  dependent induction hg.
  - intros ind decl univs isdecl.
    cbn in *. destruct isdecl as [decl' [[h1 h2] h3]].
    inversion h1.
  - intros ind decl univs isdecl.
    destruct isdecl as [decl' [[h1 h2] h3]].
    cbn in h1. unfold sdeclared_minductive in h1.
    cbn in h1.
    rewrite indpars_def.
    case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident d)).
    + intro e. rewrite e in h1.
      inversion h1 as [ h1' ]. subst.
      cbn in t. clear e.
      destruct (isArity_ind_type' t h3) as [? ?].
      split ; try assumption.
      eapply weak_glob_wf ; assumption.
    + intro e. rewrite e in h1.
      edestruct (IHhg ind decl univs) as [hw eq].
      erewrite indpars_def in eq, hw.
      split ; try eassumption.
      eapply weak_glob_wf ; eassumption.
  Unshelve. all: eassumption.
Defined.

Fact typed_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      isType Σ [] (sind_type decl).
Proof.
  intros Σ hg ind decl univs isdecl.
  destruct (isArity_ind_type hg isdecl) as [h1 h2].
  rewrite h2.
  eapply type_Prods. eapply istype_nctx_spec.
  eexists. econstructor. rewrite nil_cat. assumption.
Defined.

Fact lift_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      forall n k,
        lift n k (sind_type decl) = sind_type decl.
Proof.
  intros Σ hg ind decl univs h n k.
  destruct (typed_ind_type hg h).
  eapply closed_lift.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Fact xcomp_ind_type' :
  forall {Σ : sglobal_context} {decl'},
    type_inductive Σ decl'.(sind_params) (sind_bodies decl') ->
    forall {n decl},
      nth_error (sind_bodies decl') n = Some decl ->
      Xcomp (sind_type decl).
Proof.
  intros Σ decl' [hx hind].
  induction hind.
  - intros n decl h.
    destruct n ; cbn in h ; inversion h.
  - intros n decl h.
    destruct n.
    + cbn in h. inversion h as [ e ]. subst. clear h.
      cbn. assumption.
    + cbn in h. eapply IHhind.
      eassumption.
Defined.

Fact xcomp_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      Xcomp (sind_type decl).
Proof.
  intros Σ hg. destruct Σ as [Σ ϕ].
  dependent induction hg.
  - intros ind decl univs isdecl.
    cbn in *. destruct isdecl as [decl' [[h1 h2] h3]].
    inversion h1.
  - intros ind decl univs isdecl.
    destruct isdecl as [decl' [[h1 h2] h3]].
    cbn in h1. unfold sdeclared_minductive in h1.
    cbn in h1.
    case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident d)).
    + intro e. rewrite e in h1.
      inversion h1 as [ h1' ]. subst.
      cbn in t. clear e.
      apply (xcomp_ind_type' t h3).
    + intro e. rewrite e in h1.
      apply (IHhg ind decl univs).
      exists decl'. repeat split ; eassumption.
Defined.

Fact type_inddecls_constr :
  forall {Σ : sglobal_context} {params inds Γ},
    type_inddecls Σ params Γ inds ->
    forall {n decl},
      nth_error inds n = Some decl ->
      type_constructors Σ params Γ (sind_ctors decl).
Proof.
  intros Σ params inds Γ hind. induction hind.
  - intros n decl h.
    destruct n ; cbn in h ; inversion h.
  - intros n decl h.
    destruct n.
    + cbn in h. inversion h as [ e ]. subst. clear h.
      simpl. assumption.
    + cbn in h. eapply IHhind. eassumption.
Defined.

Fact type_ind_type_constr :
  forall {Σ : sglobal_context} {params inds},
    type_inductive Σ params inds ->
    forall {n decl},
      nth_error inds n = Some decl ->
      type_constructors Σ params (arities_context inds) (sind_ctors decl).
Proof.
  intros Σ params inds [hx hind] n decl h.
  eapply type_inddecls_constr ; eassumption.
Defined.

Fact typed_type_constructors :
  forall {Σ : sglobal_context} {pars Γ l},
    type_constructors Σ pars Γ l ->
    forall {i decl},
      nth_error l i = Some decl ->
      let '(_, t, _, _) := decl in
      isType Σ Γ t.
Proof.
  intros Σ pars Γ l htc. induction htc ; intros m decl hm.
  - destruct m ; cbn in hm ; inversion hm.
  - destruct m.
    + cbn in hm. inversion hm. subst. clear hm.
      eapply type_Prods. apply istype_nctx_spec. assumption.
    + cbn in hm. eapply IHhtc. eassumption.
Defined.

(* TODO: Move the 6 next constructions away. *)
Fact substl_cons :
  forall {a l t}, substl (a :: l) t = (substl l (t{ 0 := a })).
Proof.
  reflexivity.
Defined.

Inductive closed_list : list sterm -> Type :=
| closed_list_nil : closed_list nil
| closed_list_cons a l :
    closed_above #|l| a = true ->
    closed_list l ->
    closed_list (a :: l).

Derive Signature for closed_list.

Fact closed_substl :
  forall {l},
    closed_list l ->
    forall {t},
      closed_above #|l| t = true ->
      closed (substl l t).
Proof.
  intros l cl. induction cl ; intros t h.
  - cbn in *. assumption.
  - rewrite substl_cons. apply IHcl.
    apply closed_above_subst.
    + omega.
    + assumption.
    + replace (#|l| - 0) with #|l| by omega. assumption.
Defined.

Fact sinds_cons :
  forall {ind a l}, sinds ind (a :: l) = sInd (mkInd ind #|l|) :: sinds ind l.
Proof.
  intros ind a l. reflexivity.
Defined.

Fact arities_context_cons :
  forall {a l},
    arities_context (a :: l) =
    [ (sind_type a) ] ,,, arities_context l.
Proof.
  intros a l.
  unfold arities_context.
  rewrite rev_map_cons. reflexivity.
Defined.

Fact sinds_length :
  forall {ind l},
    #|sinds ind l| = #|l|.
Proof.
  intros ind l.
  induction l.
  - reflexivity.
  - rewrite sinds_cons. cbn. omega.
Defined.

Fact length_sinds_arities :
  forall {ind l},
    #|sinds ind l| = #|arities_context l|.
Proof.
  intros ind l.
  rewrite rev_map_length, sinds_length.
  reflexivity.
Defined.

Fact closed_sinds :
  forall {Σ id pars l},
      type_inductive Σ pars l ->
      closed_list (sinds id l).
Proof.
  intros Σ id pars l [_ ti].
  unfold type_inductive in ti. induction ti.
  - cbn. constructor.
  - rewrite sinds_cons. econstructor.
    + reflexivity.
    + assumption.
Defined.

Fact closed_type_of_constructor :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind i decl univs}
      (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
      closed (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl).
Proof.
  intros Σ hg. unfold type_glob in hg. destruct Σ as [Σ ϕ].
  cbn in hg.
  induction hg ; intros ind i decl univs isdecl.
  - cbn. bang.
  - case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident d)).
    + intro e.
      destruct isdecl as [ib [[mb [[d' ?] hn]] hn']].
      assert (eqd : d = SInductiveDecl (inductive_mind ind) mb).
      { unfold sdeclared_minductive in d'. cbn in d'. rewrite e in d'.
        now inversion d'.
      }
      subst.
      rewrite stype_of_constructor_eq by assumption.
      cbn in t.
      eapply closed_substl.
      * eapply closed_sinds. eassumption.
      * destruct decl as [[id trm] ci].
        pose proof (type_ind_type_constr t hn) as tc.
        destruct (typed_type_constructors tc hn') as [s ?].
        rewrite length_sinds_arities.
        eapply type_ctx_closed_above.
        eassumption.
    + intro e. erewrite stype_of_constructor_cons by assumption.
      apply IHhg.
      Unshelve.
      destruct isdecl as [ib [[mb [[d' ?] ?]] ?]].
      exists ib. split.
      * exists mb. repeat split.
        -- unfold sdeclared_minductive in *. cbn in d'.
           rewrite e in d'. exact d'.
        -- assumption.
        -- assumption.
      * assumption.
Defined.

Definition xcomp_list : list sterm -> Type :=
  ForallT Xcomp.

Fact xcomp_lift :
  forall {t}, Xcomp t ->
  forall {n k}, Xcomp (lift n k t).
Proof.
  intros t h. induction h ; intros m k.
  all: try (cbn ; constructor ; easy).
  cbn. destruct (k <=? n) ; constructor.
Defined.

Fact xcomp_subst :
  forall {t}, Xcomp t ->
  forall {u}, Xcomp u ->
  forall {n}, Xcomp (t{ n := u}).
Proof.
  intros t ht. induction ht ; intros t' ht' m.
  all: try (cbn ; constructor ; easy).
  cbn. case_eq (m ?= n) ; try constructor.
  intro e. apply xcomp_lift. assumption.
Defined.

Fact xcomp_substl :
  forall {l},
    xcomp_list l ->
    forall {t},
      Xcomp t ->
      Xcomp (substl l t).
Proof.
  intros l xl. induction xl ; intros t h.
  - cbn. assumption.
  - rewrite substl_cons. apply IHxl.
    apply xcomp_subst ; assumption.
Defined.

Fact xcomp_sinds :
  forall {Σ id pars l},
      type_inductive Σ pars l ->
      xcomp_list (sinds id l).
Proof.
  intros Σ id pars l [_ ti].
  unfold type_inductive in ti. induction ti.
  - cbn. constructor.
  - rewrite sinds_cons. econstructor.
    + constructor.
    + assumption.
Defined.

Fact xcomp_type_constructors :
  forall {Σ : sglobal_context} {pars Γ l },
    type_constructors Σ pars Γ l ->
    forall {i decl},
      nth_error l i = Some decl ->
      let '(_, t, _, _) := decl in
      Xcomp t.
Proof.
  intros Σ pars Γ l htc. induction htc ; intros m decl hm.
  - destruct m ; cbn in hm ; inversion hm.
  - destruct m.
    + cbn in hm. inversion hm. subst. clear hm.
      assumption.
    + cbn in hm. eapply IHhtc. eassumption.
Defined.

Fact xcomp_type_of_constructor :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind i decl univs}
      (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
      Xcomp (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl).
Proof.
  intros Σ hg. unfold type_glob in hg. destruct Σ as [Σ ϕ].
  cbn in hg.
  induction hg ; intros ind i decl univs isdecl.
  - cbn. bang.
  - case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident d)).
    + intro e.
      destruct isdecl as [ib [[mb [[d' ?] hn]] hn']].
      assert (eqd : d = SInductiveDecl (inductive_mind ind) mb).
      { unfold sdeclared_minductive in d'. cbn in d'. rewrite e in d'.
        now inversion d'.
      }
      subst.
      rewrite stype_of_constructor_eq by assumption.
      cbn in t.
      eapply xcomp_substl.
      * eapply xcomp_sinds. eassumption.
      * destruct decl as [[id trm] ci].
        pose proof (type_ind_type_constr t hn) as tc.
        apply (xcomp_type_constructors tc hn').
    + intro e. erewrite stype_of_constructor_cons by assumption.
      apply IHhg.
      Unshelve.
      destruct isdecl as [ib [[mb [[d' ?] ?]] ?]].
      exists ib. split.
      * exists mb. repeat split.
        -- unfold sdeclared_minductive in *. cbn in d'.
           rewrite e in d'. exact d'.
        -- assumption.
        -- assumption.
      * assumption.
Defined.

Fact lift_type_of_constructor :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind i decl univs}
      {isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl},
      forall n k,
        lift n k (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl) =
        stype_of_constructor (fst Σ) (ind, i) univs decl isdecl.
Proof.
  intros Σ hg ind i decl univs isdecl n k.
  eapply closed_lift.
  eapply closed_type_of_constructor.
  assumption.
Defined.

Ltac ih h :=
  lazymatch goal with
  | [ type_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Ξ |-i t : A ->
          type_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Ξ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_lift"
  end.

Ltac eih :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i lift _ _ ?t : _ => ih h
  | _ => fail "Not handled by eih"
  end.

Fixpoint type_lift {Σ Γ Δ Ξ t A} (h : Σ ;;; Γ ,,, Ξ |-i t : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A

with wf_lift {Σ Γ Δ Ξ} (h : wf Σ (Γ ,,, Ξ)) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  wf Σ (Γ ,,, Δ ,,, lift_context #|Δ| Ξ)
.
Proof.
  - { dependent destruction h ; intros hΣ hwf.
      - cbn. case_eq (#|Ξ| <=? n) ; intro e ; bprop e.
        + rewrite liftP3 by omega.
          replace (#|Δ| + S n)%nat with (S (#|Δ| + n)) by omega.
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_lift ; assumption.
          * f_equal. f_equal.
            erewrite 3!safe_nth_ge'
              by (try rewrite lift_context_length ; omega).
            eapply safe_nth_cong_irr.
            rewrite lift_context_length. omega.
        + eapply meta_conv.
          * eapply type_Rel. eapply wf_lift ; assumption.
          * erewrite 2!safe_nth_lt.
            eapply lift_context_ex.
      - cbn. apply type_Sort. now apply wf_lift.
      - cbn. eapply type_Prod ; eih.
      - cbn. eapply type_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite substP1.
        eapply type_App ; eih.
      - cbn. apply type_Eq ; eih.
      - cbn. eapply type_Refl ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by omega.
        rewrite substP1.
        cbn. eapply type_J ; try eih.
        + cbn. unfold ssnoc. cbn.
          f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by omega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by omega.
          change (sRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u))
            with (lift #|Δ| #|Ξ| (sRefl A0 u)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply type_Transport ; eih.
      - cbn. eapply type_Heq ; eih.
      - cbn. eapply type_HeqToEq ; eih.
      - cbn. eapply type_HeqRefl ; eih.
      - cbn. eapply type_HeqSym ; eih.
      - cbn. eapply @type_HeqTrans with (B := lift #|Δ| #|Ξ| B) (b := lift #|Δ| #|Ξ| b) ; eih.
      - cbn. eapply type_HeqTransport ; eih.
      - cbn. eapply type_CongProd ; try eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; try eih.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := v1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := v1 })).
        change (lift #|Δ| #|Ξ| (B2 {0 := v2}))
          with (lift #|Δ| (0 + #|Ξ|) (B2 { 0 := v2 })).
        rewrite 2!substP1.
        eapply type_CongApp ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongEq ; eih.
      - cbn. eapply type_CongRefl ; eih.
      - cbn. eapply type_EqToHeq ; eih.
      - cbn. eapply type_HeqTypeEq ; eih.
      - cbn. eapply type_Pack ; eih.
      - cbn. eapply @type_ProjT1 with (A2 := lift #|Δ| #|Ξ| A2) ; eih.
      - cbn. eapply @type_ProjT2 with (A1 := lift #|Δ| #|Ξ| A1) ; eih.
      - cbn. eapply type_ProjTe ; eih.
      - cbn. erewrite lift_ind_type by eassumption.
        eapply type_Ind.
        + now apply wf_lift.
        + eassumption.
      - cbn. erewrite lift_type_of_constructor by eassumption.
        eapply type_Construct. now apply wf_lift.
      - eapply type_conv ; try eih.
        eapply lift_conv. assumption.
    }

  (* wf_lift *)
  - { intros hg hwf.
      destruct Ξ.
      - cbn. assumption.
      - dependent destruction h.
        cbn. econstructor.
        + apply wf_lift ; assumption.
        + instantiate (1 := s0). cbn. change (sSort s0) with (lift #|Δ| #|Ξ| (sSort s0)).
          apply type_lift ; assumption.
    }

    Unshelve.
    all: try rewrite !length_cat ; try rewrite length_cat in isdecl ;
      try rewrite lift_context_length ; omega.
Defined.

Corollary typing_lift01 :
  forall {Σ Γ t A B s},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, B |-i lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A B s hg ht hB.
  apply (@type_lift _ _ [ B ] nil _ _ ht hg).
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

Corollary typing_lift02 :
  forall {Σ Γ t A B s C s'},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, B |-i C : sSort s' ->
    Σ ;;; Γ ,, B ,, C |-i lift0 2 t : lift0 2 A.
Proof.
  intros Σ Γ t A B s C s' hg ht hB hC.
  assert (eq : forall t, lift0 2 t = lift0 1 (lift0 1 t)).
  { intro u. rewrite lift_lift. reflexivity. }
  rewrite !eq. eapply typing_lift01.
  - assumption.
  - eapply typing_lift01  ; eassumption.
  - eassumption.
Defined.

Fact subst_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      forall n u,
        (sind_type decl){ n := u } = sind_type decl.
Proof.
  intros Σ hg ind decl univs h n u.
  destruct (typed_ind_type hg h).
  eapply closed_subst.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Fact subst_type_of_constructor :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind i decl univs}
      {isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl},
      forall n u,
        (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl){ n := u } =
        stype_of_constructor (fst Σ) (ind, i) univs decl isdecl.
Proof.
  intros Σ hg ind i decl univs isdecl n u.
  eapply closed_subst.
  eapply closed_type_of_constructor.
  assumption.
Defined.

Ltac sh h :=
  lazymatch goal with
  | [ type_subst :
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A : sterm)
          (B u : sterm),
          Σ;;; Γ,, B ,,, Δ |-i t : A ->
          type_glob Σ ->
          Σ;;; Γ |-i u : B -> Σ;;; Γ ,,, subst_context u Δ |-i
          t {#|Δ| := u} : A {#|Δ| := u}
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,, ?B' ,,, ?Δ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, ?B' ,,, ?Δ') ,, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "cannot find type_subst"
  end.

Ltac esh :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i ?t{ _ := _ } : _ => sh h
  | _ => fail "not handled by esh"
  end.

Fixpoint type_subst {Σ Γ Δ t A B u}
  (h : Σ ;;; Γ ,, B ,,, Δ |-i t : A) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-i t{ #|Δ| := u } : A{ #|Δ| := u }

with wf_subst {Σ Γ Δ B u}
  (h : wf Σ (Γ ,, B ,,, Δ)) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  wf Σ (Γ ,,, subst_context u Δ)
.
Proof.
  (* type_subst *)
  - { intros hg hu.
      dependent destruction h.
      - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
        + assert (h : n >= #|Δ|) by omega.
          rewrite safe_nth_ge' with (h0 := h).
          assert (n - #|Δ| = 0) by omega.
          set (ge := ge_sub isdecl h).
          generalize ge.
          rewrite H0. intro ge'.
          cbn. rewrite substP3 by omega.
          subst.
          replace #|Δ| with #|subst_context u Δ|
            by (now rewrite subst_context_length).
          eapply @type_lift with (Ξ := []) (Δ := subst_context u Δ).
          * cbn. assumption.
          * assumption.
          * eapply wf_subst ; eassumption.
        + assert (h : n >= #|Δ|) by omega.
          rewrite safe_nth_ge' with (h0 := h).
          set (ge := ge_sub isdecl h).
          destruct n ; try easy.
          rewrite substP3 by omega.
          generalize ge.
          replace (S n - #|Δ|) with (S (n - #|Δ|)) by omega.
          cbn. intro ge'.
          eapply meta_conv.
          * eapply type_Rel. eapply wf_subst ; eassumption.
          * erewrite safe_nth_ge'.
            f_equal. eapply safe_nth_cong_irr.
            rewrite subst_context_length. reflexivity.
        + assert (h : n < #|Δ|) by omega.
          rewrite @safe_nth_lt with (isdecl' := h).
          match goal with
          | |- _ ;;; _ |-i _ : ?t{?d := ?u} =>
            replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
              by (f_equal ; omega)
          end.
          rewrite substP2 by omega.
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_subst ; eassumption.
          * f_equal.
            erewrite safe_nth_lt.
            eapply safe_nth_subst_context.
      - cbn. apply type_Sort. eapply wf_subst ; eassumption.
      - cbn. eapply type_Prod ; esh.
      - cbn. eapply type_Lambda ; esh.
      - cbn.
        change ((B0 {0 := u0}) {#|Δ| := u})
          with ((B0 {0 := u0}) {0 + #|Δ| := u}).
        rewrite substP4. cbn.
        eapply type_App ; esh.
      - cbn. eapply type_Eq ; esh.
      - cbn. eapply type_Refl ; esh.
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
        rewrite substP4.
        eapply type_J ; esh.
        + cbn. unfold ssnoc. cbn.
          f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
          change (sRefl (A0 {0 + #|Δ| := u}) (u0 {0 + #|Δ| := u}))
            with ((sRefl A0 u0){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply type_Transport ; esh.
      - cbn. eapply type_Heq ; esh.
      - cbn. eapply type_HeqToEq ; esh.
      - cbn. eapply type_HeqRefl ; esh.
      - cbn. eapply type_HeqSym ; esh.
      - cbn. eapply type_HeqTrans with (B := B0{ #|Δ| := u }) (b := b{ #|Δ| := u }) ; esh.
      - cbn. eapply type_HeqTransport ; esh.
      - cbn. eapply type_CongProd ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; esh.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply type_CongApp ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongEq ; esh.
      - cbn. eapply type_CongRefl ; esh.
      - cbn. eapply type_EqToHeq ; esh.
      - cbn. eapply type_HeqTypeEq ; esh.
      - cbn. eapply type_Pack ; esh.
      - cbn. eapply @type_ProjT1 with (A2 := A2{#|Δ| := u}) ; esh.
      - cbn. eapply @type_ProjT2 with (A1 := A1{#|Δ| := u}) ; esh.
      - cbn. eapply type_ProjTe ; esh.
      - cbn. erewrite subst_ind_type by eassumption.
        eapply type_Ind.
        + now eapply wf_subst.
        + eassumption.
      - cbn. erewrite subst_type_of_constructor by eassumption.
        eapply type_Construct. now eapply wf_subst.
      - cbn. eapply type_conv ; try esh.
        eapply subst_conv. eassumption.
    }

  (* wf_subst *)
  - { intros hg hu.
      destruct Δ.
      - cbn. dependent destruction h. assumption.
      - dependent destruction h. cbn. econstructor.
        + eapply wf_subst ; eassumption.
        + esh.
    }

  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; omega.
Defined.

Corollary typing_subst :
  forall {Σ Γ t A B u},
    type_glob Σ ->
    Σ ;;; Γ ,, A |-i t : B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i t{ 0 := u } : B{ 0 := u }.
Proof.
  intros Σ Γ t A B u hg ht hu.
  eapply @type_subst with (Δ := []) ; eassumption.
Defined.

Corollary typing_subst2 :
  forall {Σ Γ t A B C u v},
    type_glob Σ ->
    Σ ;;; Γ ,, A ,, B |-i t : C ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B{ 0 := u } ->
    Σ ;;; Γ |-i t{ 1 := u }{ 0 := v } : C{ 1 := u }{ 0 := v }.
Proof.
  intros Σ Γ t A B C u v hg ht hu hv.
  eapply @type_subst with (Δ := []).
  - eapply @type_subst with (Δ := [ B ]).
    + exact ht.
    + assumption.
    + assumption.
  - assumption.
  - cbn. assumption.
Defined.

Corollary type_substln :
  forall {Σ l Γ Δ},
    type_glob Σ ->
    typed_list Σ Γ l Δ ->
    forall {t T Ξ},
      Σ ;;; Γ ,,, Δ ,,, Ξ |-i t : T ->
      Σ ;;; Γ ,,, substln_context l Ξ |-i substln l #|Ξ| t : substln l #|Ξ| T.
Proof.
  intros Σ l Γ Δ hg tl.
  induction tl ; intros u C Ξ h.
  - cbn. assumption.
  - simpl.
    replace #|Ξ| with #|subst_context A Ξ|
      by (now rewrite subst_context_length).
    apply IHtl.
    rewrite subst_context_length.
    eapply type_subst.
    + exact h.
    + assumption.
    + assumption.
Defined.

Fact substln_sort :
  forall {l n s}, substln l n (sSort s) = sSort s.
Proof.
  intro l. induction l ; intros n s.
  - cbn. reflexivity.
  - simpl. apply IHl.
Defined.

Corollary type_substl :
  forall {Σ l Γ Δ},
    type_glob Σ ->
    typed_list Σ Γ l Δ ->
    forall {t T},
      Σ ;;; Γ ,,, Δ |-i t : T ->
      Σ ;;; Γ |-i substl l t : substl l T.
Proof.
  intros Σ l Γ Δ hg tl.
  induction tl ; intros u C h.
  - cbn. assumption.
  - rewrite !substl_cons. apply IHtl.
    eapply typing_subst.
    + assumption.
    + exact h.
    + assumption.
Defined.

Fact substl_sort :
  forall {l s}, substl l (sSort s) = sSort s.
Proof.
  intro l. induction l ; intro s.
  - cbn. reflexivity.
  - rewrite substl_cons. cbn. apply IHl.
Defined.

Fact substl1_subst0 :
  forall {l t u},
    (substln l 1 t){ 0 := substl l u } = substl l (t{ 0 := u }).
Proof.
  intros l. induction l ; intros t u.
  - cbn. reflexivity.
  - simpl. rewrite IHl. f_equal.
    change 0 with (0 + 0)%nat at 4.
    rewrite substP4. cbn.
    reflexivity.
Defined.

Fact substln_context_nil :
  forall {l},
    substln_context l [] = [].
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. assumption.
Defined.

Fact substln_context_cons :
  forall {l A Γ},
    substln_context l (Γ,, A) = substln_context l Γ,, substln l #|Γ| A.
Proof.
  intros l. induction l ; intros A Γ.
  - cbn. reflexivity.
  - simpl. rewrite IHl.
    rewrite subst_context_length. reflexivity.
Defined.

(* TODO Define substl as substln _ 0 *)
Fact substl_substln0 :
  forall {l u},
    substl l u = substln l 0 u.
Proof.
  intro l. induction l ; intro u.
  - cbn. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Defined.

Fact substl_Prod :
  forall {l nx A B},
    substl l (sProd nx A B) =
    sProd nx (substl l A) (substln l 1 B).
Proof.
  intro l. induction l ; intros nx A B.
  - cbn. reflexivity.
  - simpl. rewrite IHl.
    reflexivity.
Defined.

Fact map_i_aux_S :
  forall {A B} {f : nat -> A -> B} {n l},
    map_i_aux f (S n) l = map_i_aux (fun i a => f (S i) a) n l.
Proof.
  intros A B f n l. revert n.
  induction l ; intro n.
  - cbn. reflexivity.
  - simpl. f_equal. apply IHl.
Defined.

Fact map_i_eqf :
  forall {A B} {f g : nat -> A -> B} {l n},
    (forall i a, f i a = g i a) ->
    map_i_aux f n l = map_i_aux g n l.
Proof.
  intros A B f g l n h. revert n.
  induction l ; intros n.
  - reflexivity.
  - cbn. f_equal ; auto.
Defined.

(* TODO MOVE *)
Fact lift_nctx_cons :
  forall {L nx A n k},
    lift_nctx n k ((nx, A) :: L) =
    (nx, lift n k A) :: lift_nctx n (S k) L.
Proof.
  reflexivity.
Defined.

Fact lift_Prods :
  forall {Δ T n k},
    lift n k (Prods Δ T) =
    Prods (lift_nctx n k Δ) (lift n (#|Δ| + k) T).
Proof.
  intro Δ. induction Δ as [| [nx A] Δ ih] ; intros T n k.
  - cbn. reflexivity.
  - rewrite lift_nctx_cons. simpl. f_equal.
    rewrite ih. f_equal. f_equal. omega.
Defined.

Fact substn_nctx_cons :
  forall {L u n nx A},
    substn_nctx u n ((nx,A) :: L) = (nx, A{ n := u }) :: substn_nctx u (S n) L.
Proof.
  reflexivity.
Defined.

Fact subst_Prods :
  forall {Δ T u n},
    (Prods Δ T){ n := u } =
    Prods (substn_nctx u n Δ) (T{ #|Δ| + n := u }).
Proof.
  intro Δ. induction Δ as [| [nx A] Δ ih] ; intros T u n.
  - cbn. reflexivity.
  - rewrite substn_nctx_cons.
    simpl. f_equal. rewrite ih. f_equal. f_equal.
    omega.
Defined.

Corollary subst0_Prods :
  forall {Δ T u},
    (Prods Δ T){ 0 := u } =
    Prods (subst_nctx u Δ) (T{ #|Δ| := u }).
Proof.
  intros Δ T u.
  unfold subst_nctx.
  pose proof (@subst_Prods Δ T u 0) as h. unfold map_i in *.
  erewrite map_i_eqf.
  - replace #|Δ| with (#|Δ| + 0)%nat by omega.
    apply h.
  - clear. intros i a. cbn.
    replace (i + 0)%nat with i by omega.
    reflexivity.
Defined.

Lemma istype_nctx_substn :
  forall {Σ Γ Δ L T s A u z},
    type_glob Σ ->
    istype_nctx Σ (Γ,, A ,,, Δ) L T ->
    Σ;;; Γ |-i A : sSort s ->
    Σ;;; Γ |-i u : A ->
    Σ;;; Γ,, A ,,, Δ |-i Prods L T : sSort z ->
    istype_nctx Σ (Γ ,,, subst_context u Δ)
                (substn_nctx u #|Δ| L) (T{ #|L| + #|Δ| := u }).
Proof.
  intros Σ Γ Δ L T s A u z hg hL hA hu hP.
  revert u s hA hu z hP. dependent induction hL ; intros u z hA hu z' hP.
  - rename Γ0 into Γ. cbn.
    econstructor.
    match goal with
    | |- _ ;;; _ |-i _ : ?S =>
      change S with (S{#|Δ| := u})
    end.
    cbn in hP.
    eapply type_subst ; eassumption.
  - rename Γ0 into Γ, A0 into B.
    simpl. rewrite substn_nctx_cons.
    econstructor.
    + specialize (IHhL Γ (Δ ,, A) L T B hg eq_refl).
      replace (S (#|L| + #|Δ|))%nat with (#|L| + S #|Δ|)%nat by omega.
      cbn in hP. ttinv hP.
      eapply IHhL ; eassumption.
    + match goal with
      | |- _ ;;; _ |-i _ : ?S =>
        change S with (S{#|Δ| := u})
      end.
      eapply type_subst ; eassumption.
Defined.

Corollary istype_nctx_subst0 :
  forall {Σ Γ L T s A u z},
    type_glob Σ ->
    istype_nctx Σ (Γ,, A) L T ->
    Σ;;; Γ |-i A : sSort s ->
    Σ;;; Γ |-i u : A ->
    Σ;;; Γ,, A |-i Prods L T : sSort z ->
    istype_nctx Σ Γ (subst_nctx u L) (T {#|L| := u}).
Proof.
  intros Σ Γ L T s A u z hg hL hA hu hP.
  pose proof (@istype_nctx_substn Σ Γ [] L T s A u z hg) as h.
  cbn in h.
  replace (substn_nctx u 0) with (subst_nctx u) in h by reflexivity.
  replace (#|L| + 0)%nat with #|L| in h by omega.
  apply h ; assumption.
Defined.

Lemma type_Apps :
  forall {Σ Γ Δ f l T T'},
    type_glob Σ ->
    Σ ;;; Γ |-i f : Prods Δ T ->
    istype_nctx Σ Γ Δ T ->
    type_spine Σ Γ Δ T l T' ->
    Σ ;;; Γ |-i Apps f Δ T l : T'.
Proof.
  intros Σ Γ Δ f l T T' hg hf ht hl.
  revert f hf.
  induction hl ; intros f hf.
  - cbn in *. assumption.
  - cbn in *.
    dependent destruction ht.
    rename Γ0 into Γ, A0 into A, T0 into T, nx0 into nx.
    destruct (type_Prods ht) as [z hp].
    eapply IHhl.
    + eapply istype_nctx_subst0 ; eassumption.
    + eapply meta_conv.
      * eapply type_App ; eassumption.
      * apply subst0_Prods.
Defined.

Fact ind_bodies_declared :
  forall {Σ ind mb},
    sdeclared_minductive Σ (inductive_mind ind) mb ->
    forall {n d},
      nth_error (sind_bodies mb) n = Some d ->
      sdeclared_inductive Σ (mkInd (inductive_mind ind) n) (sind_universes mb) d.
Proof.
  intros Σ ind mb hd n d hn.
  exists mb. repeat split.
  - cbn. assumption.
  - cbn. assumption.
Defined.

Fact nth_error_error :
  forall {A} {l : list A} {n},
    nth_error l n = None ->
    n >= #|l|.
Proof.
  intros A l. induction l.
  - intros. cbn. omega.
  - intros n h. cbn.
    destruct n.
    + cbn in h. inversion h.
    + inversion h as [e].
      specialize (IHl n e).
      omega.
Defined.

Fact rev_map_nth_error :
  forall {A B} {f : A -> B} {l n a},
    nth_error l n = Some a ->
    nth_error (rev_map f l) (#|l| - S n) = Some (f a).
Proof.
  intros A B f l. induction l ; intros n x hn.
  - destruct n ; inversion hn.
  - destruct n.
    + cbn in hn. inversion hn.
      rewrite rev_map_cons.
      rewrite nth_error_app2.
      * cbn. rewrite rev_map_length.
        replace (#|l| - 0 - #|l|) with 0 by omega.
        cbn. reflexivity.
      * rewrite rev_map_length. cbn. omega.
    + cbn in hn.
      rewrite rev_map_cons.
      rewrite nth_error_app1.
      * erewrite IHl by eassumption. reflexivity.
      * rewrite rev_map_length. cbn.
        assert (n < #|l|).
        { apply nth_error_Some. rewrite hn. discriminate. }
        omega.
Defined.

Fact sinds_nth_error :
  forall ind {l n},
    n < #|l| ->
    nth_error (sinds ind l) n = Some (sInd (mkInd ind (#|l| - S n))).
Proof.
  intros ind l.
  unfold sinds.
  match goal with
  | |- context [ nth_error (?faux _) ] => set (aux := faux)
  end.
  induction l ; intros n h.
  - inversion h.
  - destruct n.
    + cbn. f_equal. f_equal. f_equal. omega.
    + cbn. apply IHl. cbn in h. omega.
Defined.

Fact type_arities' :
  forall {Σ ind mb},
    type_glob Σ ->
    sdeclared_minductive (fst Σ) (inductive_mind ind) mb ->
    let id := inductive_mind ind in
    let bs := sind_bodies mb in
    let inds := sinds id bs in
    let ac := arities_context bs in
    forall n,
      let l1 := lastn n inds in
      let l2 := lastn n ac in
      (typed_list Σ [] l1 l2) * (wf Σ l2).
Proof.
  intros Σ ind mb hg hd id bs inds ac n.
  induction n.
  - rewrite !lastn_O. cbn.
    split ; constructor.
  - assert (#|ac| = #|bs|) by (apply rev_map_length).
    assert (#|inds| = #|bs|) by (apply sinds_length).
    case_eq (#|bs| <=? n) ; intro e ; bprop e ; clear e.
    + rewrite !lastn_all2 by omega.
      rewrite !lastn_all2 in IHn by omega.
      assumption.
    + intros l1 l2.
      case_eq (nth_error bs n).
      * intros a hn.
        (* Reconstructing l1 *)
        assert (e : #|inds| - S n < #|bs|) by omega.
        pose proof (sinds_nth_error id e) as hn1.
        change (sinds id bs) with inds in hn1.
        pose proof (lastn_reconstruct hn1 ltac:(omega)) as hl1.
        change (lastn (S n) inds) with l1 in hl1.
        set (l1' := lastn n inds) in *.
        (* Same with l2 *)
        assert (hn2 : nth_error ac (#|ac| - S n) = Some (sind_type a)).
        { rewrite H.
          unfold ac, arities_context.
          erewrite rev_map_nth_error.
          - reflexivity.
          - assumption.
        }
        pose proof (lastn_reconstruct hn2 ltac:(omega)) as hl2.
        change (lastn (S n) ac) with l2 in hl2.
        set (l2' := lastn n ac) in *.
        unfold l1 in IHn.
        destruct IHn as [ih1 ih2].
        rewrite !hl1, !hl2.
        set (univs := sind_universes mb).
        assert (isdecl :
          sdeclared_inductive (fst Σ) {| inductive_mind := id; inductive_ind := #|bs| - S (#|inds| - S n) |} univs a
        ).
        { eapply ind_bodies_declared ; try eassumption.
          replace (#|bs| - S (#|inds| - S n)) with n by omega.
          assumption.
        }
        split.
        -- econstructor.
           ++ assumption.
           ++ rewrite nil_cat. eapply type_Ind ; eassumption.
        -- destruct (typed_ind_type hg isdecl) as [s h].
           econstructor.
           ++ assumption.
           ++ instantiate (1 := s).
              change (sSort s) with (lift #|l2'| #|@nil sterm| (sSort s)).
              replace (sind_type a)
                with (lift #|l2'| #|@nil sterm| (sind_type a))
                by (erewrite lift_ind_type by eassumption ; reflexivity).
              eapply meta_ctx_conv.
              ** eapply @type_lift with (Γ := []) (Ξ := []) (Δ := l2').
                 --- cbn. assumption.
                 --- assumption.
                 --- rewrite nil_cat. assumption.
              ** cbn. apply nil_cat.
      * intro hn.
        pose proof (nth_error_error hn) as h. omega.
Defined.

Corollary type_arities :
  forall {Σ ind mb},
    type_glob Σ ->
    sdeclared_minductive (fst Σ) (inductive_mind ind) mb ->
    let id := inductive_mind ind in
    let bs := sind_bodies mb in
    let inds := sinds id bs in
    let ac := arities_context bs in
    (typed_list Σ [] inds ac) * (wf Σ ac).
Proof.
  intros Σ ind mb hg hd id bs inds ac.
  pose proof (type_arities' hg hd #|bs|) as h.
  rewrite !lastn_all2 in h.
  - cbn in h. apply h.
  - rewrite rev_map_length. auto.
  - rewrite sinds_length. auto.
Defined.

Fact typed_type_of_constructor :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind i decl univs}
      (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
      isType Σ [] (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl).
Proof.
  intros Σ hg. unfold type_glob in hg. destruct Σ as [Σ ϕ].
  cbn in hg.
  induction hg ; intros ind i decl univs isdecl.
  - cbn. bang.
  - case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident d)).
    + intro e.
      destruct isdecl as [ib [[mb [[d' ?] hn]] hn']].
      assert (eqd : d = SInductiveDecl (inductive_mind ind) mb).
      { unfold sdeclared_minductive in d'. cbn in d'. rewrite e in d'.
        now inversion d'.
      }
      subst.
      rewrite stype_of_constructor_eq by assumption.
      cbn in t.
      pose proof (type_ind_type_constr t hn) as tc.
      destruct (typed_type_constructors tc hn') as [s hh].
      exists s. erewrite <- substl_sort.
      eapply type_substl.
      * econstructor ; eassumption.
      * eapply type_arities.
        -- econstructor ; eassumption.
        -- cbn. assumption.
      * rewrite nil_cat.
        eapply weak_glob_type ; [| eassumption ].
        exact hh.
    + intro e. erewrite stype_of_constructor_cons by assumption.
      eapply weak_glob_isType ; [| eassumption ].
      apply IHhg.
      Unshelve.
      destruct isdecl as [ib [[mb [[d' ?] ?]] ?]].
      exists ib. split.
      * exists mb. repeat split.
        -- unfold sdeclared_minductive in *. cbn in d'.
           rewrite e in d'. exact d'.
        -- assumption.
        -- assumption.
      * assumption.
Defined.

Lemma paramless_type_of_constructor_eq :
  forall {Σ id' decl' ind i univs decl}
    {isdecl : sdeclared_constructor ((SInductiveDecl id' decl') :: Σ) (ind, i) univs decl},
    ident_eq (inductive_mind ind) id' = true ->
    let '(id, _, args, trm) := decl in
    paramless_type_of_constructor ((SInductiveDecl id' decl') :: Σ) (ind, i) univs decl isdecl =
    substln (sinds (inductive_mind ind) decl'.(sind_bodies))
            #|decl'.(sind_params)| trm.
Proof.
  intros Σ id' decl' ind i univs decl isdecl h.
  funelim (paramless_type_of_constructor (SInductiveDecl id' decl' :: Σ) (ind, i) univs decl isdecl)
  ; try bang.
  cbn. cbn in H. rewrite h in H. inversion H. subst. reflexivity.
Defined.

Lemma paramless_type_of_constructor_cons :
  forall {Σ d ind i univs decl}
    {isdecl : sdeclared_constructor Σ (ind, i) univs decl}
    {isdecl' : sdeclared_constructor (d :: Σ) (ind, i) univs decl},
    fresh_global (sglobal_decl_ident d) Σ ->
    paramless_type_of_constructor (d :: Σ) (ind, i) univs decl isdecl' =
    paramless_type_of_constructor Σ (ind, i) univs decl isdecl.
Proof.
  intros Σ d ind i univs decl isdecl isdecl' fresh.
  assert (eq : slookup_env (d :: Σ) (inductive_mind (fst (ind, i))) = slookup_env Σ (inductive_mind ind)).
  { cbn.
    destruct isdecl as [decl' [[d' [[h1 h2] h3]] h4]].
    pose proof (ident_neq_fresh h1 fresh) as neq.
    rewrite neq. reflexivity.
  }
  funelim (paramless_type_of_constructor (d :: Σ) (ind, i) univs decl isdecl')
  ; try bang.
  funelim (paramless_type_of_constructor Σ0 (ind, i) univs decl isdecl) ; try bang.
  rewrite <- eq in H. inversion H. subst. reflexivity.
Defined.

Fact typed_paramless_type_constructors :
  forall {Σ : sglobal_context} {pars Γ l},
    type_constructors Σ pars Γ l ->
    forall {i decl},
      nth_error l i = Some decl ->
      let '(_, _, _, t) := decl in
      isType Σ (Γ ,,, nlctx pars) t.
Proof.
  intros Σ pars Γ l htc. induction htc ; intros m decl hm.
  - destruct m ; cbn in hm ; inversion hm.
  - destruct m.
    + cbn in hm. inversion hm. subst. clear hm. assumption.
    + cbn in hm. eapply IHhtc. eassumption.
Defined.

Fact closed_above_substln :
  forall {l n t},
    closed_above n t = true ->
    substln l n t = t.
Proof.
  intros l. induction l ; intros n t h.
  - cbn. reflexivity.
  - simpl.
    assert (e : t{ n := a} = t).
    { eapply closed_above_subst_id ; try eassumption. omega. }
    rewrite e. apply IHl. assumption.
Defined.

Fact wf_substln_context :
  forall {Σ Γ l},
    wf Σ Γ ->
    substln_context l Γ = Γ.
Proof.
  intros Σ Γ l h. revert l.
  induction h.
  - intro l. apply substln_context_nil.
  - intro l. rewrite substln_context_cons. rewrite IHh.
    f_equal. apply closed_above_substln.
    eapply type_ctx_closed_above. eassumption.
Defined.

Fact typed_paramless_type_of_constructor :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind i decl univs}
      (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
      isType Σ (nlctx ((pi1 (fst (pi2 isdecl))).(sind_params)))
             (paramless_type_of_constructor (fst Σ) (ind, i) univs decl isdecl).
Proof.
  intros Σ hg. unfold type_glob in hg. destruct Σ as [Σ ϕ].
  cbn in hg. simpl.
  induction hg ; intros ind i decl univs isdecl.
  - cbn. bang.
  - case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident d)).
    + intro e.
      destruct isdecl as [ib [[mb [[d' ?] hn]] hn']].
      simpl.
      assert (eqd : d = SInductiveDecl (inductive_mind ind) mb).
      { unfold sdeclared_minductive in d'. cbn in d'. rewrite e in d'.
        now inversion d'.
      }
      subst.
      rewrite paramless_type_of_constructor_eq by assumption.
      cbn in t.
      pose proof (type_ind_type_constr t hn) as tc.
      destruct (typed_paramless_type_constructors tc hn') as [s hh].
      exists s. erewrite <- substln_sort.
      match type of d' with
      | sdeclared_minductive ?cc _ _ =>
        set (Σ' := cc) in *
      end.
      assert (hl : typed_list (Σ', ϕ) []
                              (sinds (inductive_mind ind) (sind_bodies mb))
                              (arities_context (sind_bodies mb))).
      { eapply type_arities.
        - econstructor ; eassumption.
        - cbn. assumption.
      }
      assert (hh' :
        (Σ', ϕ) ;;;
        [] ,,, arities_context (sind_bodies mb) ,,, nlctx (sind_params mb)
         |-i pi2_ decl : sSort s
      ).
      { rewrite nil_cat.
        eapply weak_glob_type ; [| eassumption ].
        exact hh.
      }
      assert (hg' : type_glob (Σ', ϕ)).
      { econstructor ; eassumption. }
      pose proof (type_substln hg' hl (Ξ := nlctx (sind_params mb)) hh') as h'.
      simpl in h'.
      erewrite wf_substln_context in h' by apply t.
      rewrite nil_cat in h'. rewrite rev_map_length in h'.
      apply h'.
    + intro e.
      destruct isdecl as [ib [[mb [[d' ?] hn]] hn']]. simpl.
      assert (is' : sdeclared_constructor Σ (ind, i) univs decl).
      { exists ib. split.
        - exists mb. repeat split.
          + unfold sdeclared_minductive in *. cbn in d'.
            rewrite e in d'. exact d'.
          + assumption.
          + assumption.
        - assumption.
      }
      erewrite @paramless_type_of_constructor_cons
        with (isdecl := is') by assumption.
      eapply weak_glob_isType ; [| eassumption ].
      assert (lem : forall Σ Γ A Δ, isType Σ Γ A -> Γ = Δ -> isType Σ Δ A).
      { clear. intros Σ Γ A Δ h eq. destruct eq. assumption. }
      eapply lem.
      * apply IHhg.
      * destruct is' as [ib' [[mb' [[d'' ?] ?]] ?]].
        cbn. f_equal. f_equal.
        clear - d' d'' e.
        unfold sdeclared_minductive in d', d''.
        cbn in d'. rewrite e in d'. rewrite d' in d''.
        inversion d''. subst. reflexivity.
Defined.

Fact substn_nctx_cat :
  forall u n L1 L2,
    substn_nctx u n (L1 ++ L2) =
    (substn_nctx u n L1 ++ substn_nctx u (n + #|L1|) L2).
Proof.
  intros u n L1 L2. revert u n L2.
  induction L1 as [| [nx A] L1 ih ] ; intros u n L2.
  - simpl. f_equal. omega.
  - rewrite substn_nctx_cons.
    simpl. rewrite substn_nctx_cons.
    f_equal. replace (n + S #|L1|)%nat with (S n + #|L1|)%nat by omega.
    apply ih.
Defined.

Corollary subst_nctx_cat :
  forall u L1 L2,
    subst_nctx u (L1 ++ L2) =
    (subst_nctx u L1 ++ substn_nctx u #|L1| L2).
Proof.
  intros u L1 L2.
  refine (substn_nctx_cat _ _ _ _).
Defined.

Fact substn_nctx_length :
  forall {u n L}, #|substn_nctx u n L| = #|L|.
Proof.
  intros u n L. revert u n.
  induction L as [| [nx A] L ih ] ; intros u n.
  - cbn. reflexivity.
  - rewrite substn_nctx_cons. simpl. f_equal. apply ih.
Defined.

Lemma type_spine_cat :
  forall {Σ Γ Δ1 Δ2 Ξ T T' T'' l1 l2},
    type_spine Σ Γ Δ1 (Prods Δ2 T) l1 (Prods Ξ T'') ->
    type_spine Σ Γ Ξ T'' l2 T' ->
    #|Ξ| = #|Δ2| ->
    (type_spine Σ Γ (Δ1 ++ Δ2) T (l1 ++ l2) T').
Proof.
  intros Σ Γ Δ1 Δ2 Ξ T T' T'' l1 l2 h1 h2 e.
  revert T' l2 h2 e. dependent induction h1 ; intros B l2 h2 e.
  - cbn. destruct (Prods_inj H e). subst. assumption.
  - cbn. econstructor.
    + assumption.
    + rewrite subst_nctx_cat.
      eapply IHh1.
      * f_equal. rewrite subst_Prods, app_length. f_equal.
        f_equal. f_equal. omega.
      * assumption.
      * rewrite substn_nctx_length. assumption.
Defined.

Lemma closed_context_lift :
  forall {Σ Δ k},
    wf Σ Δ ->
    lift_context k Δ = Δ.
Proof.
  intros Σ Δ k hw. revert k.
  induction hw ; intro k.
  - cbn. reflexivity.
  - cbn. rewrite IHhw. unfold ssnoc. f_equal.
    eapply closed_above_lift_id.
    + eapply type_ctx_closed_above. eassumption.
    + auto.
Defined.

Lemma wf_cat :
  forall {Σ Γ Δ},
    type_glob Σ ->
    wf Σ Γ ->
    wf Σ Δ ->
    wf Σ (Γ ,,, Δ).
Proof.
  intros Σ Γ Δ hg h1 h2.
  pose (lem := @wf_lift).
  specialize lem with (Γ := []) (Δ := Γ) (Ξ := Δ).
  rewrite !nil_cat in lem.
  specialize (lem _ h2 hg h1).
  erewrite closed_context_lift in lem ; eassumption.
Defined.

Lemma type_spine_lrel :
  forall {Σ L1 L2 L3 T},
    type_spine Σ (nlctx (L1 ++ L2 ++ L3))
               L2 (Prods L3 T)
               (lrel #|L3| #|L2|)
               (Prods L3 T).
Proof.
  intros Σ L1 L2 L3 T. revert L1 L3 T.
  induction L2 as [| [nx A] L2 ih ] ; intros L1 L3 T.
  - cbn. constructor.
  - cbn.
    specialize (ih (L1 ++ [ (nx,A) ]) L3 T).
    econstructor.
    + rewrite nlctx_cat, nlctx_cons, nlctx_cat.
      eapply meta_conv.
      * eapply type_Rel. admit.
      * admit.
    + (* We might have gotten the lemma wrong *)
      admit.
Abort.

Lemma type_indInst :
  forall {Σ ind univs decl isdecl},
    type_glob Σ ->
    let si := decl.(sind_sort) in
    let pars := @indpars (fst Σ) ind univs decl isdecl in
    let indices := decl.(sind_indices) in
    Σ ;;; nlctx (pars ++ indices) |-i indInst isdecl : sSort si.
Proof.
  intros Σ ind univs decl isdecl hg si pars indices.
  unfold indInst.
  relet.
  assert (hw : wf Σ (nlctx (pars ++ indices))).
  { destruct (isArity_ind_type hg isdecl) as [? ?].
    relet. assumption.
  }
  eapply type_Apps.
  - assumption.
  - eapply meta_conv.
    + eapply type_Ind ; eassumption.
    + destruct (isArity_ind_type hg isdecl) as [? ?]. relet. assumption.
  - apply istype_nctx_spec.
    eexists. econstructor.
    eapply wf_cat ; eassumption.
  - eapply type_spine_cat.
    +
Admitted.

Lemma type_elimPty :
  forall {Σ ind univs decl isdecl s},
    type_glob Σ ->
    let pars := @indpars (fst Σ) ind univs decl isdecl in
    let indices := decl.(sind_indices) in
    isType Σ (nlctx pars) (elimPty isdecl s).
Proof.
  intros Σ ind univs decl isdecl s hg pars indices.
  unfold elimPty. relet.
  eapply type_Prods. eapply istype_nctx_spec.
  eexists. econstructor. rewrite nlctx_cat.
  simpl. econstructor.
  - destruct (isArity_ind_type hg isdecl) as [hw ?]. relet.
    rewrite nlctx_cat in hw. assumption.
  - rewrite <- nlctx_cat.
    eapply type_indInst. assumption.
Defined.

(* TODO MOVE *)
Lemma ForallT_forall_nth :
  forall {A} {P : A -> Type} {l},
    (forall n x, nth_error l n = Some x -> P x) ->
    ForallT P l.
Proof.
  intros A P l h.
  induction l.
  - constructor.
  - econstructor.
    + apply (h 0). reflexivity.
    + apply IHl. intros n x e.
      apply (h (S n)). cbn. assumption.
Defined.

(* TODO MOVE *)
Lemma forall_list_nth :
  forall {A B} {l : list A} {f : forall x n, nth_error l n = Some x -> B} {n x},
    nth_error l n = Some x ->
    ∑ e, nth_error (forall_list l f) n = Some (f x n e).
Proof.
  intros A B l. revert B.
  induction l ; intros B f n x e.
  - destruct n ; cbn in e ; discriminate e.
  - destruct n.
    + cbn in e. inversion e. subst.
      cbn. exists eq_refl. reflexivity.
    + specialize IHl with (1 := e) (f := fun x n => f x (S n)).
      destruct IHl as [eq ih].
      simpl. exists eq. apply ih.
Defined.

(* TODO MOVE *)
Lemma meta_isType_conv :
  forall {Σ Γ Δ A},
    isType Σ Γ A ->
    Γ = Δ ->
    isType Σ Δ A.
Proof.
  intros Σ Γ Δ A ? ?.
  subst. assumption.
Defined.

(* TODO MOVE *)
Lemma ForallT_forall_list :
  forall {A B} {l : list A} {f : forall x n, nth_error l n = Some x -> B} {P : B -> Type},
    (forall n x (e : nth_error l n = Some x), P (f x n e)) ->
    ForallT P (forall_list l f).
Proof.
  intros A B l f P h. revert B f P h.
  induction l ; intros B f P h.
  - cbn. constructor.
  - simpl. econstructor.
    + apply h.
    + eapply IHl. intros n x e. apply h.
Defined.

Lemma type_pl_ctors_ty :
  forall {Σ ind univs decl isdecl},
    type_glob Σ ->
    let pars := @indpars (fst Σ) ind univs decl isdecl in
    ForallT (isType Σ (nlctx pars)) (pl_ctors_ty isdecl).
Proof.
  intros Σ ind univs decl isdecl hg pars.
  eapply ForallT_forall_list.
  intros n d e.
  eapply meta_isType_conv.
  - eapply typed_paramless_type_of_constructor.
    assumption.
  - destruct isdecl as [m [[h1 h2] h3]].
    revert pars. rewrite indpars_def. subst. cbn.
    reflexivity.
Defined.

(* TODO MOVE *)
Fact lift_nctx_cat :
  forall n k L1 L2,
    lift_nctx n k (L1 ++ L2) =
    lift_nctx n k L1 ++ lift_nctx n (k + #|L1|) L2.
Proof.
  intros n k L1 L2. revert n k L2.
  induction L1 as [| [nx A] L1 ih ] ; intros n k L2.
  - simpl. f_equal. omega.
  - rewrite lift_nctx_cons. simpl. rewrite lift_nctx_cons.
    f_equal. rewrite ih. f_equal. f_equal. omega.
Defined.

(* TODO MOVE *)
Fact lift_nctx_length :
  forall {L n k}, #|lift_nctx n k L| = #|L|.
Proof.
  intro L. induction L as [| [nx A] L ih ] ; intros n k.
  - cbn. reflexivity.
  - rewrite lift_nctx_cons. simpl. f_equal. apply ih.
Defined.

(* TODO MOVE *)
Fact lift_nctx_nil :
  forall {n k}, lift_nctx n k [] = [].
Proof.
  intros n k. reflexivity.
Defined.

(* TODO MOVE *)
Fact nlctx_nil : nlctx [] = [].
Proof. reflexivity. Defined.

(* TODO MOVE *)
Fact cat_one :
  forall {Γ A}, Γ ,,, [ A ] = Γ ,, A.
Proof.
  reflexivity.
Defined.

(* TODO MOVE *)
Fixpoint liftn_context n k Γ :=
  match Γ with
  | [] => []
  | A :: Γ => lift n (#|Γ| + k) A :: liftn_context n k Γ
  end.

(* TODO MOVE *)
Fact liftn_context_cat :
  forall {Γ Δ n k},
    liftn_context n k (Γ ,,, Δ) =
    liftn_context n k Γ ,,, liftn_context n (#|Γ| + k) Δ.
Proof.
  intros Γ Δ. revert Γ. induction Δ ; intros Γ n k.
  - cbn. reflexivity.
  - cbn. rewrite app_length. f_equal.
    + f_equal. omega.
    + apply IHΔ.
Defined.

(* TODO MOVE *)
Fact liftn_context_O :
  forall {Γ n}, liftn_context n 0 Γ = lift_context n Γ.
Proof.
  intros Γ. induction Γ ; intro n.
  - cbn. reflexivity.
  - cbn. f_equal.
    + f_equal. omega.
    + apply IHΓ.
Defined.

(* TODO MOVE *)
Fact nlctx_lift_nctx :
  forall {L n k},
    nlctx (lift_nctx n k L) = liftn_context n k (nlctx L).
Proof.
  intro L. induction L as [| [nx A] L ih] ; intros n k.
  - cbn. reflexivity.
  - rewrite nlctx_cons, lift_nctx_cons, nlctx_cons.
    rewrite liftn_context_cat. cbn. rewrite ih. reflexivity.
Defined.

Fact nlctx_lift_nctx0 :
  forall {L n},
    nlctx (lift_nctx n 0 L) = lift_context n (nlctx L).
Proof.
  intros L n.
  rewrite <- liftn_context_O.
  apply nlctx_lift_nctx.
Defined.

Lemma type_elimPapp :
  forall {Σ Γ ind univs decl isdecl s l ty},
    type_glob Σ ->
    let pars := @indpars (fst Σ) ind univs decl isdecl in
    isapp ty (sInd ind) l ->
    wf Σ (nlctx (pars) ,, elimPty isdecl s ,,, Γ ,, ty) ->
    isType Σ (nlctx (pars) ,, elimPty isdecl s ,,, Γ ,, ty)
           (elimPapp isdecl s l #|Γ|).
Proof.
  intros Σ Γ ind univs decl isdecl s l ty hg pars happ h.
  unfold elimPapp. relet.
  eexists. eapply type_Apps.
  - assumption.
  - assert (is1 : S #|Γ| < #|nlctx pars,, elimPty isdecl s ,,, Γ,, ty|).
    { simpl. rewrite length_cat. simpl. omega. }
    eapply meta_conv.
    + unshelve econstructor ; assumption.
    + assert (is2 : S #|Γ| - #|Γ,, ty| < #|nlctx pars,, elimPty isdecl s|).
      { simpl. omega. }
      erewrite @safe_nth_ge with (isdecl' := is2) by (cbn ; omega).
      revert is2.
      replace (S #|Γ| - #|Γ,, ty|) with 0 by (cbn ; omega).
      intro is2.
      simpl. unfold elimPty. rewrite lift_Prods, lift_nctx_cat. simpl. f_equal.
      f_equal. rewrite lift_nctx_cons, lift_nctx_nil, lift_nctx_length.
      reflexivity.
  - eapply istype_nctx_spec. eexists. econstructor.
    rewrite nlctx_cat, nlctx_cons, nlctx_nil, cat_nil, cat_one.
    simpl. econstructor.
    + rewrite nlctx_lift_nctx0.
      pose (hh := @wf_lift).
      specialize hh with (Γ := nlctx pars)
                         (Δ := [] ,, elimPty isdecl s ,,, Γ,, ty)
                         (Ξ := nlctx (sind_indices decl)).
      unfold sapp_context, ssnoc in *. simpl in hh.
      rewrite app_length in hh. simpl in hh.
      replace (#|Γ| + 1)%nat with (S #|Γ|) in hh by omega.
      rewrite <- app_assoc in hh. simpl in hh.
      apply hh ; clear hh.
      * destruct (isArity_ind_type hg isdecl) as [hh _].
        rewrite nlctx_cat in hh. apply hh.
      * assumption.
      * assumption.
    + rewrite nlctx_lift_nctx0.
      pose (hh := @type_lift).
      specialize hh with (Γ := nlctx pars)
                         (Δ := [] ,, elimPty isdecl s ,,, Γ,, ty)
                         (Ξ := nlctx (sind_indices decl)).
      unfold sapp_context, ssnoc in *. simpl in hh.
      rewrite app_length in hh. simpl in hh.
      replace (#|Γ| + 1)%nat with (S #|Γ|) in hh by omega.
      rewrite <- app_assoc in hh. simpl in hh.
      rewrite lift_nctx_length. rewrite rev_map_length in hh.
      match goal with
      | |- _ ;;; _ |-i lift ?n ?k _ : ?S =>
        change S with (lift n k S)
      end.
      eapply hh ; clear hh.
      * pose proof @type_indInst as hh. simpl in hh.
        specialize hh with (isdecl := isdecl). relet.
        rewrite nlctx_cat in hh. apply hh.
        assumption.
      * assumption.
      * assumption.
  - (* I still don't know how to tackle type spines. *)
    admit.
Abort.

Lemma istype_type :
  forall {Σ Γ t T},
    type_glob Σ ->
    Σ ;;; Γ |-i t : T ->
    exists s, Σ ;;; Γ |-i T : sSort s.
Proof.
  intros Σ Γ t T hg H.
  induction H.
  - revert n isdecl. induction H ; intros n isdecl.
    + cbn in isdecl. easy.
    + destruct n.
      * cbn.
        exists s. change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01 ; eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- auto with arith.
        -- destruct (IHwf n isdecl') as [s' hh].
           exists s'. change (sSort s') with (lift0 1 (sSort s')).
           (* Take out as a lemma? *)
           assert (eq : forall t, lift0 (S (S n)) t = lift0 1 (lift0 (S n) t)).
           { intro t'. rewrite lift_lift. reflexivity. }
           rewrite eq. clear eq.
           eapply typing_lift01.
           ++ assumption.
           ++ erewrite eq_safe_nth. eassumption.
           ++ eassumption.
  - exists (succ_sort (succ_sort s)). now apply type_Sort.
  - exists (succ_sort (max_sort s1 s2)). apply type_Sort. apply (typing_wf H).
  - exists (max_sort s1 s2). apply type_Prod ; assumption.
  - exists s2. change (sSort s2) with ((sSort s2){ 0 := u }).
    eapply typing_subst ; eassumption.
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. now apply type_Eq.
  - exists s2.
    change (sSort s2) with ((sSort s2){1 := v}{0 := p}).
    eapply typing_subst2.
    + assumption.
    + eassumption.
    + assumption.
    + cbn. rewrite !lift_subst, lift00.
      assumption.
  - eexists. eassumption.
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. apply type_Eq ; assumption.
  - exists s. apply type_Heq ; assumption.
  - exists s. apply type_Heq ; assumption.
  - exists s. apply type_Heq ; assumption.
  - exists s. apply type_Heq. all: try assumption.
    eapply type_Transport ; eassumption.
  - exists (succ_sort (max_sort s z)).
    apply type_Heq.
    + eapply type_Sort. apply (typing_wf H).
    + eapply type_Sort. apply (typing_wf H).
    + apply type_Prod ; assumption.
    + apply type_Prod ; assumption.
  - exists (max_sort s z). apply type_Heq.
    + apply type_Prod ; assumption.
    + apply type_Prod ; assumption.
    + eapply type_Lambda ; eassumption.
    + eapply type_Lambda ; eassumption.
  - exists z. apply type_Heq.
    + change (sSort z) with ((sSort z){ 0 := v1 }).
      eapply typing_subst ; eassumption.
    + change (sSort z) with ((sSort z){ 0 := v2 }).
      eapply typing_subst ; eassumption.
    + eapply type_App ; eassumption.
    + eapply type_App ; eassumption.
  - exists (succ_sort s). apply type_Heq.
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Eq ; assumption.
    + apply type_Eq ; assumption.
  - exists s. apply type_Heq.
    + apply type_Eq ; assumption.
    + apply type_Eq ; assumption.
    + eapply type_Refl ; eassumption.
    + eapply type_Refl ; eassumption.
  - exists s. apply type_Heq ; assumption.
  - exists (succ_sort s). eapply type_Eq ; try assumption.
    apply type_Sort. apply (typing_wf H).
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. assumption.
  - exists s. assumption.
  - exists s. apply type_Heq ; try assumption.
    + eapply type_ProjT1 ; eassumption.
    + eapply @type_ProjT2 with (A1 := A1) ; eassumption.
  - destruct (typed_ind_type hg isdecl) as [s h].
    exists s.
    change (sSort s) with (lift #|Γ| #|@nil sterm| (sSort s)).
    replace (sind_type decl)
      with (lift #|Γ| #|@nil sterm| (sind_type decl))
      by (erewrite lift_ind_type by eassumption ; reflexivity).
    eapply meta_ctx_conv.
    + eapply @type_lift with (Γ := []) (Ξ := []) (Δ := Γ).
      * assumption.
      * assumption.
      * rewrite nil_cat. assumption.
    + cbn. apply nil_cat.
  - destruct (typed_type_of_constructor hg isdecl) as [s h].
    exists s. change (sSort s) with (lift #|Γ| #|@nil sterm| (sSort s)).
    set (ty := stype_of_constructor (fst Σ) (ind, i) univs decl isdecl) in *.
    replace ty with (lift #|Γ| #|@nil sterm| ty)
      by (erewrite lift_type_of_constructor by eassumption ; reflexivity).
    eapply meta_ctx_conv.
    + eapply @type_lift with (Γ := []) (Ξ := []) (Δ := Γ).
      * assumption.
      * assumption.
      * rewrite nil_cat. assumption.
    + cbn. apply nil_cat.
  - exists s. assumption.
Defined.
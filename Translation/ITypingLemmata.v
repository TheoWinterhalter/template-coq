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
    isType Σ (Γ,,, nlctx Δ) T ->
    isType Σ Γ (Prods Δ T).
Proof.
  intros Σ Γ Δ T h. revert Γ T h.
  induction Δ as [| [nx A] Δ ih ] ; intros Γ T h.
  - cbn in *. assumption.
  - simpl in *. eapply ih.
    destruct h as [s h].
    pose proof (typing_wf h) as hw.
    dependent destruction hw.
    eexists. eapply type_Prod.
    + eassumption.
    + eassumption.
Defined.

Lemma type_Lams :
  forall {Σ Γ Δ t T},
    Σ ;;; Γ,,, nlctx Δ |-i t : T ->
    isType Σ (Γ,,, nlctx Δ) T ->
    Σ ;;; Γ |-i Lams Δ T t : Prods Δ T.
Proof.
  intros Σ Γ Δ t T h1 h2. revert Γ t T h1 h2.
  induction Δ as [| [nx A] Δ ih] ; intros Γ t T h1 h2.
  - cbn in *. assumption.
  - simpl in *. eapply ih.
    + pose proof (typing_wf h1) as hw.
      dependent destruction hw.
      destruct h2 as [s' h2].
      eapply type_Lambda ; eassumption.
    + pose proof (typing_wf h1) as hw.
      dependent destruction hw.
      destruct h2 as [s' h2].
      eexists. econstructor ; eassumption.
Defined.

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

Fact typed_ind_type' :
  forall {Σ : sglobal_context} {decl'},
    type_inductive Σ decl'.(sind_params) (sind_bodies decl') ->
    forall {n decl},
      nth_error (sind_bodies decl') n = Some decl ->
      isType Σ [] (sind_type decl).
Proof.
  intros Σ decl' [hx hind].
  induction hind.
  - intros n decl h.
    destruct n ; cbn in h ; inversion h.
  - intros n decl h.
    destruct n.
    + cbn in h. inversion h as [ e ]. subst. clear h.
      cbn. destruct i as [i _].
      assumption.
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

Fact typed_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      isType Σ [] (sind_type decl).
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
      destruct (typed_ind_type' t h3) as [s h].
      exists s. eapply weak_glob_type ; assumption.
    + intro e. rewrite e in h1.
      destruct (IHhg ind decl univs) as [s h].
      * exists decl'. repeat split ; eassumption.
      * exists s. eapply weak_glob_type ; assumption.
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
      assumption.
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

Fact rev_cons :
  forall {A} {l} {a : A},
    rev (a :: l) = (rev l ++ [a])%list.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [a]). rewrite IHl.
      change (a :: acc) with ([a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_map_cons :
  forall {A B} {f : A -> B} {l} {a : A},
    rev_map f (a :: l) = (rev_map f l ++ [f a])%list.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [f a]). rewrite IHl.
      change (f a :: acc) with ([f a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_length :
  forall {A} {l : list A},
    #|rev l| = #|l|.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- context [ #|?faux _ _| ] => set (aux := faux)
  end.
  assert (h : forall l acc, #|aux l acc| = (#|acc| + #|l|)%nat).
  { intro l. induction l ; intro acc.
    - cbn. omega.
    - cbn. rewrite IHl. cbn. omega.
  }
  intro l. apply h.
Defined.

Fact rev_map_length :
  forall {A B} {f : A -> B} {l : list A},
    #|rev_map f l| = #|l|.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- context [ #|?faux _ _| ] => set (aux := faux)
  end.
  assert (h : forall l acc, #|aux l acc| = (#|acc| + #|l|)%nat).
  { intro l. induction l ; intro acc.
    - cbn. omega.
    - cbn. rewrite IHl. cbn. omega.
  }
  intro l. apply h.
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

Lemma type_Apps :
  forall {Σ Γ Δ f l T},
    type_glob Σ ->
    Σ ;;; Γ |-i f : Prods Δ T ->
    typed_list Σ Γ l (nlctx Δ) ->
    isType Σ (Γ,,, nlctx Δ) T ->
    Σ ;;; Γ |-i Apps f Δ T l : substl l T.
Proof.
  intros Σ Γ Δ f l T hg. revert Γ f l T .
  induction Δ as [| [nx A] Δ ih] ; intros Γ f l T hf hl hT.
  - cbn in *. dependent destruction hl. cbn. assumption.
  - dependent destruction hl. simpl in *.
    rename l0 into l, A0 into t.
    rewrite <- substl1_subst0.
    destruct hT as [s hT].
    pose proof (typing_wf hT) as hw.
    dependent destruction hw.
    rename A0 into A, s0 into s'.
    eapply type_App.
    + erewrite <- substl_sort.
      eapply type_substl ; eassumption.
    + erewrite <- substln_sort.
      pose proof (type_substln hg hl (Ξ := [ A ]) hT) as hh.
      simpl in hh. rewrite substln_context_cons in hh. simpl in hh.
      rewrite <- substl_substln0, substln_context_nil in hh.
      apply hh.
    + rewrite <- substl_Prod.
      eapply ih ; try eassumption.
      eexists. econstructor ; eassumption.
    + eapply type_substl ; eassumption.
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
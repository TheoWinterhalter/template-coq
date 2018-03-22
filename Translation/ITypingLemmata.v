From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SInduction SLiftSubst SCommon ITyping.

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

Lemma meta_eqctx_conv :
  forall {Σ Γ Δ t1 t2 A},
    Σ ;;; Γ |-i t1 = t2 : A ->
    Γ = Δ ->
    Σ ;;; Δ |-i t1 = t2 : A.
Proof.
  intros Σ Γ Δ t1 t2 A h e.
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

Lemma meta_eqconv :
  forall {Σ Γ t t' A B},
    Σ ;;; Γ |-i t = t' : A ->
    A = B ->
    Σ ;;; Γ |-i t = t' : B.
Proof.
  intros Σ Γ t t' A B h e.
  rewrite <- e. exact h.
Defined.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

Ltac erewrite_assumption :=
  match goal with
  | H : _ = _ |- _ =>
    erewrite H by omega
  end.

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := apply cheating.

Fact type_ctx_closed_above :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    closed_above #|Γ| t = true.
Proof.
  intros Σ Γ t T h.
  dependent induction h.
  all: try (cbn in * ; repeat erewrite_assumption ; reflexivity).
  - unfold closed_above. case_eq (n <? #|Γ|) ; intro e ; bprop e ; try omega.
    reflexivity.
  - cbn. repeat erewrite_assumption.
    simpl. cheat. (* We need a stronger induction principle. *)
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
    type_inductive Σ (sind_bodies decl') ->
    forall {n decl},
      nth_error (sind_bodies decl') n = Some decl ->
      isType Σ [] (sind_type decl).
Proof.
  intros Σ decl' hind. unfold type_inductive in hind.
  induction hind.
  - intros n decl h.
    destruct n ; cbn in h ; inversion h.
  - intros n decl h.
    destruct n.
    + cbn in h. inversion h as [ e ]. subst. clear h.
      cbn. unfold isArity in i.
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

Ltac contrad :=
  match goal with
  | |- context [False_rect _ ?p] => exfalso ; apply p
  end.

Lemma stype_of_constructor_eq :
  forall {Σ id' decl' ind i univs decl}
    {isdecl : sdeclared_constructor ((SInductiveDecl id' decl') :: Σ) (ind, i) univs decl},
    ident_eq (inductive_mind ind) id' = true ->
    let '(id, trm, args) := decl in
    stype_of_constructor ((SInductiveDecl id' decl') :: Σ) (ind, i) univs decl isdecl =
    substl (sinds (inductive_mind ind) decl'.(sind_bodies)) trm.
Proof.
  intros Σ id' decl' ind i univs decl isdecl h.
  funelim (stype_of_constructor (SInductiveDecl id' decl' :: Σ) (ind, i) univs decl isdecl)
  ; try contrad.
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
  ; try contrad.
  funelim (stype_of_constructor Σ0 (ind, i) univs decl isdecl) ; try contrad.
  rewrite <- eq in H. inversion H. subst. reflexivity.
Defined.

Fixpoint weak_glob_type {Σ ϕ Γ t A} (h : (Σ,ϕ) ;;; Γ |-i t : A) :
  forall {d},
    fresh_global (sglobal_decl_ident d) Σ ->
    (d::Σ, ϕ) ;;; Γ |-i t : A

with weak_glob_eq {Σ ϕ Γ t1 t2 A} (h : (Σ,ϕ) ;;; Γ |-i t1 = t2 : A) :
  forall {d},
    fresh_global (sglobal_decl_ident d) Σ ->
    (d::Σ, ϕ) ;;; Γ |-i t1 = t2 : A

with weak_glob_wf {Σ ϕ Γ} (h : wf (Σ,ϕ) Γ) :
  forall {d},
    fresh_global (sglobal_decl_ident d) Σ ->
    wf (d::Σ, ϕ) Γ.
Proof.
  (* weak_glob_type *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                try apply weak_glob_eq ;
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
      - (* destruct isdecl' as [d' [[? ?] ?]] eqn:eq. *)
        (* eapply type_Case. *)
        (* + cbn in *. unfold sdeclared_minductive in *. *)
        (*   cbn. erewrite ident_neq_fresh by eassumption. *)
        (*   eassumption. *)
        (* + cbn. exists d'. repeat split. *)
        (*   * cbn in *. unfold sdeclared_minductive in *. *)
        (*     cbn. erewrite ident_neq_fresh by eassumption. *)
        (*     eassumption. *)
        (*   * eassumption. *)
        (* +  *)
        (* eapply type_Case. *)
        (* + cbn in *. unfold sdeclared_minductive in *. *)
        (*   cbn. erewrite ident_neq_fresh by eassumption. *)
        (*   eassumption. *)
        (* + cbn. exists decl. repeat split. *)
        (*   * cbn in *. unfold sdeclared_minductive in *. *)
        (*     cbn. erewrite ident_neq_fresh by eassumption. *)
        (*     eassumption. *)
        (*   * unfold sdeclared_minductive in *. cbn in *. *)
        (* + *)
        cheat.
    }

  (* weak_glob_eq *)
  - { dependent destruction h ; intros d fd.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                try apply weak_glob_eq ;
                eassumption
               ).
      - eapply cong_HeqTrans with (B := B) (b := b).
        all: try apply weak_glob_eq ; try apply weak_glob_type ; eassumption.
      - eapply cong_ProjT2 with (A1 := A1).
        all: try apply weak_glob_eq ; try apply weak_glob_type ; eassumption.
      - cheat.
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
    type_inductive Σ (sind_bodies decl') ->
    forall {n decl},
      nth_error (sind_bodies decl') n = Some decl ->
      Xcomp (sind_type decl).
Proof.
  intros Σ decl' hind. unfold type_inductive in hind.
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
  forall {Σ : sglobal_context} {inds Γ},
    type_inddecls Σ [] Γ inds ->
    forall {n decl},
      nth_error inds n = Some decl ->
      type_constructors Σ Γ (sind_ctors decl).
Proof.
  intros Σ inds Γ hind. induction hind.
  - intros n decl h.
    destruct n ; cbn in h ; inversion h.
  - intros n decl h.
    destruct n.
    + cbn in h. inversion h as [ e ]. subst. clear h.
      simpl. assumption.
    + cbn in h. eapply IHhind. eassumption.
Defined.

Fact type_ind_type_constr :
  forall {Σ : sglobal_context} {inds},
    type_inductive Σ inds ->
    forall {n decl},
      nth_error inds n = Some decl ->
      type_constructors Σ (arities_context inds) (sind_ctors decl).
Proof.
  intros Σ inds hind n decl h.
  unfold type_inductive in hind.
  eapply type_inddecls_constr ; eassumption.
Defined.

Fact typed_type_constructors :
  forall {Σ : sglobal_context} {Γ l},
    type_constructors Σ Γ l ->
    forall {i decl},
      nth_error l i = Some decl ->
      let '(_, t, _) := decl in
      isType Σ Γ t.
Proof.
  intros Σ Γ l htc. induction htc ; intros m decl hm.
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
    [ svass (nNamed (sind_name a)) (sind_type a) ] ,,, arities_context l.
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
  forall {Σ id l},
      type_inductive Σ l ->
      closed_list (sinds id l).
Proof.
  intros Σ id l ti.
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
  - cbn. contrad.
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
  forall {Σ id l},
      type_inductive Σ l ->
      xcomp_list (sinds id l).
Proof.
  intros Σ id l ti.
  unfold type_inductive in ti. induction ti.
  - cbn. constructor.
  - rewrite sinds_cons. econstructor.
    + constructor.
    + assumption.
Defined.

Fact xcomp_type_constructors :
  forall {Σ : sglobal_context} {Γ l},
    type_constructors Σ Γ l ->
    forall {i decl},
      nth_error l i = Some decl ->
      let '(_, t, _) := decl in
      Xcomp t.
Proof.
  intros Σ Γ l htc. induction htc ; intros m decl hm.
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
  - cbn. contrad.
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
          |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A,
      cong_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t1 t2 A : sterm),
          Σ;;; Γ ,,, Ξ |-i t1 = t2 : A ->
          type_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-i lift #|Δ| #|Ξ| t1 = lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A
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
    | _ ;;; ?Γ' ,,, ?Ξ' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_lift or cong_lift"
  end.

Ltac eih :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i lift _ _ ?t : _ => ih h
  | h : _ ;;; _ |-i ?t = _ : _ |- _ ;;; _ |-i lift _ _ ?t = _ : _ =>
    ih h
  | _ => fail "Not handled by eih"
  end.

Fixpoint type_lift {Σ Γ Δ Ξ t A} (h : Σ ;;; Γ ,,, Ξ |-i t : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A

with cong_lift {Σ Γ Δ Ξ t1 t2 A} (h : Σ ;;; Γ ,,, Ξ |-i t1 = t2 : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-i lift #|Δ| #|Ξ| t1
  = lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A

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
        + instantiate (1 := ne). instantiate (1 := nx). cbn. unfold ssnoc.
          rewrite !lift_decl_svass. cbn.
          f_equal. f_equal. f_equal.
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
      - cheat.
      - eapply type_conv ; eih.
    }

  (* cong_lift *)
  - { intros hg hwf. dependent destruction h.
      - apply eq_reflexivity. apply type_lift ; assumption.
      - apply eq_symmetry. eapply cong_lift ; assumption.
      - eapply eq_transitivity ; eih.
      - change (lift #|Δ| #|Ξ| (t {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (t { 0 := u })).
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite 2!substP1. cbn.
        eapply eq_beta ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by omega.
        rewrite substP1. cbn.
        eapply eq_JRefl ; eih.
        + cbn. rewrite lift_decl_svass. unfold ssnoc.
          instantiate (1 := nx). instantiate (1 := ne). cbn.
          f_equal. f_equal. f_equal.
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
      - cbn. eapply eq_TransportRefl ; eih.
      - eapply eq_conv ; eih.
      - cbn. eapply cong_Prod ; eih.
      - cbn. eapply cong_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
        rewrite substP1.
        eapply cong_App ; eih.
      - cbn. eapply cong_Eq ; eih.
      - cbn. eapply cong_Refl ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by omega.
        rewrite substP1. cbn.
        eapply cong_J ; eih.
        + cbn. rewrite lift_decl_svass. unfold ssnoc.
          instantiate (1 := nx). instantiate (1 := ne). cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by omega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by omega.
          change (sRefl (lift #|Δ| #|Ξ| A1) (lift #|Δ| #|Ξ| u1))
            with (lift #|Δ| #|Ξ| (sRefl A1 u1)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply cong_Transport ; eih.
      - cbn. eapply cong_Heq ; eih.
      - cbn. eapply cong_Pack ; eih.
      - cbn. eapply cong_HeqToEq ; eih.
      - cbn. eapply cong_HeqRefl ; eih.
      - cbn. eapply cong_HeqSym ; eih.
      - cbn. eapply cong_HeqTrans with (B := lift #|Δ| #|Ξ| B) (b := lift #|Δ| #|Ξ| b) ; eih.
      - cbn. eapply cong_HeqTransport ; eih.
      - cbn. eapply cong_CongProd ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply cong_CongLambda ; eih.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := v1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := v1 })).
        rewrite substP1.
        change (lift #|Δ| #|Ξ| (B2 {0 := v2}))
          with (lift #|Δ| (0 + #|Ξ|) (B2 { 0 := v2 })).
        rewrite substP1.
        eapply cong_CongApp ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply cong_CongEq ; eih.
      - cbn. eapply cong_CongRefl ; eih.
      - cbn. eapply cong_EqToHeq ; eih.
      - cbn. eapply cong_HeqTypeEq ; eih.
      - cbn. eapply cong_ProjT1 with (A2 := lift #|Δ| #|Ξ| A2) ; eih.
      - cbn. eapply cong_ProjT2 with (A1 := lift #|Δ| #|Ξ| A1) ; eih.
      - cbn. eapply cong_ProjTe ; eih.
      - cheat.
      - cbn. eapply eq_HeqToEqRefl ; eih.
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
  forall {Σ Γ t A x B s},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A x B s hg ht hB.
  apply (@type_lift _ _ [ svass x B ] nil _ _ ht hg).
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

Corollary typing_lift02 :
  forall {Σ Γ t A x B s y C s'},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i C : sSort s' ->
    Σ ;;; Γ ,, svass x B ,, svass y C |-i lift0 2 t : lift0 2 A.
Proof.
  intros Σ Γ t A x B s y C s' hg ht hB hC.
  assert (eq : forall t, lift0 2 t = lift0 1 (lift0 1 t)).
  { intro u. rewrite lift_lift. reflexivity. }
  rewrite !eq. eapply typing_lift01.
  - assumption.
  - eapply typing_lift01  ; eassumption.
  - eassumption.
Defined.

Corollary cong_lift01 :
  forall {Σ Γ t1 t2 A x B s},
    type_glob Σ ->
    Σ ;;; Γ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i lift0 1 t1 = lift0 1 t2 : lift0 1 A.
Proof.
  intros Σ Γ t1 t2 A x B s hg H H0.
  apply @cong_lift with (Δ := [ svass x B ]) (Ξ := nil).
  - cbn. assumption.
  - assumption.
  - econstructor.
    + eapply typing_wf. eassumption.
    + eassumption.
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
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A : sterm) (nx : name)
          (B u : sterm),
          Σ;;; Γ,, svass nx B ,,, Δ |-i t : A ->
          type_glob Σ ->
          Σ;;; Γ |-i u : B -> Σ;;; Γ ,,, subst_context u Δ |-i
          t {#|Δ| := u} : A {#|Δ| := u},
     cong_subst :
       forall (Σ : sglobal_context) (Γ Δ : scontext) (t1 t2 A : sterm) (nx : name)
         (B u : sterm),
         Σ;;; Γ,, svass nx B ,,, Δ |-i t1 = t2 : A ->
         type_glob Σ ->
         Σ;;; Γ |-i u : B -> Σ;;; Γ ,,, subst_context u Δ |-i
         t1 {#|Δ| := u} = t2 {#|Δ| := u} : A {#|Δ| := u}
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,, svass ?nx' ?B' ,,, ?Δ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,, svass ?nx' ?B' ,,, ?Δ' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d',, ?d'' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "cannot find type_subst, cong_subst"
  end.

Ltac esh :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i ?t{ _ := _ } : _ => sh h
  | h : _ ;;; _ |-i ?t = _ : _ |- _ ;;; _ |-i ?t{ _ := _ } = _ : _ =>
    sh h
  | _ => fail "not handled by esh"
  end.

Fixpoint type_subst {Σ Γ Δ t A nx B u}
  (h : Σ ;;; Γ ,, svass nx B ,,, Δ |-i t : A) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-i t{ #|Δ| := u } : A{ #|Δ| := u }

with cong_subst {Σ Γ Δ t1 t2 A nx B u}
  (h : Σ ;;; Γ ,, svass nx B ,,, Δ |-i t1 = t2 : A) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-i t1{ #|Δ| := u }
  = t2{ #|Δ| := u } : A{ #|Δ| := u }

with wf_subst {Σ Γ Δ nx B u}
  (h : wf Σ (Γ ,, svass nx B ,,, Δ)) {struct h} :
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
          rewrite H. intro ge'.
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
            f_equal. f_equal. eapply safe_nth_cong_irr.
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
        + instantiate (1 := ne). instantiate (1 := nx0). cbn. unfold ssnoc.
          rewrite !subst_decl_svass. cbn.
          f_equal. f_equal. f_equal.
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
      - cheat.
      - cbn. eapply type_conv ; esh.
    }

  (* cong_subst *)
  - { intros hg hu.
      dependent destruction h.
      - constructor. esh.
      - constructor. esh.
      - eapply eq_transitivity ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply eq_beta ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
        rewrite substP4.
        eapply eq_JRefl ; esh.
        + instantiate (1 := ne). instantiate (1 := nx0). cbn. unfold ssnoc.
          rewrite !subst_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
          change (sRefl (A0 {0 + #|Δ| := u}) (u0 {#|Δ| := u}))
            with ((sRefl A0 u0){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply eq_TransportRefl ; esh.
      - eapply eq_conv ; esh.
      - cbn. eapply cong_Prod ; esh.
      - cbn. eapply cong_Lambda ; esh.
      - cbn. change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply cong_App ; esh.
      - cbn. eapply cong_Eq ; esh.
      - cbn. eapply cong_Refl ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
        rewrite substP4.
        eapply cong_J ; esh.
        + instantiate (1 := ne). instantiate (1 := nx0). cbn. unfold ssnoc.
          rewrite !subst_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
          change (sRefl (A1 {0 + #|Δ| := u}) (u1 {0 + #|Δ| := u}))
            with ((sRefl A1 u1){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply cong_Transport ; esh.
      - cbn. eapply cong_Heq ; esh.
      - cbn. eapply cong_Pack ; esh.
      - cbn. eapply cong_HeqToEq ; esh.
      - cbn. eapply cong_HeqRefl ; esh.
      - cbn. eapply cong_HeqSym ; esh.
      - cbn. eapply cong_HeqTrans with (B := B0{ #|Δ| := u }) (b := b{ #|Δ| := u }) ; esh.
      - cbn. eapply cong_HeqTransport ; esh.
      - cbn. eapply cong_CongProd ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply cong_CongLambda ; esh.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
      - cbn. change #|Δ| with (0 + #|Δ|)%nat.
        rewrite !substP4. cbn.
        eapply cong_CongApp ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply cong_CongEq ; esh.
      - cbn. eapply cong_CongRefl ; esh.
      - cbn. eapply cong_EqToHeq ; esh.
      - cbn. eapply cong_HeqTypeEq ; esh.
      - cbn. eapply cong_ProjT1 with (A2 := A2{ #|Δ| := u }) ; esh.
      - cbn. eapply cong_ProjT2 with (A1 := A1{ #|Δ| := u }) ; esh.
      - cbn. eapply cong_ProjTe ; esh.
      - cheat.
      - cbn. eapply eq_HeqToEqRefl ; esh.
    }

  (* wf_subst *)
  - { intros hg hu.
      destruct Δ.
      - cbn. dependent destruction h. assumption.
      - dependent destruction h. cbn. rewrite subst_decl_svass. econstructor.
        + eapply wf_subst ; eassumption.
        + esh.
    }

  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; omega.
Defined.

Corollary typing_subst :
  forall {Σ Γ t A B u n},
    type_glob Σ ->
    Σ ;;; Γ ,, svass n A |-i t : B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i t{ 0 := u } : B{ 0 := u }.
Proof.
  intros Σ Γ t A B u n hg ht hu.
  eapply @type_subst with (Δ := []) ; eassumption.
Defined.

Corollary typing_subst2 :
  forall {Σ Γ t A B C na nb u v},
    type_glob Σ ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t : C ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B{ 0 := u } ->
    Σ ;;; Γ |-i t{ 1 := u }{ 0 := v } : C{ 1 := u }{ 0 := v }.
Proof.
  intros Σ Γ t A B C na nb u v hg ht hu hv.
  eapply @type_subst with (Δ := []).
  - eapply @type_subst with (Δ := [ svass nb B ]).
    + exact ht.
    + assumption.
    + assumption.
  - assumption.
  - cbn. assumption.
Defined.

Inductive typed_list Σ Γ : list sterm -> scontext -> Type :=
| typed_list_nil : typed_list Σ Γ [] []
| typed_list_cons A l Δ nA T :
    typed_list Σ Γ l Δ ->
    Σ ;;; Γ ,,, Δ |-i A : T ->
    typed_list Σ Γ (A :: l) (Δ ,, svass nA T).

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

Fact skipn_all :
  forall {A} {l : list A},
    skipn #|l| l = [].
Proof.
  intros A l. induction l.
  - cbn. reflexivity.
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

Fact skipn_length :
  forall {A} {l : list A} {n},
    #|skipn n l| = #|l| - n.
Proof.
  intros A. induction l ; intro n.
  - cbn. destruct n ; reflexivity.
  - destruct n.
    + cbn. reflexivity.
    + cbn. apply IHl.
Defined.

Fact skipn_reconstruct :
  forall {A} {l : list A} {n a},
    nth_error l n = Some a ->
    skipn n l = a :: skipn (S n) l.
Proof.
  intros A l.
  induction l ; intros n x hn.
  - destruct n ; cbn in hn ; inversion hn.
  - cbn. destruct n.
    + cbn. cbn in hn. inversion hn. reflexivity.
    + apply IHl. now inversion hn.
Defined.

Fact firstn_reconstruct :
  forall {A} {l : list A} {n a},
    nth_error l n = Some a ->
    firstn (S n) l = (firstn n l ++ [a])%list.
Proof.
  intros A l.
  induction l ; intros n x hn.
  - destruct n ; cbn in hn ; inversion hn.
  - cbn. destruct n.
    + cbn. cbn in hn. inversion hn. reflexivity.
    + inversion hn as [e].
      erewrite IHl by exact e. cbn. reflexivity.
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

Definition lastn n {A} (l : list A) :=
  skipn (#|l| - n) l.

Fact lastn_O :
  forall {A} {l : list A}, lastn 0 l = [].
Proof.
  intros A l. unfold lastn.
  replace (#|l| - 0) with #|l| by omega.
  apply skipn_all.
Defined.

Fact lastn_all :
  forall {A} {l : list A},
    lastn #|l| l = l.
Proof.
  intros A l. unfold lastn.
  replace (#|l| - #|l|) with 0 by omega.
  reflexivity.
Defined.

Fact lastn_all2 :
  forall {A} {n} {l : list A},
    #|l| <= n ->
    lastn n l = l.
Proof.
  intros A n l h.
  unfold lastn.
  replace (#|l| - n) with 0 by omega.
  reflexivity.
Defined.

Fact lastn_reconstruct :
  forall {A} {l : list A} {n a},
    nth_error l (#|l| - S n) = Some a ->
    n < #|l| ->
    lastn (S n) l = a :: lastn n l.
Proof.
  intros A l n a hn h.
  unfold lastn.
  erewrite skipn_reconstruct.
  - f_equal. f_equal. omega.
  - assumption.
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
        assert (hn2 : nth_error ac (#|ac| - S n) =
                      Some (svass (nNamed (sind_name a)) (sind_type a))).
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
              change (sSort s) with (lift #|l2'| #|@nil scontext_decl| (sSort s)).
              replace (sind_type a)
                with (lift #|l2'| #|@nil scontext_decl| (sind_type a))
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
  - cbn. contrad.
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

Lemma cong_substs :
  forall {Σ Γ Δ t A nx B},
  Σ ;;; Γ ,, svass nx B ,,, Δ |-i t : A ->
  type_glob Σ ->
  forall {u1 u2},
    Σ ;;; Γ |-i u1 = u2 : B ->
    Σ ;;; Γ |-i u1 : B ->
    Σ ;;; Γ ,,, subst_context u1 Δ
    |-i t{ #|Δ| := u1 }
     = t{ #|Δ| := u2 } : A{ #|Δ| := u1 }.
Proof.
  intros Σ Γ Δ t A nx B ht hg.
  dependent induction ht ; intros uu1 uu2 huu huu1.
  - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
    + assert (h : n >= #|Δ|) by omega.
      rewrite safe_nth_ge' with (h0 := h).
      set (ge := ge_sub isdecl h).
      rewrite substP3 by omega.
      generalize ge.
      replace (n - #|Δ|) with 0 by omega.
      intro ge'. cbn.
      subst.
      replace #|Δ| with #|subst_context uu1 Δ|
        by (now rewrite subst_context_length).
      eapply @cong_lift with (Ξ := []) (Δ := subst_context uu1 Δ).
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
      eapply meta_eqconv.
      * eapply eq_reflexivity. eapply type_Rel. eapply wf_subst ; eassumption.
      * erewrite safe_nth_ge'.
        f_equal. f_equal. eapply safe_nth_cong_irr.
        rewrite subst_context_length. reflexivity.
    + assert (h : n < #|Δ|) by omega.
      rewrite @safe_nth_lt with (isdecl' := h).
      match goal with
      | |- _ ;;; _ |-i _ = _ : ?t{?d := ?u} =>
        replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
          by (f_equal ; omega)
      end.
      rewrite substP2 by omega.
      eapply meta_eqconv.
      * eapply eq_reflexivity. eapply type_Rel.
        eapply wf_subst ; eassumption.
      * f_equal.
        erewrite safe_nth_lt.
        eapply safe_nth_subst_context.
  - cbn. apply eq_reflexivity. apply type_Sort.
    eapply wf_subst ; eassumption.
  - cbn. eapply cong_Prod.
    + now apply IHht1.
    + specialize (IHht2 Γ0 (Δ ,, svass n t) b (sSort s2) nx B eq_refl).
      apply IHht2 ; assumption.
  - cbn. eapply cong_Lambda.
    + apply IHht1 ; eassumption.
    + eapply IHht2 with (Δ0 := Δ ,, svass n t) (A := sSort s2)
      ; [ reflexivity | eassumption .. ].
    + eapply IHht3 with (Δ0 := Δ ,, svass n t)
      ; [ reflexivity | eassumption .. ].
  - cbn. change #|Δ| with (0 + #|Δ|)%nat.
    rewrite substP4. cbn.
    eapply cong_App.
    + apply IHht1 ; eassumption.
    + eapply IHht2 with (Δ0 := Δ ,, svass n A) (A0 := sSort s2)
      ; [ reflexivity | eassumption .. ].
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_Eq.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply cong_Refl.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
  - cbn. change #|Δ| with (0 + #|Δ|)%nat.
    rewrite substP4.
    replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
    rewrite substP4.
    eapply cong_J.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + eapply meta_eqctx_conv.
      * eapply IHht4
          with (Δ0 := (Δ ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)))
               (A0 := sSort s2)
        ; [ reflexivity | eassumption .. ].
      * instantiate (1 := ne). instantiate (1 := nx). cbn. unfold ssnoc.
        rewrite !subst_decl_svass. cbn. f_equal.
        f_equal. f_equal.
        -- replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
           apply substP2. omega.
        -- replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
           apply substP2. omega.
    + apply IHht5 ; eassumption.
    + eapply meta_eqconv.
      * apply IHht6 ; eassumption.
      * replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
        rewrite <- substP4.
        replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
        change (sRefl (A {0 + #|Δ| := uu1}) (u {0 + #|Δ| := uu1}))
          with ((sRefl A u){ 0 + #|Δ| := uu1}).
        rewrite <- substP4. reflexivity.
  - cbn. eapply cong_Transport.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_Heq.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_HeqToEq.
    + apply IHht1 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_HeqRefl.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
  - cbn. eapply cong_HeqSym.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + apply IHht5 ; eassumption.
  - cbn. eapply cong_HeqTrans with (B := B{#|Δ| := uu1}).
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + apply IHht7 ; eassumption.
    + apply IHht8 ; eassumption.
  - cbn. eapply cong_HeqTransport.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_CongProd.
    + apply IHht1 ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht2 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply meta_eqctx_conv.
      * eapply IHht5 with (Δ0 := Δ,, svass nx A1) (A := sSort z)
        ; [ reflexivity | eassumption .. ].
      * cbn. rewrite subst_decl_svass. reflexivity.
    + eapply meta_eqctx_conv.
      * eapply IHht6 with (Δ0 := Δ,, svass ny A2) (A := sSort z)
        ; [ reflexivity | eassumption .. ].
      * cbn. rewrite subst_decl_svass. reflexivity.
  - cbn. eapply cong_CongLambda.
    + apply IHht1 ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht2 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + eapply meta_eqconv.
      * eapply IHht3 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht6 with (Δ0 := Δ,, svass nx A1)
        ; [ reflexivity | eassumption .. ].
      * cbn. reflexivity.
    + eapply meta_eqconv.
      * eapply IHht7 with (Δ0 := Δ,, svass ny A2)
        ; [ reflexivity | eassumption .. ].
      * reflexivity.
    + eapply IHht8 with (Δ0 := Δ,, svass nx A1)
      ; [ reflexivity | eassumption .. ].
    + eapply IHht9 with (Δ0 := Δ,, svass ny A2)
      ; [ reflexivity | eassumption .. ].
  - cbn. change #|Δ| with (0 + #|Δ|)%nat.
    rewrite 2!substP4. cbn.
    eapply cong_CongApp.
    + eapply IHht1 ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht2 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht7 with (Δ0 := Δ,, svass nx A1)
        ; [ reflexivity | eassumption .. ].
      * cbn. reflexivity.
    + eapply meta_eqconv.
      * eapply IHht8 with (Δ0 := Δ,, svass ny A2)
        ; [ reflexivity | eassumption .. ].
      * reflexivity.
    + eapply @type_subst with (A := sProd nx A1 B1) ; eassumption.
    + eapply @type_subst with (A := sProd ny A2 B2) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_CongEq.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_CongRefl.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_EqToHeq.
    + apply IHht1 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_HeqTypeEq.
    + apply IHht1 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_Pack.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
  - cbn. eapply cong_ProjT1 with (A2 :=  A2 {#|Δ| := uu1}).
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply cong_ProjT2 with (A1 :=  A1 {#|Δ| := uu1}).
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply cong_ProjTe.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply eq_reflexivity.
    erewrite subst_ind_type by eassumption.
    eapply type_Ind.
    + eapply wf_subst ; eassumption.
    + eassumption.
  - cbn. eapply eq_reflexivity.
    erewrite subst_type_of_constructor by eassumption.
    eapply type_Construct.
    eapply wf_subst ; eassumption.
  - cheat.
  - eapply eq_conv.
    + eapply IHht1 ; assumption.
    + eapply @cong_subst with (A := sSort s) ; eassumption.
  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; omega.
Defined.

Corollary full_cong_subst :
  forall {Σ Γ nx B Δ t1 t2 u1 u2 A},
    type_glob Σ ->
    Σ ;;; Γ ,, svass nx B ,,, Δ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i u1 = u2 : B ->
    Σ ;;; Γ ,, svass nx B ,,, Δ |-i t2 : A ->
    Σ ;;; Γ |-i u1 : B ->
    Σ ;;; Γ ,,, subst_context u1 Δ |-i
    t1{ #|Δ| := u1 } = t2{ #|Δ| := u2 } : A{ #|Δ| := u1 }.
Proof.
  intros Σ Γ nx B Δ t1 t2 u1 u2 A hg ht hu ht2 hu1.
  eapply eq_transitivity.
  - exact (cong_subst ht hg hu1).
  - exact (cong_substs ht2 hg hu hu1).
Defined.

Lemma pre_cong_subst1 :
  forall {Σ Γ t1 t2 A B u1 u2 n},
    type_glob Σ ->
    Σ ;;; Γ ,, svass n A |-i t1 = t2 : B ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ ,, svass n A |-i t2 : B ->
    Σ ;;; Γ |-i u1 : A ->
    Σ ;;; Γ |-i t1{ 0 := u1 } = t2{ 0 := u2 } : B{ 0 := u1 }.
Proof.
  intros Σ Γ t1 t2 A B u1 u2 n hg ht hu ht2 hu1.
  eapply @full_cong_subst with (Δ := []) ; eassumption.
Defined.

Lemma pre_cong_subst2 :
  forall {Σ Γ t1 t2 A B C na nb u1 u2 v1 v2},
    type_glob Σ ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t1 = t2 : C ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ |-i v1 = v2 : B{ 0 := u1 } ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t2 : C ->
    Σ ;;; Γ |-i u1 : A ->
    Σ;;; Γ,, svass nb (B {0 := u1}) |-i t2 {1 := u2} : C {1 := u1} ->
    Σ ;;; Γ |-i v1 : B{ 0 := u1 } ->
    Σ ;;; Γ |-i t1{ 1 := u1 }{ 0 := v1 }
             = t2{ 1 := u2 }{ 0 := v2 } : C{ 1 := u1 }{ 0 := v1 }.
Proof.
  intros Σ Γ t1 t2 A B C na nb u1 u2 v1 v2 hg ht hu hv ht2 hu1 hst2 hv1.
  eapply @full_cong_subst with (Δ := []).
  - assumption.
  - eapply @full_cong_subst with (Δ := [ svass nb B ]).
    + assumption.
    + exact ht.
    + assumption.
    + assumption.
    + assumption.
  - cbn. assumption.
  - cbn. assumption.
  - cbn. assumption.
Defined.

Inductive eqctx Σ : scontext -> scontext -> Type :=
| eqnil : eqctx Σ nil nil
| eqsnoc Γ na A Δ nb B s :
    eqctx Σ Γ Δ ->
    Σ ;;; Γ |-i A = B : sSort s ->
    eqctx Σ (Γ ,, svass na A) (Δ ,, svass nb B).

Fact eqctx_refl :
  forall {Σ Γ},
    wf Σ Γ ->
    eqctx Σ Γ Γ.
Proof.
  intros Σ Γ h.
  dependent induction Γ.
  - constructor.
  - dependent destruction h.
    econstructor.
    + now apply IHΓ.
    + now apply eq_reflexivity.
Defined.

(* Lemma ctx_conv : *)
(*   forall {Σ Γ Δ}, *)
(*     eqctx Σ Γ Δ -> *)
(*     forall {t A}, *)
(*       Σ ;;; Γ |-i t : A -> *)
(*       Σ ;;; Δ |-i t : A. *)
(* Proof. *)
  (* intros Σ Γ Δ eq. *)
  (* dependent induction eq ; intros t C h. *)
  (* - assumption. *)
  (* - dependent induction h. *)
  (*   + eapply type_Rel. *)
(* Admitted. *)

Lemma ctx_conv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-i t : A ->
    eqctx Σ Γ Δ ->
    Σ ;;; Δ |-i t : A.
Admitted.

Lemma eqctx_conv :
  forall {Σ Γ Δ t u A},
    Σ ;;; Γ |-i t = u : A ->
    eqctx Σ Γ Δ ->
    Σ ;;; Δ |-i t = u : A.
Admitted.

Lemma istype_type :
  forall {Σ Γ t T},
    type_glob Σ ->
    Σ ;;; Γ |-i t : T ->
    ∑ s, Σ ;;; Γ |-i T : sSort s.
Proof.
  intros Σ Γ t T hg H.
  induction H.
  - revert n isdecl. induction w ; intros n isdecl.
    + cbn in isdecl. easy.
    + destruct n.
      * cbn.
        exists s. change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01 ; eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- auto with arith.
        -- destruct (IHw n isdecl') as [s' hh].
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
  - exists (max_sort s1 s2). apply type_Prod.
    + assumption.
    + eapply ctx_conv ; [ eassumption |].
      econstructor.
      * apply eqctx_refl. now apply (typing_wf H).
      * apply eq_reflexivity. eassumption.
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
  - exists (succ_sort (succ_sort s)). apply type_Sort. apply (typing_wf H).
  - exists s. apply type_Eq ; assumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). apply type_Heq. all: try assumption.
    eapply type_Transport ; eassumption.
  - exists (succ_sort (succ_sort (max_sort s z))).
    apply type_Heq.
    + eapply type_Sort. apply (typing_wf H).
    + eapply type_Sort. apply (typing_wf H).
    + apply type_Prod ; assumption.
    + apply type_Prod ; assumption.
  - exists (succ_sort (max_sort s z)). apply type_Heq.
    + apply type_Prod ; assumption.
    + apply type_Prod ; assumption.
    + eapply type_Lambda ; eassumption.
    + eapply type_Lambda ; eassumption.
  - exists (succ_sort z). apply type_Heq.
    + change (sSort z) with ((sSort z){ 0 := v1 }).
      eapply typing_subst ; eassumption.
    + change (sSort z) with ((sSort z){ 0 := v2 }).
      eapply typing_subst ; eassumption.
    + eapply type_App ; eassumption.
    + eapply type_App ; eassumption.
  - exists (succ_sort (succ_sort s)). apply type_Heq.
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Eq ; assumption.
    + apply type_Eq ; assumption.
  - exists (succ_sort s). apply type_Heq.
    + apply type_Eq ; assumption.
    + apply type_Eq ; assumption.
    + eapply type_Refl ; eassumption.
    + eapply type_Refl ; eassumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). eapply type_Eq ; try assumption.
    apply type_Sort. apply (typing_wf H).
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. assumption.
  - exists s. assumption.
  - exists (succ_sort s). apply type_Heq ; try assumption.
    + eapply type_ProjT1 ; eassumption.
    + eapply @type_ProjT2 with (A1 := A1) ; eassumption.
  - destruct (typed_ind_type hg isdecl) as [s h].
    exists s.
    change (sSort s) with (lift #|Γ| #|@nil scontext_decl| (sSort s)).
    replace (sind_type decl)
      with (lift #|Γ| #|@nil scontext_decl| (sind_type decl))
      by (erewrite lift_ind_type by eassumption ; reflexivity).
    eapply meta_ctx_conv.
    + eapply @type_lift with (Γ := []) (Ξ := []) (Δ := Γ).
      * assumption.
      * assumption.
      * rewrite nil_cat. assumption.
    + cbn. apply nil_cat.
  - destruct (typed_type_of_constructor hg isdecl) as [s h].
    exists s. change (sSort s) with (lift #|Γ| #|@nil scontext_decl| (sSort s)).
    set (ty := stype_of_constructor (fst Σ) (ind, i) univs decl isdecl) in *.
    replace ty with (lift #|Γ| #|@nil scontext_decl| ty)
      by (erewrite lift_type_of_constructor by eassumption ; reflexivity).
    eapply meta_ctx_conv.
    + eapply @type_lift with (Γ := []) (Ξ := []) (Δ := Γ).
      * assumption.
      * assumption.
      * rewrite nil_cat. assumption.
    + cbn. apply nil_cat.
  - cheat.
  - exists s. assumption.
Defined.

Lemma eq_typing :
  forall {Σ Γ t u T},
    type_glob Σ ->
    Σ ;;; Γ |-i t = u : T ->
    (Σ ;;; Γ |-i t : T) * (Σ ;;; Γ |-i u : T).
Proof.
  intros Σ Γ t u T hg h.
  induction h ;
    repeat match goal with
           | H : ?A * ?B |- _ => destruct H
           end ;
    split ; try (now constructor + easy).
  all: try (econstructor ; eassumption).
  - eapply type_conv.
    + econstructor ; try eassumption.
      eapply type_conv.
      * econstructor ; eassumption.
      * econstructor ; eassumption.
      * apply eq_reflexivity. constructor ; assumption.
    + instantiate (1 := s2).
      change (sSort s2) with ((sSort s2){ 0 := u }).
      eapply typing_subst ; eassumption.
    + apply eq_reflexivity.
      change (sSort s2) with ((sSort s2){ 0 := u }).
      eapply typing_subst ; eassumption.
  - eapply typing_subst ; eassumption.
  - econstructor ; try eassumption.
    econstructor ; eassumption.
  - econstructor ; try eassumption.
    econstructor ; try eassumption.
    econstructor. apply (typing_wf t1).
  - constructor ; try eassumption.
    eapply ctx_conv.
    + eassumption.
    + econstructor.
      * apply eqctx_refl. now apply (typing_wf pi1_0).
      * eassumption.
  - eapply type_conv.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- eapply eqctx_refl. now apply (typing_wf pi1_1).
        -- eassumption.
      * eapply ctx_conv.
        -- eapply type_conv ; eassumption.
        -- econstructor.
           ++ apply eqctx_refl. now apply (typing_wf pi1_1).
           ++ eassumption.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_1).
        -- apply eq_reflexivity. eassumption.
    + apply eq_symmetry. apply cong_Prod.
      * assumption.
      * eapply eqctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_1).
        -- apply eq_reflexivity. eassumption.
  - econstructor.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_2).
        -- eassumption.
      * econstructor.
        -- eassumption.
        -- econstructor.
           ++ eassumption.
           ++ eapply ctx_conv ; [ eassumption |].
              econstructor.
              ** apply eqctx_refl. now apply (typing_wf pi1_2).
              ** eassumption.
        -- eapply cong_Prod ; eassumption.
      * econstructor ; eassumption.
    + instantiate (1 := s2).
      change (sSort s2) with ((sSort s2){ 0 := u1 }).
      eapply typing_subst ; eassumption.
    + change (sSort s2) with ((sSort s2){0 := u2}).
      eapply pre_cong_subst1.
      * assumption.
      * eapply eq_symmetry. eassumption.
      * eapply eq_symmetry. assumption.
      * assumption.
      * assumption.
  - constructor.
    + assumption.
    + eapply type_conv ; eassumption.
    + eapply type_conv ; eassumption.
  - eapply type_conv ; [ eapply type_Refl | .. ].
    + eassumption.
    + eapply type_conv ; eassumption.
    + constructor ; eassumption.
    + apply eq_symmetry. apply cong_Eq ; assumption.
  - eapply type_conv ; [ econstructor | .. ].
    1: eassumption.
    all: try (econstructor ; eassumption).
    + eapply ctx_conv ; [ eassumption |].
      econstructor.
      * econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_2).
        -- eassumption.
      * eapply cong_Eq.
        -- match goal with
           | |- _ ;;; _ |-i _ = _ : ?S =>
             change S with (lift0 1 S)
           end.
           eapply cong_lift01 ; eassumption.
        -- eapply cong_lift01 ; eassumption.
        -- apply eq_reflexivity.
           eapply type_conv ; [ eapply type_Rel | .. ].
           ++ econstructor.
              ** now apply (typing_wf pi1_2).
              ** eassumption.
           ++ instantiate (1 := s1).
              change (sSort s1) with (lift0 1 (sSort s1)).
              eapply typing_lift01 ; eassumption.
           ++ cbn. apply eq_reflexivity.
              change (sSort s1) with (lift0 1 (sSort s1)).
              eapply typing_lift01 ; eassumption.
    + eapply type_conv ; [ eassumption | .. ].
      * econstructor.
        -- eassumption.
        -- eapply type_conv ; eassumption.
        -- eapply type_conv ; eassumption.
      * apply cong_Eq ; eassumption.
    + eapply type_conv ; [ eassumption | .. ].
      * instantiate (1 := s2).
        change (sSort s2) with ((sSort s2){ 1 := u2 }{ 0 := sRefl A2 u2 }).
        eapply typing_subst2.
        -- assumption.
        -- eassumption.
        -- eassumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply type_conv ; [ eapply type_Refl | .. ].
           ++ eassumption.
           ++ eapply type_conv ; eassumption.
           ++ eapply type_Eq ; eassumption.
           ++ apply eq_symmetry. apply cong_Eq.
              ** assumption.
              ** assumption.
              ** apply eq_reflexivity. assumption.
      * match goal with
        | |- _ ;;; _ |-i _ = _ : ?S =>
          change S with (S{1 := u1}{0 := sRefl A1 u1})
        end.
        eapply pre_cong_subst2.
        -- assumption.
        -- eassumption.
        -- assumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply cong_Refl ; eassumption.
        -- assumption.
        -- assumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply ctx_conv.
           ++ eapply @type_subst with (A := sSort s2) (Δ := [ svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) ]).
              ** exact pi2_1.
              ** assumption.
              ** assumption.
           ++ cbn. rewrite subst_decl_svass. cbn. rewrite !lift_subst, lift00.
              econstructor.
              ** eapply eqctx_refl. eapply typing_wf. eassumption.
              ** eapply eq_symmetry. eapply cong_Eq.
                 all: try eapply eq_reflexivity.
                 all: eassumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply type_Refl ; eassumption.
    + match goal with
      | |- _ ;;; _ |-i _ : ?S =>
        change S with (S{1 := v1}{0 := p1})
      end.
      eapply typing_subst2.
      * assumption.
      * eassumption.
      * assumption.
      * cbn. rewrite !lift_subst, lift00. assumption.
    + eapply eq_symmetry.
      match goal with
      | |- _ ;;; _ |-i _ = _ : ?S =>
        change S with (S{1 := v1}{0 := p1})
      end.
      eapply pre_cong_subst2.
      * assumption.
      * eassumption.
      * assumption.
      * cbn. rewrite !lift_subst, lift00. assumption.
      * assumption.
      * assumption.
      * cbn. rewrite !lift_subst, lift00.
        eapply ctx_conv.
        -- eapply @type_subst with (A := sSort s2) (Δ := [ svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) ]).
           ++ exact pi2_1.
           ++ assumption.
           ++ assumption.
        -- cbn. rewrite subst_decl_svass. cbn. rewrite !lift_subst, lift00.
           econstructor.
           ++ eapply eqctx_refl. eapply typing_wf. eassumption.
           ++ eapply eq_symmetry. eapply cong_Eq.
              all: try eapply eq_reflexivity.
              all: eassumption.
      * cbn. rewrite !lift_subst, lift00.
        assumption.
  - eapply type_conv.
    + eapply type_Transport ; try eassumption.
      * eapply type_conv.
        -- eassumption.
        -- apply type_Eq.
           ++ apply type_Sort. eapply typing_wf. eassumption.
           ++ assumption.
           ++ assumption.
        -- eapply cong_Eq.
           ++ eapply eq_reflexivity.
              apply type_Sort. eapply typing_wf. eassumption.
           ++ assumption.
           ++ assumption.
      * eapply type_conv ; eassumption.
    + eassumption.
    + eapply eq_symmetry. assumption.
  - eapply type_Heq ; try assumption.
    + eapply type_conv ; eassumption.
    + eapply type_conv ; eassumption.
      Unshelve. 1-3: exact nAnon. cbn. omega.
  - eapply type_conv.
    + eapply type_HeqRefl ; try eassumption.
      eapply type_conv ; eassumption.
    + eapply type_Heq ; try assumption ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq ; assumption.
  - eapply type_HeqTrans with (B := B) (b := b) ; eassumption.
  - eapply type_HeqTrans with (B := B) (b := b) ; eassumption.
  - eapply type_conv.
    + eapply type_HeqTransport ; [ .. | eassumption ] ; eassumption.
    + eapply type_Heq ; try eassumption.
      eapply type_Transport ; eassumption.
    + eapply eq_symmetry.
      eapply cong_Heq ; try eapply eq_reflexivity ; try eassumption.
      eapply cong_Transport ; try eapply eq_reflexivity ; eassumption.
  - eapply type_conv.
    + eapply type_CongProd ; try eassumption.
      eapply type_conv ; try eassumption.
      * eapply type_Heq.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply @typing_subst with (B := sSort z).
           ++ assumption.
           ++ eapply @type_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass nx A1 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
        -- eapply @typing_subst with (B := sSort z).
           ++ assumption.
           ++ eapply @type_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass ny A2 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
      * eapply cong_Heq. all: try eapply eq_reflexivity.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply @pre_cong_subst1 with (B := sSort z).
           ++ assumption.
           ++ eapply @cong_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass nx A1 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @cong_ProjT1 with (A2 := lift0 1 A2).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply eq_reflexivity.
                 refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
           ++ cbn. eapply @type_lift
                     with (A := sSort z)
                          (Δ := [ svass np (sPack A1 A2) ])
                          (Ξ := [ svass nx A1 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
        -- eapply @pre_cong_subst1 with (B := sSort z).
           ++ assumption.
           ++ eapply @cong_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass ny A2 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @cong_ProjT2 with (A1 := lift0 1 A1).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply eq_reflexivity.
                 refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
           ++ cbn. eapply @type_lift
                     with (A := sSort z)
                          (Δ := [ svass np (sPack A1 A2) ])
                          (Ξ := [ svass ny A2 ]).
              ** assumption.
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
    + eapply type_Heq.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply type_Prod ; eassumption.
      * eapply type_Prod ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq. all: try eapply eq_reflexivity.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
  - eapply type_conv.
    + eapply type_CongLambda ; try eassumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Heq.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
        -- eapply cong_Heq. all: try eapply eq_reflexivity.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- assumption.
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- assumption.
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
      * eapply type_conv ; try eassumption.
        -- eapply type_Heq.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply typing_subst.
              ** assumption.
              ** eapply @type_lift
                   with (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- eapply type_conv ; eassumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply typing_subst.
              ** assumption.
              ** eapply @type_lift
                   with (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- eapply type_conv ; eassumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
        -- eapply cong_Heq. all: try eapply eq_reflexivity.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- assumption.
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- assumption.
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @cong_subst with (Δ := []).
              --- eapply @cong_lift
                    with (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- assumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @cong_subst with (Δ := []).
              --- eapply @cong_lift
                    with (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- assumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
      * eapply type_conv ; eassumption.
      * eapply type_conv ; eassumption.
    + eapply type_Heq.
      * eapply type_Prod ; eassumption.
      * eapply type_Prod ; eassumption.
      * eapply type_Lambda ; eassumption.
      * eapply type_Lambda ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
      * eapply cong_Lambda ; try eassumption.
        eapply eq_reflexivity. eassumption.
      * eapply cong_Lambda ; try eassumption.
        eapply eq_reflexivity. eassumption.
  - eapply type_conv.
    + eapply type_CongApp ; try eassumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Heq.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply @typing_subst with (B := sSort z).
              ** assumption.
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- assumption.
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
        -- eapply cong_Heq. all: try eapply eq_reflexivity.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply @cong_subst with (A := sSort z) (Δ := []).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- assumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @cong_subst with (A := sSort z) (Δ := []).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- assumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
      * eapply type_conv.
        -- eassumption.
        -- eapply type_Heq.
           ++ eapply type_Prod ; eassumption.
           ++ eapply type_Prod ; eassumption.
           ++ eapply type_conv ; try exact t1.
              ** eapply type_Prod ; eassumption.
              ** eapply cong_Prod ; try eassumption.
                 eapply eq_reflexivity. assumption.
           ++ eapply type_conv ; try exact t2.
              ** eapply type_Prod ; eassumption.
              ** eapply cong_Prod ; try eassumption.
                 eapply eq_reflexivity. assumption.
        -- eapply cong_Heq.
           ** eapply cong_Prod ; try eassumption.
              eapply eq_reflexivity. assumption.
           ** eapply cong_Prod ; try eassumption.
              eapply eq_reflexivity. assumption.
           ** eapply eq_reflexivity. assumption.
           ** eapply eq_reflexivity. assumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Prod ; eassumption.
        -- eapply cong_Prod ; try eassumption.
           eapply eq_reflexivity. assumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Prod ; eassumption.
        -- eapply cong_Prod ; try eassumption.
           eapply eq_reflexivity. assumption.
    + eapply type_Heq.
      * eapply @typing_subst with (B := sSort z) ; eassumption.
      * eapply @typing_subst with (B := sSort z) ; eassumption.
      * eapply type_App ; eassumption.
      * eapply type_App ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq.
      * eapply @cong_subst with (A := sSort z) (Δ := []).
        -- eassumption.
        -- assumption.
        -- assumption.
      * eapply @cong_subst with (A := sSort z) (Δ := []).
        -- eassumption.
        -- assumption.
        -- assumption.
      * eapply cong_App.
        all: try eapply eq_reflexivity.
        all: eassumption.
      * eapply cong_App.
        all: try eapply eq_reflexivity.
        all: eassumption.
  - eapply type_ProjT2 with (A1 := A1) ; eassumption.
  - eapply type_ProjT2 with (A1 := A1) ; eassumption.
  - eapply type_conv.
    + eapply type_ProjTe with (A1 := A1) (A2 := A2) ; eassumption.
    + eapply type_Heq ; try eassumption.
      * eapply type_ProjT1 with (A2 := A2) ; eassumption.
      * eapply type_ProjT2 with (A1 := A1) ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq ; try eapply eq_reflexivity ; try eassumption.
      * eapply cong_ProjT1 with (A2 := A2) ; eassumption.
      * eapply cong_ProjT2 with (A1 := A1) ; eassumption.
  - cheat.
  - cheat.
  - eapply type_HeqToEq ; try eassumption.
    eapply type_HeqRefl ; eassumption.
Defined.

Corollary full_cong_subst' :
  forall {Σ Γ nx B Δ t1 t2 u1 u2 A},
    type_glob Σ ->
    Σ ;;; Γ ,, svass nx B ,,, Δ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i u1 = u2 : B ->
    Σ ;;; Γ ,,, subst_context u1 Δ |-i
    t1{ #|Δ| := u1 } = t2{ #|Δ| := u2 } : A{ #|Δ| := u1 }.
Proof.
  intros Σ Γ nx B Δ t1 t2 u1 u2 A hg ht hu.
  destruct (eq_typing hg ht) as [_ ht2].
  destruct (eq_typing hg hu) as [hu1 _].
  eapply eq_transitivity.
  - exact (cong_subst ht hg hu1).
  - exact (cong_substs ht2 hg hu hu1).
Defined.

Lemma cong_subst1 :
  forall {Σ Γ t1 t2 A B u1 u2 n},
    type_glob Σ ->
    Σ ;;; Γ ,, svass n A |-i t1 = t2 : B ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ |-i t1{ 0 := u1 } = t2{ 0 := u2 } : B{ 0 := u1 }.
Proof.
  intros Σ Γ t1 t2 A B u1 u2 n hg ht hu.
  eapply @full_cong_subst' with (Δ := []) ; eassumption.
Defined.

Lemma cong_subst2 :
  forall {Σ Γ t1 t2 A B C na nb u1 u2 v1 v2},
    type_glob Σ ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t1 = t2 : C ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ |-i v1 = v2 : B{ 0 := u1 } ->
    Σ ;;; Γ |-i t1{ 1 := u1 }{ 0 := v1 }
             = t2{ 1 := u2 }{ 0 := v2 } : C{ 1 := u1 }{ 0 := v1 }.
Proof.
  intros Σ Γ t1 t2 A B C na nb u1 u2 v1 v2 hg ht hu hv.
  eapply @full_cong_subst' with (Δ := []).
  - assumption.
  - eapply @full_cong_subst' with (Δ := [ svass nb B ]).
    + assumption.
    + exact ht.
    + assumption.
  - cbn. assumption.
Defined.

Lemma sorts_in_sort :
  forall {Σ Γ s1 s2 s},
    Σ ;;; Γ |-i sSort s1 : sSort s ->
    Σ ;;; Γ |-i sSort s2 : sSort s ->
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort s.
Admitted.

(* Fixpoint strengthen_sort' {Σ Γ s A} (h : Σ ;;; Γ |-i sSort s : A) {struct h} : *)
(*   forall {z B}, *)
(*     Σ ;;; Γ |-i A = B : sSort z -> *)
(*     Σ ;;; [] |-i B : sSort z -> *)
(*     Σ ;;; [] |-i sSort s : B *)

(* with strengthen_eqsort {Σ Γ s z A} *)
(*   (h : Σ ;;; Γ |-i sSort s = A : sSort z) {struct h} : *)
(*   Σ ;;; [] |-i A : sSort z -> *)
(*   Σ ;;; [] |-i sSort s = A : sSort z. *)
(* Proof. *)
(*   - dependent destruction h ; intros z C he hC. *)
(*     + pose proof (strengthen_eqsort _ _ _ _ _ he hC). *)
(*       eapply type_conv. *)
(*       * eapply type_Sort. constructor. *)
(*       * eassumption. *)
(*       * assumption. *)
(*     + cheat. *)
(*   - cheat. *)
(* Defined. *)

(* Lemma strengthen_sort' : *)
(*   forall {Σ Γ s A}, *)
(*     Σ ;;; Γ |-i sSort s : A -> *)
(*     forall {z B}, *)
(*       Σ ;;; Γ |-i A = B : sSort z -> *)
(*       Σ ;;; [] |-i B : sSort z -> *)
(*       Σ ;;; [] |-i sSort s : B. *)
(* Proof. *)
(*   intros Σ Γ s A hs. *)
(*   dependent induction hs ; intros z C he hA. *)
(*   - eapply type_Sort. constructor. *)
(*   - *)


Lemma strengthen_sort :
  forall {Σ Γ Δ s z},
    Σ ;;; Γ |-i sSort s : sSort z ->
    wf Σ Δ ->
    Σ ;;; Δ |-i sSort s : sSort z.
Admitted.

Lemma strengthen_sort_eq :
  forall {Σ Γ Δ s1 s2 z},
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort z ->
    wf Σ Δ ->
    Σ ;;; Δ |-i sSort s1 = sSort s2 : sSort z.
Admitted.

Lemma cong_succ_sort :
  forall {Σ Γ s1 s2 s3},
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort s3 ->
    Σ ;;; Γ |-i sSort (succ_sort s1) = sSort (succ_sort s2) : sSort (succ_sort s3).
Admitted.

(* Lemma uniqueness_ctx : *)
(*   forall {Σ Γ u A}, *)
(*     Σ ;;; Γ |-i u : A -> *)
(*     forall {Δ} *)

Lemma uniqueness :
  forall {Σ Γ A B u},
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u : B ->
    ∑ s, Σ ;;; Γ |-i A = B : sSort s.
Proof.
  (* intros Σ Γ A B u hu1. *)
  (* dependent induction hu1 ; intros hu2 ; dependent induction hu2. *)
  (* - eexists. cheat. *)
  (* - destruct (IHhu2_1 w isdecl) as [s' h']. *)
  (*   eexists. eapply eq_transitivity. *)
  (*   + exact h'. *)
  (*   + eapply eq_conv. *)
  (*     * exact e. *)
  (*     * (* This bit I usually use uniqueness to conclude... *)
  (*          This means we might need a stronger induction hypothesis to go. *)
  (*        *) *)
  (*       cheat. *)
  (* - *)
Admitted.
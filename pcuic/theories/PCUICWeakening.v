(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List BinPos Compare_dec ZArith Lia.
Require Import Coq.Program.Syntax Coq.Program.Basics.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICPattern PCUICTyping
  PCUICWeakeningEnv PCUICClosed PCUICReduction PCUICPosition PCUICReflect.
Require Import ssreflect ssrbool.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Import MonadNotation.

Set Default Goal Selector "!".

(** * Weakening lemmas for typing derivations.

  [weakening_*] proves weakening of typing, reduction etc... w.r.t. the *local* environment. *)

Set Asymmetric Patterns.
Generalizable Variables Σ Γ t T.

Derive Signature NoConfusion for All_local_env.
Derive Signature for All_local_env_over.

(* FIXME inefficiency in equations: using a very slow "pattern_sigma" to simplify an equality between sigma types *)
Ltac Tactics.destruct_tele_eq H ::= noconf H.

(* Derive Signature NoConfusion for All_local_env. *)
Derive NoConfusion for All_local_env_over.
Derive NoConfusion for context_decl.

Lemma typed_liftn `{checker_flags} Σ Γ t T n k :
  wf Σ.1 -> wf_local Σ Γ -> k >= #|Γ| ->
  Σ ;;; Γ |- t : T -> lift n k T = T /\ lift n k t = t.
Proof.
  intros wfΣ wfΓ Hk Hty.
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ Hcl].
  rewrite -> andb_and in Hcl. destruct Hcl as [clb clty].
  pose proof (closed_upwards k clb).
  pose proof (closed_upwards k clty).
  simpl in *. forward H0 by lia.
  apply (lift_closed n) in H0.
  simpl in *. forward H1 by lia.
  now apply (lift_closed n) in H1.
Qed.

Lemma weaken_nth_error_ge {Γ Γ' v Γ''} : #|Γ'| <= v ->
  nth_error (Γ ,,, Γ') v =
  nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (#|Γ''| + v).
Proof.
  intros Hv.
  rewrite -> !nth_error_app_context_ge, ?lift_context_length.
  - f_equal. lia.
  - rewrite lift_context_length. lia.
  - rewrite lift_context_length. lia.
  - auto.
Qed.

Lemma weaken_nth_error_lt {Γ Γ' Γ'' v} : v < #|Γ'| ->
  nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') v =
  option_map (lift_decl #|Γ''| (#|Γ'| - S v)) (nth_error (Γ ,,, Γ') v).
Proof.
  simpl. intros Hv.
  rewrite -> !nth_error_app_context_lt.
  - rewrite nth_error_lift_context_eq.
    do 2 f_equal. lia.
  - lia.
  - now rewrite lift_context_length.
Qed.

Lemma lift_simpl {Γ'' Γ' : context} {i t} :
  i < #|Γ'| ->
  lift0 (S i) (lift #|Γ''| (#|Γ'| - S i) t) = lift #|Γ''| #|Γ'| (lift0 (S i) t).
Proof.
  intros. assert (#|Γ'| = S i + (#|Γ'| - S i)) by easy.
  rewrite -> H0 at 2.
  rewrite permute_lift; try easy.
Qed.

Lemma lift_iota_red n k pars c args brs :
  lift n k (iota_red pars c args brs) =
  iota_red pars c (List.map (lift n k) args) (List.map (on_snd (lift n k)) brs).
Proof.
  unfold iota_red. rewrite !lift_mkApps. f_equal; auto using map_skipn.
  rewrite nth_map; simpl; auto.
Qed.

Lemma parsubst_empty k a : subst [] k a = a.
Proof.
  induction a in k |- * using term_forall_list_ind; simpl; try congruence;
    try solve [f_equal; eauto; solve_all; eauto].

  - elim (Nat.compare_spec k n); destruct (Nat.leb_spec k n); intros; try easy.
    + subst. rewrite Nat.sub_diag. simpl. rewrite Nat.sub_0_r. reflexivity.
    + assert (n - k > 0) by lia.
      assert (exists n', n - k = S n').
      * exists (Nat.pred (n - k)). lia.
      * destruct H2. rewrite H2. simpl. now rewrite Nat.sub_0_r.
Qed.

Lemma lift_unfold_fix n k mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx = Some (narg, lift n k fn).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  case e: isLambda => //.
  intros [= <- <-]. simpl.
  rewrite isLambda_lift //.
  repeat f_equal.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite fix_subst_length. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve lift_unfold_fix.

Lemma lift_unfold_cofix n k mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx = Some (narg, lift n k fn).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  intros [= <- <-]. simpl. repeat f_equal.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite cofix_subst_length. f_equal.
  unfold cofix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve lift_unfold_cofix.

Lemma decompose_app_rec_lift n k t l :
  let (f, a) := decompose_app_rec t l in
  decompose_app_rec (lift n k t) (map (lift n k) l)  = (lift n k f, map (lift n k) a).
Proof.
  induction t in k, l |- *; simpl; auto.

  - destruct Nat.leb; reflexivity.
  - specialize (IHt1 k (t2 :: l)).
    destruct decompose_app_rec. now rewrite IHt1.
Qed.

Lemma decompose_app_lift n k t f a :
  decompose_app t = (f, a) -> decompose_app (lift n k t) = (lift n k f, map (lift n k) a).
Proof.
  generalize (decompose_app_rec_lift n k t []).
  unfold decompose_app. destruct decompose_app_rec.
  now move=> Heq [= <- <-].
Qed.
Hint Rewrite decompose_app_lift using auto : lift.

Lemma lift_is_constructor:
  forall (args : list term) (narg : nat) n k,
    is_constructor narg args = true -> is_constructor narg (map (lift n k) args) = true.
Proof.
  intros args narg.
  unfold is_constructor; intros.
  rewrite nth_error_map. destruct nth_error; try discriminate. simpl.
  unfold isConstruct_app in *. destruct decompose_app eqn:Heq.
  eapply decompose_app_lift in Heq as ->.
  destruct t0; try discriminate || reflexivity.
Qed.
Hint Resolve lift_is_constructor.

Hint Rewrite lift_subst_instance_constr : lift.
Hint Rewrite lift_mkApps : lift.
Hint Rewrite distr_lift_subst distr_lift_subst10 : lift.
Hint Rewrite lift_iota_red : lift.

Lemma lift_declared_symbol `{checker_flags} :
  forall Σ k n u decl ty i j,
    wf Σ ->
    declared_symbol Σ k decl ->
    nth_error (symbols decl) n = Some ty ->
    let ty' :=
      subst0 (symbols_subst k (S n) u #|symbols decl|) (subst_instance_constr u ty)
    in
    lift i j ty' = ty'.
Proof.
  intros Σ k n u decl ty i j hΣ h e ty'.
  eapply lift_closed.
  eapply closed_upwards.
  - eapply closed_declared_symbol. all: eauto.
  - lia.
Qed.

Lemma lift_declared_constant `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_constant Σ cst decl ->
  decl = map_constant_body (lift n k) decl.
Proof.
  unfold declared_constant.
  intros.
  eapply lookup_on_global_env in H0; eauto.
  destruct H0 as [Σ' [wfΣ' decl']].
  red in decl'. red in decl'.
  destruct decl. simpl in *. destruct cst_body.
  - unfold map_constant_body. simpl.
    pose proof decl' as declty.
    apply typecheck_closed in declty; eauto.
    + destruct declty as [declty Hcl].
      rewrite -> andb_and in Hcl. destruct Hcl as [clb clty].
      pose proof (closed_upwards k clb).
      pose proof (closed_upwards k clty).
      simpl in *. forward H0 by lia. forward H1 by lia.
      apply (lift_closed n k) in H0.
      apply (lift_closed n k) in H1. rewrite H0 H1. reflexivity.
    + constructor.
  - red in decl'.
    destruct decl'.
    apply typecheck_closed in t.
    + destruct t as [_ ccst].
      rewrite -> andb_and in ccst. destruct ccst as [ccst _].
      eapply closed_upwards in ccst; simpl.
      * apply (lift_closed n k) in ccst. unfold map_constant_body. simpl.
        rewrite ccst. reflexivity.
      * lia.
    + auto.
    + constructor.
Qed.

Definition lift_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun k' => lift n (k' + k)) m.

Lemma lift_wf_local `{checker_flags} Σ Γ n k :
  wf Σ.1 ->
  wf_local Σ Γ ->
  lift_context n k Γ = Γ.
Proof.
  intros wfΣ.
  induction 1; auto; unfold lift_context, snoc; rewrite fold_context_snoc0; auto; unfold snoc;
    f_equal; auto; unfold map_decl; simpl.
  - destruct t0 as [s Hs]. unfold vass. f_equal.
    eapply typed_liftn; eauto. lia.
  - red in t0. destruct t0. unfold vdef. f_equal.
    + f_equal. eapply typed_liftn; eauto. lia.
    + eapply typed_liftn in t0 as [Ht HT]; eauto. lia.
Qed.

Lemma closed_wf_local `{checker_flags} Σ Γ :
  wf Σ.1 ->
  wf_local Σ Γ ->
  closed_ctx Γ.
Proof.
  intros wfΣ. unfold closed_ctx, mapi. intros wf. generalize 0.
  induction wf; intros n; auto; unfold closed_ctx, snoc; simpl;
    rewrite mapi_rec_app forallb_app; unfold id, closed_decl.
  - simpl.
    destruct t0 as [s Hs].
    eapply typecheck_closed in Hs as [closedΓ tcl]; eauto.
    rewrite -> andb_and in *. simpl in *; rewrite andb_true_r in tcl |- *.
    simpl in *. intuition auto.
    + apply IHwf.
    + erewrite closed_upwards; eauto. rewrite List.rev_length. lia.
  - simpl. eapply typecheck_closed in t1 as [closedΓ tcl]; eauto.
    rewrite -> andb_and in *. intuition auto.
    + apply IHwf.
    + erewrite closed_upwards; eauto.
      * erewrite closed_upwards; eauto.
        rewrite List.rev_length. lia.
      * rewrite List.rev_length. lia.
Qed.

Lemma lift_declared_minductive `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive Σ cst decl ->
  lift_mutual_inductive_body n k decl = decl.
Proof.
  intros wfΣ Hdecl. eapply on_declared_minductive in Hdecl; eauto.
  destruct decl. simpl in *. f_equal.
  - apply onParams in Hdecl. simpl in *.
    eapply lift_wf_local; eauto; eauto.
  - apply onInductives in Hdecl.
    revert Hdecl. simpl. generalize ind_bodies at 2 4 5.
    intros.
    eapply (Alli_mapi_id Hdecl).
    clear Hdecl. intros.
    destruct x; simpl in *.
    destruct (decompose_prod_assum [] ind_type) eqn:Heq.
    destruct (decompose_prod_assum [] (lift n k ind_type)) eqn:Heq'.
    destruct X. simpl in *.
    assert (lift n k ind_type = ind_type).
    { repeat red in onArity.
      destruct onArity as [s Hs].
      eapply typed_liftn; eauto; eauto.
      - constructor.
      - simpl. lia.
    }
    rewrite H0 in Heq'. rewrite Heq in Heq'. revert Heq'; intros [= <- <-].
    f_equal; auto.
    + eapply All_map_id. eapply All2_All_left; tea.
      intros [[x p] n'] y [[s Hty] [cs Hargs]].
      unfold on_pi2; cbn; f_equal; f_equal.
      simpl in Hty.
      eapply typed_liftn. 4:eapply Hty.
      * eauto.
      * apply typing_wf_local in Hty; eauto.
      * change PCUICEnvironment.arities_context with arities_context. lia.
    + destruct(eq_dec ind_projs []) as [Hp|Hp].
      * subst; auto.
      * specialize (onProjections Hp).
        destruct onProjections as [_ _ _ onProjections].
        apply (Alli_map_id onProjections).
        intros n1 [x p].
        unfold on_projection. simpl.
        intros [s Hty].
        unfold on_snd; f_equal; f_equal.
        eapply typed_liftn. 4:eapply Hty. all:eauto.
        -- eapply typing_wf_local in Hty; eauto.
        -- simpl.
           rewrite smash_context_length. simpl.
           rewrite context_assumptions_fold. lia.
Qed.

Lemma lift_declared_inductive `{checker_flags} Σ ind mdecl idecl n k :
  wf Σ ->
  declared_inductive Σ mdecl ind idecl ->
  map_one_inductive_body (context_assumptions mdecl.(ind_params))
                         (length (arities_context mdecl.(ind_bodies))) (fun k' => lift n (k' + k))
                         (inductive_ind ind) idecl = idecl.
Proof.
  unfold declared_inductive. intros wfΣ [Hmdecl Hidecl].
  eapply (lift_declared_minductive _ _ _ n k) in Hmdecl. 2: auto.
  unfold lift_mutual_inductive_body in Hmdecl.
  destruct mdecl. simpl in *.
  injection Hmdecl. intros Heq.
  clear Hmdecl.
  pose proof Hidecl as Hidecl'.
  rewrite <- Heq in Hidecl'.
  rewrite nth_error_mapi in Hidecl'.
  clear Heq.
  unfold option_map in Hidecl'. rewrite Hidecl in Hidecl'.
  congruence.
Qed.

Lemma subst0_inds_lift ind u mdecl n k t :
  (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
          (lift n (#|arities_context (ind_bodies mdecl)| + k) t)) =
  lift n k (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)) t).
Proof.
  rewrite (distr_lift_subst_rec _ _ n 0 k). simpl.
  unfold arities_context. rewrite rev_map_length inds_length.
  f_equal. generalize (ind_bodies mdecl).
  clear. intros.
  induction l; unfold inds; simpl; auto. f_equal. auto.
Qed.

Lemma lift_declared_constructor `{checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ ->
  declared_constructor Σ mdecl idecl c cdecl ->
  lift n k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci]. intros wfΣ [Hidecl Hcdecl].
  eapply (lift_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
  unfold type_of_constructor. destruct cdecl as [[id t'] arity].
  destruct idecl; simpl in *.
  injection Hidecl.
  intros.
  pose Hcdecl as Hcdecl'.
  rewrite <- H1 in Hcdecl'.
  rewrite nth_error_map in Hcdecl'. rewrite Hcdecl in Hcdecl'.
  simpl in Hcdecl'. injection Hcdecl'.
  intros.
  rewrite <- H3 at 2.
  rewrite <- lift_subst_instance_constr.
  now rewrite subst0_inds_lift.
Qed.

Lemma lift_declared_projection `{checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ ->
  declared_projection Σ mdecl idecl c pdecl ->
  on_snd (lift n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  intros.
  destruct H0 as [[Hmdecl Hidecl] [Hpdecl Hnpar]].
  eapply declared_decl_closed in Hmdecl; auto.
  simpl in Hmdecl.
  pose proof (onNpars _ _ _ _ Hmdecl).
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hmdecl; eauto.
  pose proof (onProjections Hmdecl) as onp; eauto. forward onp.
  1: now eapply nth_error_Some_non_nil in Hpdecl.
  eapply on_projs, nth_error_alli in onp; eauto.
  move: onp => /= /andb_and[Hd _]. simpl in Hd.
  rewrite smash_context_length in Hd. simpl in *.
  change PCUICEnvironment.context_assumptions with context_assumptions in H0.
  rewrite H0 in Hd.
  destruct pdecl as [id ty]. unfold on_snd; simpl in *.
  f_equal. eapply lift_closed.
  eapply closed_upwards; eauto. lia.
Qed.

Lemma lift_fix_context:
  forall (mfix : list (def term)) (n k : nat),
    fix_context (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) = lift_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rewrite map_vass_map_def rev_mapi.
  fold (fix_context mfix).
  rewrite (lift_context_alt n k (fix_context mfix)).
  unfold lift_decl. now rewrite mapi_length fix_context_length.
Qed.

Hint Rewrite <- lift_fix_context : lift.

Lemma All_local_env_lift `{checker_flags}
      (P Q : context -> term -> option term -> Type) c n k :
  All_local_env Q c ->
  (forall Γ t T,
      Q Γ t T ->
      P (lift_context n k Γ) (lift n (#|Γ| + k) t)
        (option_map (lift n (#|Γ| + k)) T)
  ) ->
  All_local_env P (lift_context n k c).
Proof.
  intros Hq Hf.
  induction Hq in |- *; try econstructor; eauto;
    simpl; rewrite lift_context_snoc; econstructor; eauto.
  - simpl. eapply (Hf _ _ None). eauto.
  - simpl. eapply (Hf _ _ None). eauto.
  - simpl. eapply (Hf _ _ (Some t)). eauto.
Qed.

Lemma lift_destArity ctx t n k :
  destArity (lift_context n k ctx) (lift n (#|ctx| + k) t) =
        match destArity ctx t with
        | Some (args, s) => Some (lift_context n k args, s)
        | None => None
        end.
Proof.
  revert ctx.
  induction t in n, k |- * using term_forall_list_ind; intros ctx; simpl; trivial.
  - destruct Nat.leb; reflexivity.
  - move: (IHt2 n k (ctx,, vass n0 t1)).
    now rewrite lift_context_snoc /= /lift_decl /map_decl /vass /= => ->.
  - move: (IHt3 n k (ctx,, vdef n0 t1 t2)).
    now rewrite lift_context_snoc /= /lift_decl /map_decl /vass /= => ->.
Qed.

(* Lemma lift_strip_outer_cast n k t : lift n k (strip_outer_cast t) = strip_outer_cast (lift n k t). *)
(* Proof. *)
(*   induction t; simpl; try reflexivity. *)
(*   destruct Nat.leb; reflexivity. *)
(*   now rewrite IHt1. *)
(* Qed. *)

Definition on_pair {A B C D} (f : A -> B) (g : C -> D) (x : A * C) :=
  (f (fst x), g (snd x)).

Lemma lift_instantiate_params_subst n k params args s t :
  instantiate_params_subst (mapi_rec (fun k' decl => lift_decl n (k' + k) decl) params #|s|)
                           (map (lift n k) args) (map (lift n k) s) (lift n (#|s| + k) t) =
  option_map (on_pair (map (lift n k)) (lift n (#|s| + k + #|params|))) (instantiate_params_subst params args s t).
Proof.
  induction params in args, t, n, k, s |- *.
  - destruct args; simpl; rewrite ?Nat.add_0_r; reflexivity.
  - simpl. simpl. (* rewrite <- lift_strip_outer_cast. generalize (strip_outer_cast t). *)
    (* clear t; intros t. *)
    destruct a as [na [body|] ty]; simpl; try congruence.
    + destruct t; simpl; try congruence.
      * now destruct (Nat.leb (#|s| + k) n0).
      * specialize (IHparams n k args (subst0 s body :: s) t3).
        rewrite <- Nat.add_succ_r. simpl in IHparams.
        rewrite Nat.add_succ_r.
        replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
        rewrite <- IHparams.
        rewrite distr_lift_subst. reflexivity.
    + destruct t; simpl; try congruence.
      1: now destruct (Nat.leb (#|s| + k) n0).
      destruct args; simpl; try congruence.
      specialize (IHparams n k args (t :: s) t2). simpl in IHparams.
      replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
      rewrite <- IHparams. auto.
Qed.

Lemma instantiate_params_subst_length params args s t ctx t' :
  instantiate_params_subst params args s t = Some (ctx, t') ->
  #|ctx| = #|s| + #|params|.
Proof.
  induction params in args, s, t, ctx, t' |- * ;
  destruct args; simpl; auto; try congruence.
  - rewrite Nat.add_0_r. congruence.
  - destruct decl_body.
    + simpl.
      destruct t; simpl; try congruence.
      intros. erewrite IHparams; eauto. simpl. lia.
    + destruct t; simpl; try congruence.
  - destruct decl_body.
    + simpl.
      destruct t; simpl; try congruence.
      intros. erewrite IHparams; eauto. simpl. lia.
    + destruct t; simpl; try congruence.
      intros. erewrite IHparams; eauto. simpl. lia.
Qed.

Lemma lift_decl_closed n k d : closed_decl k d -> lift_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /lift_decl /map_decl /=.
  - move/andP => [cb cty]. now rewrite !lift_closed //.
  - move=> cty; now rewrite !lift_closed //.
Qed.

Lemma closed_decl_upwards k d : closed_decl k d -> forall k', k <= k' -> closed_decl k' d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /=.
  - move/andP => [cb cty] k' lek'. do 2 rewrite (@closed_upwards k) //.
  - move=> cty k' lek'; rewrite (@closed_upwards k) //.
Qed.

Lemma closedn_ctx_lift :
  forall n k Γ,
    closedn_ctx k Γ ->
    lift_context n k Γ = Γ.
Proof.
  intros n k Γ h.
  induction Γ as [| [na [b|] A] Γ ih ] in n, k, h |- *.
  - reflexivity.
  - apply closedn_ctx_cons in h. apply utils.andP in h as [hΓ hd].
    unfold closed_decl in hd. cbn in hd.
    apply utils.andP in hd as [? ?].
    rewrite lift_context_snoc. rewrite -> ih by auto.
    unfold ",,". f_equal.
    unfold lift_decl, map_decl. cbn.
    rewrite -> 2!lift_closed.
    1: reflexivity.
    all: replace (#|Γ| + k) with (k + #|Γ|) by lia.
    all: assumption.
  - apply closedn_ctx_cons in h. apply utils.andP in h as [hΓ hd].
    unfold closed_decl in hd. cbn in hd.
    rewrite lift_context_snoc. rewrite -> ih by auto.
    unfold ",,". f_equal.
    unfold lift_decl, map_decl. cbn. f_equal.
    rewrite -> lift_closed.
    1: reflexivity.
    replace (#|Γ| + k) with (k + #|Γ|) by lia.
    assumption.
Qed.

Lemma closed_ctx_lift n k ctx : closed_ctx ctx -> lift_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  unfold closed_ctx, id. simpl.
  rewrite mapi_app forallb_app List.rev_length /= lift_context_snoc0 /snoc Nat.add_0_r.
  move/andb_and => /= [Hctx /andb_and [Ha _]].
  rewrite IHctx // lift_decl_closed //. now apply: closed_decl_upwards.
Qed.

Lemma closed_tele_lift n k ctx :
  closed_ctx ctx ->
  mapi (fun (k' : nat) (decl : context_decl) => lift_decl n (k' + k) decl) (List.rev ctx) = List.rev ctx.
Proof.
  rewrite /closedn_ctx /mapi. simpl. generalize 0.
  induction ctx using rev_ind.
  1: move=> //.
  move=> n0.
  rewrite /closedn_ctx !rev_app_distr /id /=.
  move/andP => [closedx Hctx].
  rewrite lift_decl_closed.
  - rewrite (@closed_decl_upwards n0) //; try lia.
  - f_equal. now rewrite IHctx.
Qed.

Lemma lift_instantiate_params n k params args t :
  closed_ctx params ->
  option_map (lift n k) (instantiate_params params args t) =
  instantiate_params params (map (lift n k) args) (lift n k t).
Proof.
  unfold instantiate_params.
  move/(closed_tele_lift n k params)=> Heq.
  rewrite -{2}Heq.
  specialize (lift_instantiate_params_subst n k (List.rev params) args [] t).
  move=> /= Heq'; rewrite Heq'.
  case E: (instantiate_params_subst (List.rev params) args)=> [[l' t']|] /= //.
  rewrite distr_lift_subst.
  move/instantiate_params_subst_length: E => -> /=.  do 3 f_equal. lia.
Qed.
Hint Rewrite lift_instantiate_params : lift.

(* bug eauto with let .. in hypothesis failing *)
Lemma lift_decompose_prod_assum_rec ctx t n k :
  let (ctx', t') := decompose_prod_assum ctx t in
  (lift_context n k ctx', lift n (length ctx' + k) t') =
  decompose_prod_assum (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction t in n, k, ctx |- *; simpl;
    try rewrite -> Nat.sub_diag, Nat.add_0_r; try (eauto; congruence).
  - now destruct (Nat.leb (#|ctx| + k) n0).
  - specialize (IHt2 (ctx ,, vass na t1) n k).
    destruct decompose_prod_assum. rewrite IHt2. simpl.
    rewrite lift_context_snoc. reflexivity.
  - specialize (IHt3 (ctx ,, vdef na t1 t2) n k).
    destruct decompose_prod_assum. rewrite IHt3. simpl.
    rewrite lift_context_snoc. reflexivity.
Qed.

Lemma lift_decompose_prod_assum t n k :
  let (ctx', t') := decompose_prod_assum [] t in
  (lift_context n k ctx', lift n (length ctx' + k) t') =
  decompose_prod_assum [] (lift n k t).
Proof. apply lift_decompose_prod_assum_rec. Qed.

Lemma lift_it_mkProd_or_LetIn n k ctx t :
  lift n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (lift_context_snoc n k ctx a). unfold snoc in e. rewrite -> e. clear e.
  simpl. rewrite -> IHctx.
  pose (lift_context_snoc n k ctx a).
  now destruct a as [na [b|] ty].
Qed.
Hint Rewrite lift_it_mkProd_or_LetIn : lift.

Lemma to_extended_list_lift n k c :
  to_extended_list (lift_context n k c) = to_extended_list c.
Proof.
  unfold to_extended_list, to_extended_list_k. generalize 0. generalize (nil term) at 1 2.
  induction c in n, k |- *; simpl; intros. 1: reflexivity.
  rewrite -> lift_context_snoc0. unfold snoc. simpl.
  destruct a. destruct decl_body.
  - unfold lift_decl, map_decl. simpl.
    now rewrite -> IHc.
  - simpl. apply IHc.
Qed.

Lemma to_extended_list_map_lift:
  forall (n k : nat) (c : context), to_extended_list c = map (lift n (#|c| + k)) (to_extended_list c).
Proof.
  intros n k c.
  pose proof (to_extended_list_lift_above c).
  symmetry. solve_all.
  destruct H as [x' [-> Hx]]. simpl.
  destruct (leb_spec_Set (#|c| + k) x').
  - f_equal. lia.
  - reflexivity.
Qed.

Lemma lift_decl_vdef :
  forall n k na t T,
    lift_decl n k (vdef na t T) =
    vdef na (lift n k t) (lift n k T).
Proof.
  intros n k na t T. reflexivity.
Qed.

Lemma untyped_subslet_lift :
  forall Γ1 Γ2 Γ3 s Δ,
    untyped_subslet (Γ1 ,,, Γ3) s Δ ->
    untyped_subslet
      (Γ1 ,,, Γ2 ,,, lift_context #|Γ2| 0 Γ3)
      (map (lift #|Γ2| #|Γ3|) s)
      (lift_context #|Γ2| #|Γ3| Δ).
Proof.
  intros Γ1 Γ2 Γ3 s Δ h.
  induction h.
  - constructor.
  - rewrite lift_context_snoc. cbn.
    econstructor. eapply IHh.
  - rewrite lift_context_snoc. cbn.
    rewrite distr_lift_subst.
    rewrite lift_decl_vdef.
    apply untyped_subslet_length in h. rewrite h.
    eapply untyped_cons_let_def.
    eassumption.
Qed.

Lemma closedn_ctx_upwards :
  forall n m Γ,
    closedn_ctx m Γ ->
    n >= m ->
    closedn_ctx n Γ.
Proof.
  intros n m Γ c e.
  induction Γ as [| [na [b|] A] Γ ih ] in n, m, e, c |- *.
  - constructor.
  - apply closedn_ctx_cons in c.
    apply utils.andP in c as [hΓ hd].
    unfold closed_decl in hd. cbn in hd.
    apply utils.andP in hd as [hb hA].
    cbn. rewrite mapi_rec_app. cbn.
    rewrite forallb_app. cbn.
    eapply ih in hΓ. 2: eassumption.
    unfold closedn_ctx in hΓ. rewrite hΓ. cbn.
    unfold closed_decl. cbn.
    rewrite List.rev_length.
    eapply closed_upwards with (k' := n + (#|Γ| + 0)) in hb. 2: lia.
    rewrite hb. cbn.
    eapply closed_upwards with (k' := n + (#|Γ| + 0)) in hA. 2: lia.
    rewrite hA. reflexivity.
  - apply closedn_ctx_cons in c.
    apply utils.andP in c as [hΓ hd].
    unfold closed_decl in hd. cbn in hd.
    cbn. rewrite mapi_rec_app. cbn.
    rewrite forallb_app. cbn.
    eapply ih in hΓ. 2: eassumption.
    unfold closedn_ctx in hΓ. rewrite hΓ. cbn.
    rewrite List.rev_length.
    eapply closed_upwards with (k' := n + (#|Γ| + 0)) in hd. 2: lia.
    rewrite hd. reflexivity.
Qed.

Definition subst_decl s k (d : context_decl) := map_decl (subst s k) d.

Lemma subst_context_snoc s k Γ d : subst_context s k (d :: Γ) = subst_context s k Γ ,, subst_decl s (#|Γ| + k) d.
Proof.
  unfold subst_context, fold_context.
  rewrite !rev_mapi !rev_involutive /mapi mapi_rec_eqn /snoc.
  f_equal. 1: now rewrite Nat.sub_0_r List.rev_length.
  rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
  rewrite app_length !List.rev_length. simpl. f_equal. f_equal. lia.
Qed.
Hint Rewrite subst_context_snoc : subst.

Lemma subst_context_snoc0 s Γ d : subst_context s 0 (Γ ,, d) = subst_context s 0 Γ ,, subst_decl s #|Γ| d.
Proof.
  unfold snoc. now rewrite subst_context_snoc Nat.add_0_r.
Qed.
Hint Rewrite subst_context_snoc : subst.

Lemma distr_lift_context_subst_context :
  forall n k p s Γ,
    lift_context n (p+ k) (subst_context s p Γ) =
    subst_context (map (lift n k) s) p (lift_context n (p + #|s| + k) Γ).
Proof.
  intros n k p s Γ.
  induction Γ as [| [na [b|] A] Γ ih ] in n, k, p, s |- *.
  - reflexivity.
  - rewrite lift_context_snoc subst_context_snoc.
    rewrite lift_context_snoc subst_context_snoc.
    rewrite ih. f_equal.
    unfold lift_decl, subst_decl. unfold map_decl. cbn.
    rewrite subst_context_length lift_context_length.
    replace (#|Γ| + (p + k)) with (#|Γ| + p + k) by lia.
    rewrite -> 2!distr_lift_subst_rec.
    f_equal. all: f_equal. all: f_equal.
    + f_equal. lia.
    + lia.
  - rewrite lift_context_snoc subst_context_snoc.
    rewrite lift_context_snoc subst_context_snoc.
    rewrite ih. f_equal.
    unfold lift_decl, subst_decl. unfold map_decl. cbn.
    rewrite subst_context_length lift_context_length.
    replace (#|Γ| + (p + k)) with (#|Γ| + p + k) by lia.
    rewrite distr_lift_subst_rec.
    f_equal. f_equal. f_equal. lia.
Qed.

(*
  |- Γ, Δ, Ξ, Θ
  Γ |- s : Δ
  |- Γ, subst_context s #|Θ| Δ, subst_context s 0 Θ
*)

(* TODO MOVE *)
Lemma closedn_ctx_subst_context :
  forall s k p Γ,
    forallb (closedn k) s ->
    closedn_ctx (k + p + #|s|) Γ ->
    closedn_ctx (k + p) (subst_context s p Γ).
Proof.
  intros s k p Γ hs h.
  induction Γ as [| [na [b|] A] Γ ih ] in s, k, p, h, hs |- *.
  - constructor.
  - rewrite subst_context_snoc. cbn.
    rewrite mapi_rec_app. rewrite forallb_app. cbn.
    apply closedn_ctx_cons in h.
    apply utils.andP in h as [h1 h2].
    unfold closed_decl in h2. cbn in h2.
    apply utils.andP in h2 as [h2 h3].
    eapply ih in h1 as h1'. 2: auto.
    unfold closedn_ctx in h1'. rewrite h1'. cbn.
    unfold subst_decl, map_decl, closed_decl. cbn.
    rewrite List.rev_length. rewrite subst_context_length.
    unfold id.
    replace (#|Γ| + 0) with #|Γ| by lia.
    replace (k + p + #|s| + #|Γ|) with (k + (p + #|Γ|) + #|s|) in h2 by lia.
    replace (k + p + #|s| + #|Γ|) with (k + (p + #|Γ|) + #|s|) in h3 by lia.
    apply closedn_subst in h2. 2: auto.
    apply closedn_subst in h3. 2: auto.
    replace (#|Γ| + p) with (p + #|Γ|) by lia.
    replace (k + p + #|Γ|) with (k + (p + #|Γ|)) by lia.
    rewrite h2 h3. reflexivity.
  - rewrite subst_context_snoc. cbn.
    rewrite mapi_rec_app. rewrite forallb_app. cbn.
    apply closedn_ctx_cons in h.
    apply utils.andP in h as [h1 h2].
    unfold closed_decl in h2. cbn in h2.
    eapply ih in h1 as h1'. 2: auto.
    unfold closedn_ctx in h1'. rewrite h1'. cbn.
    rewrite List.rev_length. rewrite subst_context_length.
    replace (#|Γ| + 0) with #|Γ| by lia.
    replace (k + p + #|s| + #|Γ|) with (k + (p + #|Γ|) + #|s|) in h2 by lia.
    apply closedn_subst in h2. 2: auto.
    replace (#|Γ| + p) with (p + #|Γ|) by lia.
    replace (k + p + #|Γ|) with (k + (p + #|Γ|)) by lia.
    rewrite h2. reflexivity.
Qed.

Corollary closedn_ctx_subst_context0 :
  forall s k Γ,
    forallb (closedn k) s ->
    closedn_ctx (k + #|s|) Γ ->
    closedn_ctx k (subst_context s 0 Γ).
Proof.
  intros s k Γ hs h.
  replace k with (k + 0) by lia.
  eapply closedn_ctx_subst_context.
  - assumption.
  - replace (k + 0) with k by lia. assumption.
Qed.

(* TODO MOVE *)
Lemma nfalse_le :
  forall l,
    nfalse l <= #|l|.
Proof.
  intros l. induction l as [| [] l ih]. all: cbn ; lia.
Qed.

(* TODO MOVE *)
Lemma masked_before_le :
  forall m n,
    masked_before m n <= n.
Proof.
  intros m n.
  unfold masked_before.
  etransitivity.
  - eapply nfalse_le.
  - apply firstn_le_length.
Qed.

(* TODO MOVE *)
Lemma masked_before_le_nfalse :
  forall m n,
    masked_before m n <= nfalse m.
Proof.
  intros m n.
  unfold masked_before.
  induction m as [| [] m ih] in n |- *.
  - destruct n. all: auto.
  - destruct n.
    + cbn. lia.
    + cbn. apply ih.
  - destruct n.
    + cbn. lia.
    + cbn. specialize (ih n). lia.
Qed.

Lemma nfalse_app :
  forall l1 l2,
    nfalse (l1 ++ l2) = nfalse l1 + nfalse l2.
Proof.
  intros l1 l2.
  induction l1 as [| [] l1 ih] in l2 |- *.
  - reflexivity.
  - cbn. apply ih.
  - cbn. f_equal. apply ih.
Qed.

Lemma match_option_eq :
  forall A B (x : option A) (f : A -> B) b y,
    x = Some y ->
    match x with
    | Some a => f a
    | None => b
    end = f y.
Proof.
  intros A B x f b y e. subst. reflexivity.
Qed.

Lemma strengthen_mask_lift :
  forall m k t u p q,
    q > #|m| + k ->
    strengthen_mask m k t = Some u ->
    strengthen_mask m k (lift p q t) = Some (lift p (q - nfalse m) u).
Proof.
  intros m k t u p q h e.
  induction t in m, k, u, p, q, e, h |- * using term_forall_list_ind.
  (* all: try solve [
    cbn in * ; apply some_inj in e ; subst ;
    reflexivity
  ]. *)
  all: try solve [
    cbn in * ;
    repeat match type of e with
    | context [ strengthen_mask ?m ?k ?t ] =>
      let e' := fresh "e" in
      destruct (strengthen_mask m k t) eqn:e' ; [| discriminate ] ;
      match goal with
      | ih : forall m k u p q, _ -> strengthen_mask m k t = _ -> _ |- _ =>
        erewrite ih ; [| eauto ; lia .. ]
      end
    end ;
    apply some_inj in e ; subst ; cbn - [minus] ;
    pose proof (nfalse_le m) ;
    (repeat f_equal) ; lia
  ].
  - cbn.
    pose proof (nfalse_le m).
    destruct (Nat.leb_spec q n).
    + unfold strengthen_mask in e.
      destruct (Nat.ltb_spec n k). 1: lia.
      unfold strengthen_mask.
      destruct (Nat.ltb_spec (p + n) k). 1: lia.
      destruct nth_error eqn:e1.
      1:{ apply nth_error_Some_length in e1. lia. }
      clear e1.
      destruct nth_error eqn:e1.
      1:{ apply nth_error_Some_length in e1. lia. }
      clear e1.
      cbn in e. apply some_inj in e. subst.
      cbn. f_equal.
      match goal with
      | |- context [ ?a <=? ?b ] =>
        destruct (Nat.leb_spec a b)
      end. 2: lia.
      f_equal. lia.
    + rewrite e. f_equal.
      unfold strengthen_mask in e.
      destruct (Nat.ltb_spec n k).
      * cbn in e. apply some_inj in e. subst.
        cbn.
        match goal with
        | |- context [ ?a <=? ?b ] =>
          destruct (Nat.leb_spec a b)
        end. 1: lia.
        reflexivity.
      * destruct nth_error as [[]|] eqn:e1. 2: discriminate.
        --- cbn in e. apply some_inj in e. subst.
            cbn.
            match goal with
            | |- context [ ?a <=? ?b ] =>
              destruct (Nat.leb_spec a b)
            end.
            1:{
              pose proof (masked_before_le_nfalse m (n - k)).
              pose proof (masked_before_le m (n - k)).
              apply nth_error_Some_length in e1.
              exfalso.
              assert (e : nfalse m = masked_before m (n - k) + nfalse (skipn (n - k) m)).
              { rewrite <- (firstn_skipn (n - k) m) at 1.
                rewrite nfalse_app. reflexivity.
              }
              assert (q <= n + nfalse (skipn (n - k) m)) by lia.
              pose proof (nfalse_le (skipn (n - k) m)).
              pose proof (skipn_length (n - k) m) as hl.
              lia.
            }
            reflexivity.
        --- cbn in e. apply some_inj in e. subst.
            cbn.
            match goal with
            | |- context [ ?a <=? ?b ] =>
              destruct (Nat.leb_spec a b)
            end.
            1:{
              pose proof (masked_before_le_nfalse m (n - k)).
              pose proof (masked_before_le m (n - k)).
              apply nth_error_None in e1.
              exfalso. lia.
            }
            reflexivity.
  - cbn in *.
    destruct monad_map as [l1|] eqn:e1. 2: discriminate.
    apply some_inj in e. subst. cbn.
    eapply match_option_eq with (f := fun x => _).
    induction H in l1, e1.
    1:{ cbn in e1. apply some_inj in e1. subst. reflexivity. }
    cbn in e1.
    destruct strengthen_mask eqn:e2. 2: discriminate.
    destruct monad_map eqn:e3. 2: discriminate.
    apply some_inj in e1. subst. cbn.
    erewrite p0. all: eauto.
    erewrite IHAll. 2: reflexivity.
    reflexivity.
  - cbn in *.
    destruct monad_map as [l1|] eqn:e1. 2: discriminate.
    repeat match type of e with
    | context [ strengthen_mask ?m ?k ?t ] =>
      let e' := fresh "e" in
      destruct (strengthen_mask m k t) eqn:e' ; [| discriminate ] ;
      match goal with
      | ih : forall m k u p q, _ -> strengthen_mask m k t = _ -> _ |- _ =>
        erewrite ih ; [| eauto ; lia .. ]
      end
    end.
    apply some_inj in e. subst.
    cbn - [minus].
    eapply match_option_eq with (f := fun x => _).
    clear IHt1 IHt2 e0 e2.
    induction X as [| [n u] l hu hl ih] in l1, e1.
    1:{ cbn in e1. apply some_inj in e1. subst. reflexivity. }
    cbn in e1.
    destruct strengthen_mask eqn:e2. 2: discriminate.
    destruct monad_map eqn:e3. 2: discriminate.
    apply some_inj in e1. subst. cbn.
    erewrite hu. all: eauto.
    erewrite ih. 2: reflexivity.
    reflexivity.
  - cbn in *.
    destruct monad_map as [l|] eqn:e1. 2: discriminate.
    apply some_inj in e. subst. cbn.
    eapply match_option_eq with (f := fun x => _).
    rewrite map_length.
    revert e1. generalize #|m0|. intros v e1.
    induction X as [| [na ty bo ra] mfix [h1 h2] hm ih] in l, v, e1.
    1:{ cbn in e1. apply some_inj in e1. subst. reflexivity. }
    cbn in *.
    repeat match type of e1 with
    | context [ strengthen_mask ?m ?k ?t ] =>
      let e' := fresh "e" in
      destruct (strengthen_mask m k t) eqn:e' ; [| discriminate ] ;
      match goal with
      | ih : forall m k u p q, _ -> strengthen_mask m k t = _ -> _ |- _ =>
        erewrite ih ; [| eauto ; lia .. ]
      end
    end.
    destruct monad_map eqn:e3. 2: discriminate.
    apply some_inj in e1. subst. cbn - [minus].
    erewrite ih. 2: eauto.
    f_equal. unfold map_def at 2. cbn.
    f_equal.
Admitted.

Lemma match_pattern_lift :
  forall npat Ξ p t s n m,
    match_pattern npat Ξ p t = Some s ->
    match_pattern npat Ξ p (lift n m t) = Some (map (option_map (lift n m)) s).
Proof.
  intros npat Ξ p t s n m e.
  induction p in npat, Ξ, t, s, n, m, e |- * using pattern_all_rect.
  - cbn in *. destruct strengthen_mask eqn:e1. 2: discriminate.
    apply strengthen_mask_lift with (p := n) (q := m) in e1 as e2.
    2:{
      (* m >= #|mask| + #|Ξ| *)
      (* How are we ever gonna have that?
        By saying m >= #|s| + #|Ξ|?
        #|s| = npat, but what's the link with mask?
        From validity of patterns we have #|mask| = nb so we'd need to talk
        about nb actually.
        Isn't nb already #|Ξ|?
        This is really confusing...
      *)
      admit.
    }
Admitted.

Lemma match_elims_lift :
  forall k hn ui npat l t s n m,
    match_elims k hn ui npat l t = Some s ->
    match_elims k hn ui npat l (lift n m t) =
    Some (map (option_map (lift n m)) s).
Proof.
  intros k hn ui npat l t s n m e.
  induction l as [| [] l ih] in k, hn, ui, npat, t, s, n, m, e |- *.
  - unfold match_elims in *.
    destruct (eqb_spec (tSymb k hn ui) t). 2: discriminate.
    subst. cbn in e. apply some_inj in e. subst.
    unfold lift at 1.
    destruct (eqb_spec (tSymb k hn ui) (tSymb k hn ui)).
    2:{ exfalso. auto. }
    cbn. f_equal.
    unfold subs_empty. induction npat. 1: reflexivity.
    cbn. f_equal. auto.
  - cbn in *. destruct t. all: try discriminate.
    cbn. destruct match_pattern eqn:e1. 2: discriminate.
    (* We need the same for match_pattern *)
Abort.

Lemma match_lhs_lift :
  forall k hn ui npat l t s n m,
    match_lhs k hn ui npat l t = Some s ->
    match_lhs k hn ui npat l (lift n m t) = Some (map (lift n m) s).
Proof.
  intros k hn ui npat l t s n m e.
  unfold match_lhs in *.
  destruct match_elims eqn:e1. 2: discriminate.
  cbn in e.
Abort.

Lemma match_rule_lift :
  forall nsymb k ui r t s n m,
    match_rule nsymb k ui r t = Some s ->
    match_rule nsymb k ui r (lift n m t) = Some (map (lift n m) s).
Proof.
  intros nsymb k ui r t s n m e.
  unfold match_rule in *.
Abort.

Lemma weakening_red1 `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ ->
  red1 Σ (Γ ,,, Γ') M N ->
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
    (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros wfΣ H.
  remember (Γ ,,, Γ') as Γ0. revert Γ Γ' Γ'' HeqΓ0.
  induction H using red1_ind_all in |- *; intros Γ0 Γ' Γ'' HeqΓ0; try subst Γ; simpl;
    autorewrite with lift;
    try solve [  econstructor; eauto ].

  - elim (leb_spec_Set); intros Hn.
    + rewrite -> simpl_lift; try lia. rewrite -> Nat.add_succ_r.
      econstructor; eauto.
      erewrite (weaken_nth_error_ge Hn) in H. eauto.

    + rewrite <- lift_simpl by easy.
      econstructor.
      rewrite -> (weaken_nth_error_lt Hn).
      now unfold lift_decl; rewrite -> option_map_decl_body_map_decl, H.

  - econstructor; eauto.
    rewrite H0. f_equal.
    eapply (lookup_on_global_env _ _ _ _ wfΣ) in H.
    destruct H as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    rewrite -> H0 in decl'.
    apply typecheck_closed in decl'; eauto. 2: constructor.
    destruct decl'.
    rewrite -> andb_and in i. destruct i as [Hclosed _].
    simpl in Hclosed.
    pose proof (closed_upwards #|Γ'| Hclosed).
    forward H by lia.
    apply (lift_closed #|Γ''| #|Γ'|) in H. auto.

  - simpl. constructor.
    now rewrite -> nth_error_map, H.

  - unfold rrhs.
    apply match_rule_length in H1 as el.
    rewrite <- el.
    rewrite distr_lift_subst_rec.
    set (ss := symbols_subst _ _ _ _).
    assert (e : forall i j, map (lift i j) ss = ss).
    { intros i j. subst ss. unfold symbols_subst.
      rewrite list_make_map. simpl. reflexivity.
    }
    rewrite e.
    set (t' := lift _ _ t).
    rewrite lift_closed.
    1:{
      eapply closed_upwards. 1: eapply closed_rule_rhs.
      all: eauto.
      subst ss. rewrite symbols_subst_length.
      lia.
    }
    rewrite el.
    eapply red_rewrite_rule. all: eauto.
    subst t'.

    eapply untyped_subslet_lift with (Γ2 := Γ'') in H1 as h.
    eapply closed_declared_symbol_pat_context in H as hcl. 2-3: eassumption.
    rewrite -> (closed_ctx_lift _ #|Γ'|) in h.
    + assumption.
    + eapply closedn_ctx_subst_context0.
      * subst ss. unfold symbols_subst. clear.
        generalize (#|symbols decl| - 0). intro m.
        generalize 0 at 2. intro n.
        induction m in n |- *.
        1: reflexivity.
        cbn. apply IHm.
      * cbn. clear - hcl. subst ss.
        rewrite symbols_subst_length.
        replace (#|symbols decl| - 0) with #|symbols decl| by lia.
        assumption.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vass na N) Γ'' eq_refl).
    rewrite -> lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vdef na b t) Γ'' eq_refl).
    rewrite -> lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition; eauto.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vass na M1) Γ'' eq_refl).
    rewrite -> lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition; eauto.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; simpl; intuition eauto.
    congruence.

  - apply fix_red_body. rewrite !lift_fix_context.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel; solve_all. 2: congruence.
    specialize (b0 Γ0 (Γ' ,,, fix_context mfix0)).
    rewrite app_context_assoc in b0. specialize (b0 Γ'' eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> lift_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; intuition eauto.
    + simpl; auto.
    + simpl; congruence.

  - apply cofix_red_body. rewrite !lift_fix_context.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel; solve_all. 2: congruence.
    specialize (b0 Γ0 (Γ' ,,, fix_context mfix0)).
    rewrite app_context_assoc in b0. specialize (b0 Γ'' eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> lift_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.
Qed.

Lemma weakening_red `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ ->
  red Σ (Γ ,,, Γ') M N ->
  red Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros wfΣ; induction 1.
  - constructor.
  - eapply red_trans with (lift #|Γ''| #|Γ'| P); eauto.
    simpl; eapply red1_red. eapply weakening_red1; auto.
Qed.

Fixpoint lift_stack n k π :=
  match π with
  | ε => ε
  | App u π =>
      let k' := #|stack_context π| + k in
      App (lift n k' u) (lift_stack n k π)
  | Fix mfix idx args π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix| + k' in
      let mfix' := List.map (map_def (lift n k') (lift n k'')) mfix in
      Fix mfix' idx (map (lift n k') args) (lift_stack n k π)
  | Fix_mfix_ty na bo ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (lift n k') (lift n k'')) mfix1 in
      let mfix2' := List.map (map_def (lift n k') (lift n k'')) mfix2 in
      Fix_mfix_ty na (lift n k'' bo) ra mfix1' mfix2' idx (lift_stack n k π)
  | Fix_mfix_bd na ty ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (lift n k') (lift n k'')) mfix1 in
      let mfix2' := List.map (map_def (lift n k') (lift n k'')) mfix2 in
      Fix_mfix_bd na (lift n k' ty) ra mfix1' mfix2' idx (lift_stack n k π)
  | CoFix mfix idx args π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix| + k' in
      let mfix' := List.map (map_def (lift n k') (lift n k'')) mfix in
      CoFix mfix' idx (map (lift n k') args) (lift_stack n k π)
  | Case_p indn c brs π =>
      let k' := #|stack_context π| + k in
      let brs' := List.map (on_snd (lift n k')) brs in
      Case_p indn (lift n k' c) brs' (lift_stack n k π)
  | Case indn pred brs π =>
      let k' := #|stack_context π| + k in
      let brs' := List.map (on_snd (lift n k')) brs in
      Case indn (lift n k' pred) brs' (lift_stack n k π)
  | Case_brs indn pred c m brs1 brs2 π =>
      let k' := #|stack_context π| + k in
      let brs1' := List.map (on_snd (lift n k')) brs1 in
      let brs2' := List.map (on_snd (lift n k')) brs2 in
      Case_brs indn (lift n k' pred) (lift n k' c) m brs1' brs2' (lift_stack n k π)
  | Proj p π =>
      Proj p (lift_stack n k π)
  | Prod_l na B π =>
      let k' := #|stack_context π| + k in
      Prod_l na (lift n (S k') B) (lift_stack n k π)
  | Prod_r na A π =>
      let k' := #|stack_context π| + k in
      Prod_r na (lift n k' A) (lift_stack n k π)
  | Lambda_ty na b π =>
      let k' := #|stack_context π| + k in
      Lambda_ty na (lift n (S k') b) (lift_stack n k π)
  | Lambda_tm na A π =>
      let k' := #|stack_context π| + k in
      Lambda_tm na (lift n k' A) (lift_stack n k π)
  | LetIn_bd na B u π =>
      let k' := #|stack_context π| + k in
      LetIn_bd na (lift n k' B) (lift n (S k') u) (lift_stack n k π)
  | LetIn_ty na b u π =>
      let k' := #|stack_context π| + k in
      LetIn_ty na (lift n k' b) (lift n (S k') u) (lift_stack n k π)
  | LetIn_in na b B π =>
      let k' := #|stack_context π| + k in
      LetIn_in na (lift n k' b) (lift n k' B) (lift_stack n k π)
  | coApp u π =>
      let k' := #|stack_context π| + k in
      coApp (lift n k' u) (lift_stack n k π)
  end.

(* TODO MOVE *)
Lemma fix_context_alt_length :
  forall l,
    #|fix_context_alt l| = #|l|.
Proof.
  intro l.
  unfold fix_context_alt.
  rewrite List.rev_length.
  rewrite mapi_length. reflexivity.
Qed.

Lemma lift_zipc :
  forall n k t π,
    let k' := #|stack_context π| + k in
    lift n k (zipc t π) =
    zipc (lift n k' t) (lift_stack n k π).
Proof.
  intros n k t π k'.
  induction π in n, k, t, k' |- *.
  all: try reflexivity.
  all: try solve [
    simpl ; rewrite IHπ ; cbn ; reflexivity
  ].
  - simpl. rewrite IHπ. cbn. f_equal.
    rewrite lift_mkApps. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. f_equal.
    unfold map_def at 1. cbn. f_equal.
    rewrite fix_context_alt_length.
    rewrite !app_length. cbn. rewrite !map_length.
    f_equal. f_equal. lia.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite lift_mkApps. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. cbn. reflexivity.
Qed.

Lemma weakening_eta_expands `{checker_flags} :
  forall u v n k,
    eta_expands u v ->
    eta_expands (lift n k u) (lift n k v).
Proof.
  intros u v n k [na [A [t [π [e1 e2]]]]]. subst.
  rewrite 2!lift_zipc. cbn.
  replace (S (#|stack_context π| + k))
    with ((#|stack_context π| + k) + 1)
    by lia.
  rewrite <- permute_lift by lia.
  eexists _, _, _, _. intuition reflexivity.
Qed.

Lemma weakening_cumul `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ.1 ->
  Σ ;;; Γ ,,, Γ' |- M <= N ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M <= lift #|Γ''| #|Γ'| N.
Proof.
  intros wfΣ. induction 1.
  - constructor. now apply lift_leq_term.
  - eapply weakening_red1 in r; auto.
    econstructor 2; eauto.
  - eapply weakening_red1 in r; auto.
    econstructor 3; eauto.
  - eapply cumul_eta_l. 2: eauto.
    eapply weakening_eta_expands. assumption.
  - eapply cumul_eta_r. 1: eauto.
    eapply weakening_eta_expands. assumption.
Qed.

Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
  destArity ctx (it_mkProd_or_LetIn ctx' t) =
  destArity (ctx ,,, ctx') t.
Proof.
  induction ctx' in ctx, t |- *; simpl; auto.
  rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
Qed.

Lemma lift_build_case_predicate_type ind mdecl idecl u params ps n k :
  closed_ctx (subst_instance_context u (ind_params mdecl)) ->
  build_case_predicate_type ind mdecl
    (map_one_inductive_body (context_assumptions mdecl.(ind_params))
            (length (arities_context (ind_bodies mdecl))) (fun k' => lift n (k' + k))
            (inductive_ind ind) idecl)
    (map (lift n k) params) u ps
  = option_map (lift n k) (build_case_predicate_type ind mdecl idecl params u ps).
Proof.
  intros closedpars. unfold build_case_predicate_type.
  rewrite -> ind_type_map. simpl.
  epose proof (lift_instantiate_params n k _ params (subst_instance_constr u (ind_type idecl))) as H.
  rewrite <- lift_subst_instance_constr.
  erewrite <- H; trivial. clear H.
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) params (subst_instance_constr u (ind_type idecl))) ; cbnr.
  intros ity eq.
  pose proof (lift_destArity [] ity n k) as H; cbn in H. rewrite H; clear H.
  destruct destArity as [[ctx s] | ]; [|reflexivity]. simpl. f_equal.
  rewrite lift_it_mkProd_or_LetIn; cbn. f_equal. f_equal.
  - destruct idecl; reflexivity.
  - rewrite lift_mkApps; cbn; f_equal. rewrite map_app. f_equal.
    + rewrite !map_map lift_context_length; apply map_ext. clear.
      intro. now rewrite -> permute_lift by lia.
    + now rewrite -> to_extended_list_lift, <- to_extended_list_map_lift.
Qed.

Lemma lift_build_branches_type ind mdecl idecl u p params n k :
  closed_ctx (subst_instance_context u (ind_params mdecl)) ->
  build_branches_type ind mdecl
         (map_one_inductive_body (context_assumptions mdecl.(ind_params))
            #|arities_context (ind_bodies mdecl)| (fun k' => lift n (k' + k))
            (inductive_ind ind) idecl)
         (map (lift n k) params) u (lift n k p)
  = map (option_map (on_snd (lift n k)))
        (build_branches_type ind mdecl idecl params u p).
Proof.
  intros closedpars. unfold build_branches_type.
  rewrite -> ind_ctors_map.
  rewrite -> mapi_map, map_mapi. eapply mapi_ext. intros i x.
  destruct x as [[id t] arity]. simpl.
  rewrite <- lift_subst_instance_constr.
  rewrite subst0_inds_lift.
  rewrite <- lift_instantiate_params ; trivial.
  match goal with
  | |- context [ option_map _ (instantiate_params ?x ?y ?z) ] =>
    destruct (instantiate_params x y z) eqn:Heqip; cbnr
  end.
  epose proof (lift_decompose_prod_assum t0 n k).
  destruct (decompose_prod_assum [] t0).
  rewrite <- H.
  destruct (decompose_app t1) as [fn arg] eqn:?.
  rewrite (decompose_app_lift _ _ _ fn arg); auto. simpl.
  destruct (chop _ arg) eqn:Heqchop.
  eapply chop_map in Heqchop.
  rewrite -> Heqchop. clear Heqchop.
  unfold on_snd. simpl. f_equal.
  rewrite -> lift_it_mkProd_or_LetIn, !lift_mkApps, map_app; simpl.
  rewrite -> !lift_mkApps, !map_app, lift_context_length.
  rewrite -> permute_lift by lia. arith_congr.
  now rewrite -> to_extended_list_lift, <- to_extended_list_map_lift.
Qed.


Lemma weakening_typing `{cf : checker_flags} Σ Γ Γ' Γ'' (t : term) :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
  `(Σ ;;; Γ ,,, Γ' |- t : T ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |-
    lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T).
Proof.
  intros HΣ HΓΓ' HΓ'' * H.
  generalize_eqs H. intros eqw. rewrite <- eqw in HΓΓ'.
  revert Γ Γ' Γ'' HΓ'' eqw.
  revert Σ HΣ Γ0 HΓΓ' t T H.
  apply (typing_ind_env (fun Σ Γ0 t T =>  forall Γ Γ' Γ'' : context,
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    Γ0 = Γ ,,, Γ' ->
    Σ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T));
    intros Σ wfΣ Γ0; !!intros; subst Γ0; simpl in *; try solve [econstructor; eauto].

  - elim (leb_spec_Set); intros Hn.
    + rewrite -> simpl_lift; try lia. rewrite -> Nat.add_succ_r.
      constructor. 1: auto.
      now rewrite <- (weaken_nth_error_ge Hn).
    + assert (forall t, lift0 (S n) (lift #|Γ''| (#|Γ'| - S n) t) = lift #|Γ''| #|Γ'| (lift0 (S n) t)).
      * intros.
        assert (H:#|Γ'| = S n + (#|Γ'| - S n)) by easy.
        rewrite -> H at 2.
        rewrite permute_lift; easy.
      * rewrite <- H.
        rewrite -> map_decl_type. constructor; auto.
        now rewrite -> (weaken_nth_error_lt Hn), heq_nth_error.

  - econstructor; auto.
    specialize (IHb Γ (Γ' ,, vass n t) Γ'').
    forward IHb.
    { rewrite -> lift_context_snoc. simpl. econstructor; eauto.
      simpl. rewrite -> Nat.add_0_r. exists s1; eapply IHt; auto.
    }
    rewrite -> lift_context_snoc, plus_0_r in IHb.
    eapply IHb. reflexivity.

  - econstructor; auto.
    simpl.
    specialize (IHb Γ (Γ' ,, vass n t) Γ'').
    forward IHb.
    { rewrite -> lift_context_snoc. simpl; econstructor; eauto.
      simpl.  rewrite -> Nat.add_0_r. exists s1; eapply IHt; auto.
    }
    rewrite -> lift_context_snoc, plus_0_r in IHb.
    eapply IHb. reflexivity.

  - econstructor; auto.
    specialize (IHb Γ Γ' Γ'' wf eq_refl). simpl.
    specialize (IHb' Γ (Γ' ,, vdef n b b_ty) Γ'').
    (* specialize (IHb_ty Γ Γ' Γ''). *)
    forward IHb'.
    { rewrite -> lift_context_snoc. simpl; econstructor; eauto.
      - simpl. eexists. rewrite -> Nat.add_0_r. auto.
      - simpl. rewrite -> Nat.add_0_r. auto.
    }
    rewrite -> lift_context_snoc, plus_0_r in IHb'.
    apply IHb'. reflexivity.

  - eapply refine_type. 1: econstructor; auto.
    now rewrite -> distr_lift_subst10.

  - erewrite lift_declared_symbol by eassumption.
    econstructor. all: eauto.

  - autorewrite with lift.
    rewrite -> map_cst_type. constructor; auto.
    erewrite <- lift_declared_constant; eauto.

  - autorewrite with lift.
    erewrite <- (ind_type_map (fun k' => lift #|Γ''| (k' + #|Γ'|))).
    pose proof isdecl as isdecl'.
    destruct isdecl. intuition auto.
    eapply lift_declared_inductive in isdecl'. 2: auto.
    rewrite -> isdecl'.
    econstructor; try red; intuition eauto.

  - rewrite (lift_declared_constructor _ (ind, i) u mdecl idecl cdecl _ _ wfΣ isdecl).
    econstructor; eauto.

  - rewrite -> lift_mkApps, map_app, map_skipn.
    specialize (IHc _ _ _ wf eq_refl).
    specialize (IHp _ _ _ wf eq_refl).
    assert (Hclos: closed_ctx (subst_instance_context u (ind_params mdecl))). {
      destruct isdecl as [Hmdecl Hidecl].
      eapply on_declared_minductive in Hmdecl; eauto.
      eapply onParams in Hmdecl.
      rewrite closedn_subst_instance_context.
      eapply closed_wf_local in Hmdecl; eauto. }
    simpl. econstructor.
    7:{ cbn. rewrite -> firstn_map.
        erewrite lift_build_branches_type; tea.
        rewrite map_option_out_map_option_map.
        subst params. erewrite heq_map_option_out. reflexivity. }
    all: eauto.
    -- erewrite -> lift_declared_inductive; eauto.
    -- simpl. erewrite firstn_map, lift_build_case_predicate_type; tea.
       subst params. erewrite heq_build_case_predicate_type; reflexivity.
    -- destruct idecl; simpl in *; auto.
    -- now rewrite -> !lift_mkApps in IHc.
    -- solve_all.

  - simpl.
    erewrite (distr_lift_subst_rec _ _ _ 0 #|Γ'|).
    simpl. rewrite -> map_rev.
    subst ty.
    rewrite -> List.rev_length, lift_subst_instance_constr.
    replace (lift #|Γ''| (S (#|args| + #|Γ'|)) (snd pdecl))
      with (snd (on_snd (lift #|Γ''| (S (#|args| + #|Γ'|))) pdecl)) by now destruct pdecl.
    econstructor.
    + red. split.
      * apply (proj1 isdecl).
      * split.
        -- rewrite -> (proj1 (proj2 isdecl)). f_equal.
           rewrite -> heq_length.
           symmetry. eapply lift_declared_projection; eauto.
        -- apply (proj2 (proj2 isdecl)).
    + specialize (IHc _ _ _ wf eq_refl).
      rewrite -> lift_mkApps in *. eapply IHc.
    + now rewrite -> map_length.

  - rewrite -> (map_dtype _ (lift #|Γ''| (#|mfix| + #|Γ'|))).
    assert (wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' ,,, lift_context #|Γ''| #|Γ'| (fix_context mfix))).
    + subst types.
      apply All_local_env_app in X as [X Hfixc].
      apply All_local_env_app_inv. intuition.
      revert Hfixc. clear X0 X heq_nth_error.
      induction 1; simpl; auto; try constructor; rewrite -> lift_context_snoc.
      * econstructor; auto.
        destruct t0 as [u [Ht IHt]].
        specialize (IHt Γ (Γ' ,,, Γ0) Γ'').
        forward IHt.
        { apply All_local_env_app in wf.
          apply All_local_env_app_inv. intuition.
          rewrite -> lift_context_app.
          apply All_local_env_app_inv. intuition.
          rewrite -> Nat.add_0_r. eapply All_local_env_impl; eauto.
          intros.
          now unfold app_context in *; rewrite <- app_assoc.
        }
        rewrite -> lift_context_app, Nat.add_0_r in IHt.
        unfold app_context in *. rewrite <- !app_assoc, app_length in IHt.
        specialize (IHt eq_refl). simpl. exists u. apply IHt.
      * destruct t0 as [u [Ht IHt]]. destruct t1 as [Ht' IHt'].
        specialize (IHt Γ (Γ' ,,, Γ0) Γ'').
        forward IHt.
        { apply All_local_env_app in wf.
          apply All_local_env_app_inv. intuition.
          rewrite -> lift_context_app.
          apply All_local_env_app_inv. intuition.
          rewrite -> Nat.add_0_r. eapply All_local_env_impl; eauto. intros.
          now unfold app_context in *; rewrite <- app_assoc.
        }
        specialize (IHt' Γ (Γ' ,,, Γ0) Γ'').
        forward IHt'.
        { apply All_local_env_app in wf.
          apply All_local_env_app_inv. intuition.
          rewrite -> lift_context_app.
          apply All_local_env_app_inv. intuition.
          rewrite -> Nat.add_0_r. eapply All_local_env_impl; eauto. intros.
          now unfold app_context in *; rewrite <- app_assoc.
        }
        constructor; auto.
        -- simpl. eexists.
           rewrite -> lift_context_app, Nat.add_0_r in IHt.
           unfold app_context in *. rewrite <- !app_assoc, app_length in IHt.
           specialize (IHt eq_refl). simpl. apply IHt.
        -- simpl. rewrite -> lift_context_app, Nat.add_0_r in IHt'.
           unfold app_context in *. rewrite <- !app_assoc, app_length in IHt'.
           specialize (IHt' eq_refl). simpl. apply IHt'.
    + eapply type_Fix.
      * eapply fix_guard_lift ; eauto.
      * rewrite -> nth_error_map, heq_nth_error. reflexivity.
      * now rewrite -> lift_fix_context.
      * rewrite -> lift_fix_context.
        apply All_map.
        clear X. eapply All_impl; eauto.
        clear X0. unfold Basics.compose; simpl; intros [na ty bod] [[Htyd Hlam] IH].
        simpl in *. intuition.
        specialize (IH Γ (Γ' ,,, fix_context mfix) Γ'').
        rewrite -> lift_context_app in IH.
        rewrite -> !app_context_assoc, Nat.add_0_r, !app_context_length, fix_context_length in IH.
        specialize (IH X1 eq_refl).
        rewrite -> permute_lift, lift_context_length, fix_context_length by lia.
        subst types; rewrite -> fix_context_length in IH.
        rewrite (Nat.add_comm #|Γ'|). apply IH.

  - assert (wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' ,,, lift_context #|Γ''| #|Γ'| (fix_context mfix))).
    { subst types.
      apply All_local_env_app in X as [X Hfixc].
      apply All_local_env_app_inv. intuition.
      revert Hfixc. clear X0 X.
      induction 1; simpl; auto; try constructor; rewrite -> lift_context_snoc.
      - econstructor; auto.
        destruct t0 as [u [Ht IHt]].
        specialize (IHt Γ (Γ' ,,, Γ0) Γ'').
        forward IHt.
        { apply All_local_env_app in wf.
          apply All_local_env_app_inv. intuition.
          rewrite -> lift_context_app.
          apply All_local_env_app_inv. intuition.
          rewrite -> Nat.add_0_r. eapply All_local_env_impl; eauto. intros.
          now unfold app_context in *; rewrite <- app_assoc.
        }
        rewrite -> lift_context_app, Nat.add_0_r in IHt.
        unfold app_context in *. rewrite <- !app_assoc, app_length in IHt.
        specialize (IHt eq_refl). exists u; apply IHt.
      - destruct t0 as [u [Ht IHt]].
        specialize (IHt Γ (Γ' ,,, Γ0) Γ''). forward IHt.
        { apply All_local_env_app in wf.
          apply All_local_env_app_inv. intuition.
          rewrite -> lift_context_app.
          apply All_local_env_app_inv. intuition.
          rewrite -> Nat.add_0_r. eapply All_local_env_impl; eauto. intros.
          now unfold app_context in *; rewrite <- app_assoc.
        }
        destruct t1 as [Ht' IHt'].
        specialize (IHt' Γ (Γ' ,,, Γ0) Γ'').
        forward IHt'.
        { apply All_local_env_app in wf.
          apply All_local_env_app_inv. intuition.
          rewrite -> lift_context_app.
          apply All_local_env_app_inv. intuition.
          rewrite -> Nat.add_0_r. eapply All_local_env_impl; eauto. intros.
          now unfold app_context in *; rewrite <- app_assoc.
        }
        constructor; auto.
        + simpl. eexists. rewrite -> lift_context_app, Nat.add_0_r in IHt.
          unfold app_context in *. rewrite <- !app_assoc, app_length in IHt.
          specialize (IHt eq_refl). simpl. apply IHt.
        + simpl. rewrite -> lift_context_app, Nat.add_0_r in IHt'.
          unfold app_context in *. rewrite <- !app_assoc, app_length in IHt'.
          specialize (IHt' eq_refl). simpl. apply IHt'.
    }
    rewrite -> (map_dtype _ (lift #|Γ''| (#|mfix| + #|Γ'|))).
    eapply type_CoFix.
    + assumption.
    + now rewrite -> nth_error_map, heq_nth_error.
    + now rewrite -> lift_fix_context.
    + rewrite -> lift_fix_context.
      apply All_map.
      clear X. eapply All_impl; eauto.
      clear X0. unfold compose; simpl; intros [na ty bod] [Htyd IH].
      simpl in *. intuition.
      specialize (IH Γ (Γ' ,,, fix_context mfix) Γ'').
      rewrite -> lift_context_app in IH.
      rewrite -> !app_context_assoc, Nat.add_0_r, !app_context_length, fix_context_length in IH.
      specialize (IH X1 eq_refl).
      rewrite -> permute_lift, lift_context_length, fix_context_length by lia.
      subst types; rewrite -> fix_context_length in IH.
      rewrite (Nat.add_comm #|Γ'|).
      apply IH.

  - econstructor; eauto.
    + destruct IHB.
      * left. destruct i as [[ctx [u [Hd IH]]]]. simpl in *.
        exists (lift_context #|Γ''| #|Γ'| ctx), u.
        rewrite (lift_destArity [] B #|Γ''| #|Γ'|) Hd.
        split; auto.
        apply All_local_env_app_inv; intuition auto.
        clear -wf a.
        induction ctx; try constructor; depelim a.
        -- rewrite lift_context_snoc. unfold vass, snoc in H. noconf H.
           constructor; auto.
           ++ eapply IHctx. eapply a.
           ++ simpl. destruct tu as [u tu]. exists u.
              specialize (t0 Γ (Γ' ,,, ctx) Γ'').
              forward t0.
              { rewrite lift_context_app app_context_assoc Nat.add_0_r.
                apply All_local_env_app_inv. split; auto.
                eapply IHctx. eapply a.
              }
              rewrite app_context_assoc in t0.
              specialize (t0 eq_refl). simpl in t0.
              rewrite app_context_length lift_context_app app_context_assoc Nat.add_0_r in t0.
              apply t0.
        -- rewrite lift_context_snoc. unfold vass, snoc in H; noconf H.
           constructor; auto.
            ++ eapply IHctx. eapply a.
            ++ simpl.
               specialize (t1 Γ (Γ' ,,, ctx) Γ'').
               forward t1.
               { rewrite lift_context_app app_context_assoc Nat.add_0_r.
                 apply All_local_env_app_inv. split; auto.
                 eapply IHctx. eapply a.
               }
               rewrite app_context_assoc in t1.
               specialize (t1 eq_refl). simpl in t1.
               rewrite app_context_length lift_context_app app_context_assoc Nat.add_0_r in t1.
               eexists. apply t1.
            ++ simpl.
               specialize (t0 Γ (Γ' ,,, ctx) Γ''). forward t0.
               { rewrite lift_context_app app_context_assoc Nat.add_0_r.
                 apply All_local_env_app_inv. split; auto.
                 eapply IHctx. eapply a.
               }
               rewrite app_context_assoc in t0.
               specialize (t0 eq_refl). simpl in t0.
               rewrite app_context_length lift_context_app app_context_assoc Nat.add_0_r in t0.
               apply t0.
      * right. destruct s as [u Hu]; exists u.
        intuition; now eapply weakening_cumul.
    + now eapply weakening_cumul.
Qed.

Lemma weakening `{cf : checker_flags} Σ Γ Γ' (t : term) T :
  wf Σ.1 -> wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T.
Proof.
  intros HΣ HΓΓ' * H.
  pose (weakening_typing Σ Γ [] Γ' t).
  forward t0; eauto.
  forward t0; eauto. now eapply wf_local_app in HΓΓ'.
Qed.

(** Variant with more freedom on the length to apply it in backward-chainings. *)
Lemma weakening_length {cf:checker_flags} Σ Γ Γ' t T n :
  wf Σ.1 ->
  n = #|Γ'| ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- (lift0 n) t : (lift0 n) T.
Proof. intros wfΣ ->; now apply weakening. Qed.

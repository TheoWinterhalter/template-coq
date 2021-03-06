(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".
Require Import ssreflect ssrbool.
From Coq Require Import Bool List Utf8 ZArith Lia Morphisms String
  Sorting.Permutation.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSize
  PCUICLiftSubst PCUICSigmaCalculus PCUICUnivSubst PCUICTyping PCUICReduction
  PCUICSubstitution PCUICReflect PCUICClosed PCUICParallelReduction
  PCUICPattern PCUICInduction PCUICRW PCUICPredExtra.

Require Import monad_utils.
Import MonadNotation.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Derive Signature for pred1 All2_local_env.

Local Set Keyed Unification.
Set Asymmetric Patterns.

Ltac solve_discr := (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
  try discriminate.

Lemma simpl_pred Σ Γ Γ' t t' u u' : t = t' -> u = u' -> pred1 Σ Γ Γ' t' u' -> pred1 Σ Γ Γ' t u.
Proof. now intros -> ->. Qed.

Ltac simpl_pred :=
  eapply simpl_pred;
  rewrite ?up_Upn;
  unfold Upn, Up, idsn;
  [autorewrite with sigma; reflexivity|
    autorewrite with sigma; reflexivity|].

Lemma pred_atom_inst t σ : pred_atom t -> t.[σ] = t.
Proof.
  destruct t; simpl; intros; try discriminate; auto.
Qed.

Lemma mfixpoint_size_In {mfix d} :
  In d mfix ->
  size (dbody d) < mfixpoint_size size mfix /\
  size (dtype d) < mfixpoint_size size mfix.
Proof.
  induction mfix in d |- *; simpl; auto. 1: intros [].
  move=> [->|H].
  - unfold def_size. split; lia.
  - destruct (IHmfix d H). split; lia.
Qed.

Lemma mfixpoint_size_nth_error {mfix i d} :
  nth_error mfix i = Some d ->
  size (dbody d) < mfixpoint_size size mfix.
Proof.
  induction mfix in i, d |- *; destruct i; simpl; try congruence.
  - move=> [] ->. unfold def_size. lia.
  - move/IHmfix. lia.
Qed.

Section FoldFix.
  Context (rho : context -> term -> term).
  Context (Γ : context).

  Fixpoint fold_fix_context acc m :=
    match m with
  | [] => acc
    | def :: fixd =>
      fold_fix_context (vass def.(dname) (lift0 #|acc| (rho Γ def.(dtype))) :: acc) fixd
    end.
End FoldFix.

Lemma fold_fix_context_length f Γ l m : #|fold_fix_context f Γ l m| = #|m| + #|l|.
Proof.
  induction m in l |- *; simpl; auto. rewrite IHm. simpl. auto with arith.
Qed.

Fixpoint isFixLambda_app (t : term) : bool :=
match t with
| tApp (tFix _ _) _ => true
| tApp (tLambda _ _ _) _ => true
| tApp f _ => isFixLambda_app f
| _ => false
end.

Inductive fix_lambda_app_view : term -> term -> Type :=
| fix_lambda_app_fix mfix i l a : fix_lambda_app_view (mkApps (tFix mfix i) l) a
| fix_lambda_app_lambda na ty b l a : fix_lambda_app_view (mkApps (tLambda na ty b) l) a
| fix_lambda_app_other t a : ~~ isFixLambda_app (tApp t a) -> fix_lambda_app_view t a.
Derive Signature for fix_lambda_app_view.

Lemma view_lambda_fix_app (t u : term) : fix_lambda_app_view t u.
Proof.
  induction t; try solve [apply fix_lambda_app_other; simpl; auto].
  - apply (fix_lambda_app_lambda na t1 t2 [] u).
  - destruct IHt1.
    + pose proof (fix_lambda_app_fix mfix i (l ++ [t2]) a).
      change (tApp (mkApps (tFix mfix i) l) t2) with (mkApps (mkApps (tFix mfix i) l) [t2]).
      now rewrite mkApps_nested.
    + pose proof (fix_lambda_app_lambda na ty b (l ++ [t2]) a).
      change (tApp (mkApps (tLambda na ty b) l) t2) with (mkApps (mkApps (tLambda na ty b) l) [t2]).
      now rewrite mkApps_nested.
    + destruct t; try solve [apply fix_lambda_app_other; simpl; auto].
  - apply (fix_lambda_app_fix mfix idx [] u).
Defined.

Lemma eq_pair_transport {A B} (x y : A) (t : B y) (eq : x = y) :
  (x; eq_rect_r (fun x => B x) t eq) = (y; t) :> ∑ x, B x.
Proof.
  destruct eq. unfold eq_rect_r. now simpl.
Qed.

Lemma view_lambda_fix_app_fix_app_sigma mfix idx l a :
  ((mkApps (tFix mfix idx) l); view_lambda_fix_app (mkApps (tFix mfix idx) l) a) =
  ((mkApps (tFix mfix idx) l); fix_lambda_app_fix mfix idx l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite -{1 2}mkApps_nested.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tFix mfix idx) l) x) with (mkApps (mkApps (tFix mfix idx) l) [x]).
  now rewrite eq_pair_transport.
Qed.

Lemma view_lambda_fix_app_lambda_app_sigma na ty b l a :
  ((mkApps (tLambda na ty b) l); view_lambda_fix_app (mkApps (tLambda na ty b) l) a) =
  ((mkApps (tLambda na ty b) l); fix_lambda_app_lambda na ty b l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite -{1 2}mkApps_nested.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tLambda na ty b) l) x) with (mkApps (mkApps (tLambda na ty b) l) [x]).
  now rewrite eq_pair_transport.
Qed.

Set Equations With UIP.

Lemma view_lambda_fix_app_fix_app mfix idx l a :
  view_lambda_fix_app (mkApps (tFix mfix idx) l) a =
  fix_lambda_app_fix mfix idx l a.
Proof.
  pose proof (view_lambda_fix_app_fix_app_sigma mfix idx l a).
  now noconf H.
Qed.

Lemma view_lambda_fix_app_lambda_app na ty b l a :
  view_lambda_fix_app (mkApps (tLambda na ty b) l) a =
  fix_lambda_app_lambda na ty b l a.
Proof.
  pose proof (view_lambda_fix_app_lambda_app_sigma na ty b l a).
  now noconf H.
Qed.

Hint Rewrite view_lambda_fix_app_fix_app view_lambda_fix_app_lambda_app : rho.

Equations construct_cofix_discr (t : term) : bool :=
construct_cofix_discr (tConstruct _ _ _) => true;
construct_cofix_discr (tCoFix _ _) => true;
construct_cofix_discr _ => false.
Transparent construct_cofix_discr.

Equations discr_construct_cofix (t : term) : Prop :=
  { | tConstruct _ _ _ => False;
    | tCoFix _ _ => False;
    | _ => True }.
Transparent discr_construct_cofix.

Inductive construct_cofix_view : term -> Type :=
| construct_cofix_construct c u i : construct_cofix_view (tConstruct c u i)
| construct_cofix_cofix mfix idx : construct_cofix_view (tCoFix mfix idx)
| construct_cofix_other t : discr_construct_cofix t -> construct_cofix_view t.

Equations view_construct_cofix (t : term) : construct_cofix_view t :=
{ | tConstruct ind u i => construct_cofix_construct ind u i;
  | tCoFix mfix idx => construct_cofix_cofix mfix idx;
  | t => construct_cofix_other t I }.

(** This induction principle gives a general induction hypothesis for applications,
    allowing to apply the induction to their head. *)
Lemma term_ind_size_app :
  forall (P : term -> Type),
    (forall (n : nat), P (tRel n)) ->
    (forall (i : ident), P (tVar i)) ->
    (forall (n : nat) (l : list term), All (P) l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 ->
                                                   P (tLetIn n t t0 t1)) ->
    (forall (t u : term),
        (forall t', size t' < size (tApp t u) -> P t') ->
        P t -> P u -> P (tApp t u)) ->
    (forall (s : kername) (n : nat) (u : list Level.t), P (tSymb s n u)) ->
    (forall s (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall t0 : term, P t0 -> forall l : list (nat * term),
            tCaseBrsProp (P) l -> P (tCase p t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat),
        tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat),
        tFixProp (P) P m -> P (tCoFix m n)) ->
    forall (t : term), P t.
Proof.
  intros.
  revert t. set(foo:=CoreTactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (precompose lt size). simpl. clear H0.
  assert (auxl : forall {A} (l : list A) (f : A -> term), list_size (fun x => size (f x)) l < size pr1 ->
                                                            All (fun x => P (f x)) l).
  { induction l; constructor.
    - eapply aux. red. simpl in H. lia.
    - apply IHl. simpl in H. lia.
  }
  assert (forall m, list_size (fun x : def term => size (dtype x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m.
    - simpl. auto.
    - simpl. lia.
  }
  assert (forall m, list_size (fun x : def term => size (dbody x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m.
    - simpl. auto.
    - simpl. lia.
  }

  move aux at top. move auxl at top.

  !destruct pr1; eauto;
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); red; simpl; try lia]
        end.

  - eapply X13; try (apply aux; red; simpl; lia).
    red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X14; try (apply aux; red; simpl; lia).
    red. apply All_pair. split; apply auxl; simpl; auto.
Defined.

Lemma fix_context_gen_assumption_context k Γ :
  assumption_context (fix_context_gen k Γ).
Proof.
  rewrite /fix_context_gen. revert k.
  induction Γ using rev_ind. 1: constructor.
  intros.
  rewrite mapi_rec_app /= List.rev_app_distr /=. constructor.
  apply IHΓ.
Qed.

Lemma fix_context_assumption_context m : assumption_context (fix_context m).
Proof. apply fix_context_gen_assumption_context. Qed.

Lemma nth_error_assumption_context Γ n d :
  assumption_context Γ -> nth_error Γ n = Some d ->
  decl_body d = None.
Proof.
  intros H; induction H in n, d |- * ; destruct n; simpl; try congruence; eauto.
  now move=> [<-] //.
Qed.

Lemma decompose_app_rec_rename r t l :
  forall hd args,
  decompose_app_rec t l = (hd, args) ->
  decompose_app_rec (rename r t) (map (rename r) l) = (rename r hd, map (rename r) args).
Proof.
  induction t in l |- *; simpl; try intros hd args [= <- <-]; auto.
  intros hd args e. now apply (IHt1 _ _ _ e).
Qed.

Lemma decompose_app_rename {r t hd args} :
  decompose_app t = (hd, args) ->
  decompose_app (rename r t) = (rename r hd, map (rename r) args).
Proof. apply decompose_app_rec_rename. Qed.

Lemma mkApps_eq_decompose_app {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  decompose_app_rec t l = decompose_app_rec t' l'.
Proof.
  induction l in t, t', l' |- *; simpl.
  - intros ->. rewrite !decompose_app_rec_mkApps.
    now rewrite app_nil_r.
  - intros H. apply (IHl _ _ _ H).
Qed.


Lemma atom_mkApps {t l} : atom (mkApps t l) -> atom t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). discriminate.
Qed.

Lemma pred_atom_mkApps {t l} : pred_atom (mkApps t l) -> pred_atom t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). discriminate.
Qed.

Ltac finish_discr :=
  repeat PCUICAstUtils.finish_discr ||
         match goal with
         | [ H : atom (mkApps _ _) |- _ ] => apply atom_mkApps in H; intuition subst
         | [ H : pred_atom (mkApps _ _) |- _ ] => apply pred_atom_mkApps in H; intuition subst
         end.

Definition application_atom t :=
  match t with
  | tVar _
  | tSort _
  | tInd _ _
  | tConstruct _ _ _
  | tLambda _ _ _ => true
  | _ => false
  end.

Lemma application_atom_mkApps {t l} : application_atom (mkApps t l) -> application_atom t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). discriminate.
Qed.

Ltac solve_discr ::=
  (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
  (try (match goal with
        | [ H : is_true (application_atom _) |- _ ] => discriminate
        | [ H : is_true (atom _) |- _ ] => discriminate
        | [ H : is_true (atom (mkApps _ _)) |- _ ] => destruct (atom_mkApps H); subst; try discriminate
        | [ H : is_true (pred_atom _) |- _ ] => discriminate
        | [ H : is_true (pred_atom (mkApps _ _)) |- _ ] => destruct (pred_atom_mkApps H); subst; try discriminate
        | [ H : is_true (application_atom (mkApps _ _)) |- _ ] =>
          destruct (application_atom_mkApps H); subst; try discriminate
        end)).

Lemma is_constructor_app_ge n l l' : is_constructor n l -> is_constructor n (l ++ l').
Proof.
  unfold is_constructor. destruct nth_error eqn:Heq. 2: discriminate.
  rewrite nth_error_app_lt ?Heq //; eauto using nth_error_Some_length.
Qed.

Lemma is_constructor_prefix n args args' :
  ~~ is_constructor n (args ++ args') ->
  ~~ is_constructor n args.
Proof.
  rewrite /is_constructor.
  elim: nth_error_spec.
  - rewrite app_length.
    move=> i hi harg. elim: nth_error_spec.
    + move=> i' hi' hrarg'.
      rewrite nth_error_app_lt in hi; eauto. congruence.
    + auto.
  - rewrite app_length. move=> ge _.
    elim: nth_error_spec; intros; try lia. auto.
Qed.


Section Pred1_inversion.

  Lemma pred_snd_nth:
    ∀ (Σ : global_env) (Γ Δ : context) (c : nat) (brs1 brs' : list (nat * term)),
      All2
        (on_Trel (pred1 Σ Γ Δ) snd) brs1
        brs' ->
        pred1_ctx Σ Γ Δ ->
      pred1 Σ Γ Δ
              (snd (nth c brs1 (0, tDummy)))
              (snd (nth c brs' (0, tDummy))).
  Proof.
    intros Σ Γ Δ c brs1 brs' brsl. intros.
    induction brsl in c |- *; simpl.
    - destruct c; now apply pred1_refl_gen.
    - destruct c; auto.
  Qed.

  Lemma pred_mkApps Σ Γ Δ M0 M1 N0 N1 :
    pred1 Σ Γ Δ M0 M1 ->
    All2 (pred1 Σ Γ Δ) N0 N1 ->
    pred1 Σ Γ Δ (mkApps M0 N0) (mkApps M1 N1).
  Proof.
    intros.
    induction X0 in M0, M1, X |- *. 1: auto.
    simpl. eapply IHX0. now eapply pred_app.
  Qed.

  Lemma isAppSymb_subst :
    forall t s k,
      isAppSymb t ->
      isAppSymb (subst s k t).
  Proof.
    intros t s k h.
    induction t. all: try discriminate.
    - cbn in *. eapply IHt1. assumption.
    - cbn. reflexivity.
  Qed.

  Lemma pred1_mkApps_tConstruct `{cf : checker_flags} (Σ : global_env) (Γ Δ : context)
        ind pars k (args : list term) c :
    wf Σ ->
    pred1 Σ Γ Δ (mkApps (tConstruct ind pars k) args) c ->
    {args' : list term & (c = mkApps (tConstruct ind pars k) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    intro wfΣ.
    revert c.
    induction args using rev_ind; intros; simpl in *.
    - remember (tConstruct _ _ _) as lt. revert Heqlt.
      induction X. all: try discriminate. all: intros et. all: solve_discr.
      + exfalso. apply (f_equal isElimSymb) in et.
        cbn in et.
        eapply diff_false_true. rewrite <- et.
        eapply isElimSymb_subst. apply untyped_subslet_length in u.
        rewrite subst_context_length in u. rewrite u.
        eapply isElimSymb_lhs.
        eapply declared_symbol_head in d. all: eauto.
      + exfalso. apply (f_equal isElimSymb) in et.
        cbn in et.
        eapply diff_false_true. rewrite <- et.
        eapply isElimSymb_subst. apply untyped_subslet_length in u.
        rewrite subst_context_length in u. rewrite u.
        eapply isElimSymb_lhs.
        eapply declared_symbol_par_head in d. all: eauto.
      + exists []. intuition auto.
    - intros. rewrite <- mkApps_nested in X. cbn in X.
      remember (tApp _ _) as lt. revert Heqlt.
      induction X. all: try discriminate. all: intros et. all: solve_discr.
      + simpl in et. noconf et. hnf in H. noconf H. solve_discr.
      + prepare_discr. apply mkApps_eq_decompose_app in et.
        rewrite !decompose_app_rec_mkApps in et. noconf et.
      + exfalso. apply (f_equal isElimSymb) in et.
        cbn in et. rewrite isElimSymb_mkApps in et. cbn in et.
        eapply diff_false_true. rewrite <- et.
        eapply isElimSymb_subst. apply untyped_subslet_length in u.
        rewrite subst_context_length in u. rewrite u.
        eapply isElimSymb_lhs.
        eapply declared_symbol_head in d. all: eauto.
      + exfalso. apply (f_equal isElimSymb) in et.
        cbn in et. rewrite isElimSymb_mkApps in et. cbn in et.
        eapply diff_false_true. rewrite <- et.
        eapply isElimSymb_subst. apply untyped_subslet_length in u.
        rewrite subst_context_length in u. rewrite u.
        eapply isElimSymb_lhs.
        eapply declared_symbol_par_head in d. all: eauto.
      + noconf et.
        destruct (IHargs _ X1) as [args' [-> Hargs']].
        exists (args' ++ [N1])%list.
        rewrite <- mkApps_nested. intuition auto.
        eapply All2_app; auto.
      + subst. solve_discr.
  Qed.

  Lemma pred1_mkApps_refl_tConstruct `{checker_flags} (Σ : global_env) Γ Δ i k u l l' :
    wf Σ ->
    pred1 Σ Γ Δ (mkApps (tConstruct i k u) l) (mkApps (tConstruct i k u) l') ->
    All2 (pred1 Σ Γ Δ) l l'.
  Proof.
    intros wfΣ X.
    eapply pred1_mkApps_tConstruct in X. 2: auto.
    destruct X.
    destruct p. now eapply mkApps_eq_inj in e as [_ <-].
  Qed.

  Lemma pred1_mkApps_tInd `{cf : checker_flags} (Σ : global_env) (Γ Δ : context)
        ind u (args : list term) c :
    wf Σ ->
    pred1 Σ Γ Δ (mkApps (tInd ind u) args) c ->
    {args' : list term & (c = mkApps (tInd ind u) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    intro wfΣ.
    revert c. induction args using rev_ind; intros; simpl in *.
    - generalize_by_eqs X. destruct X.
      all: try subst lhs rhs.
      all: simplify_dep_elim.
      all: try solve_discr.
      + exfalso.
        apply diff_false_true.
        apply (f_equal isElimSymb) in H.
        cbn in H.
        rewrite H.
        apply isElimSymb_subst.
        apply untyped_subslet_length in u0.
        rewrite u0. rewrite subst_context_length.
        eapply isElimSymb_lhs.
        eapply declared_symbol_head. all: eauto.
      + exfalso.
        apply diff_false_true.
        apply (f_equal isElimSymb) in H.
        cbn in H.
        rewrite H.
        apply isElimSymb_subst.
        apply untyped_subslet_length in u0.
        rewrite u0. rewrite subst_context_length.
        eapply isElimSymb_lhs.
        eapply declared_symbol_par_head. all: eauto.
      + exists []. intuition auto.
    - intros. rewrite <- mkApps_nested in X.
      generalize_by_eqs X. destruct X.
      all: try subst lhs rhs.
      all: simplify_dep_elim.
      all: try solve_discr.
      + simpl in H; noconf H. solve_discr.
      + prepare_discr. apply mkApps_eq_decompose_app in H.
        rewrite !decompose_app_rec_mkApps in H. noconf H.
      + exfalso.
        apply diff_false_true.
        apply (f_equal isElimSymb) in H.
        cbn in H. rewrite isElimSymb_mkApps in H. cbn in H.
        rewrite H.
        apply isElimSymb_subst.
        apply untyped_subslet_length in u0.
        rewrite u0. rewrite subst_context_length.
        eapply isElimSymb_lhs.
        eapply declared_symbol_head. all: eauto.
      + exfalso.
        apply diff_false_true.
        apply (f_equal isElimSymb) in H.
        cbn in H. rewrite isElimSymb_mkApps in H. cbn in H.
        rewrite H.
        apply isElimSymb_subst.
        apply untyped_subslet_length in u0.
        rewrite u0. rewrite subst_context_length.
        eapply isElimSymb_lhs.
        eapply declared_symbol_par_head. all: eauto.
      + destruct (IHargs _ X1) as [args' [-> Hargs']].
        exists (args' ++ [N1])%list.
        rewrite <- mkApps_nested. intuition auto.
        eapply All2_app; auto.
  Qed.

  (* This lemma is from the master branch of MetaCoq used in file
    PCUICConfluence.v and needs to be updated to take rewrite rules into
    account, but it is not used for the proofs of confluence and subject
    reduction.
  *)
  Lemma pred1_mkApps_tConst_axiom (Σ : global_env) (Γ Δ : context)
        cst u (args : list term) cb c :
    declared_constant Σ cst cb -> cst_body cb = None ->
    pred1 Σ Γ Δ (mkApps (tConst cst u) args) c ->
    {args' : list term & (c = mkApps (tConst cst u) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    - depelim X...
      + (* TODO Rewrite rules *) admit.
      + (* TODO Rewrite rules *) admit.
      + red in H, isdecl. rewrite isdecl in H; noconf H.
        simpl in H. injection H. intros. subst. congruence.
      + exists []. intuition auto.
    - rewrite <- mkApps_nested in X.
      depelim X...
      + simpl in H1; noconf H1. solve_discr.
      + prepare_discr. apply mkApps_eq_decompose_app in H1.
        rewrite !decompose_app_rec_mkApps in H1. noconf H1.
      + (* TODO Rewrite rules *) admit.
      + (* TODO Rewrite rules *) admit.
      + destruct (IHargs _ H H0 X1) as [args' [-> Hargs']].
        exists (args' ++ [N1])%list.
        rewrite <- mkApps_nested. intuition auto.
        eapply All2_app; auto.
  (* Qed. *)
  Admitted.

  Lemma pred1_mkApps_tFix_inv `{cf : checker_flags} Σ (Γ Δ : context)
        mfix0 idx (args0 : list term) c d :
    wf Σ ->
    nth_error mfix0 idx = Some d ->
    ~~ is_constructor (rarg d) args0 ->
    pred1 Σ Γ Δ (mkApps (tFix mfix0 idx) args0) c ->
    ({ mfix1 & { args1 : list term &
                         (c = mkApps (tFix mfix1 idx) args1) *
                         All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                                       dtype dbody
                                    (fun x => (dname x, rarg x))
                                    (pred1 Σ) mfix0 mfix1 *
                         (All2 (pred1 Σ Γ Δ) ) args0 args1 } }%type).
  Proof with solve_discr.
    intros wfΣ hnth isc pred. remember (mkApps _ _) as fixt.
    revert mfix0 idx args0 Heqfixt hnth isc.
    induction pred; intros; solve_discr.
    - unfold PCUICTyping.unfold_fix in e.
      red in a1.
      eapply All2_nth_error_Some in a1; eauto.
      destruct a1 as [t' [ht' [hds [hr [= eqna eqrarg]]]]].
      rewrite ht' in e => //. noconf e. rewrite -eqrarg in e0.
      rewrite e0 in isc => //.
    - exfalso. apply (f_equal isElimSymb) in Heqfixt.
      rewrite isElimSymb_mkApps in Heqfixt. cbn in Heqfixt.
      eapply diff_false_true. rewrite <- Heqfixt.
      eapply isElimSymb_subst. apply untyped_subslet_length in u.
      rewrite subst_context_length in u. rewrite u.
      eapply isElimSymb_lhs.
      eapply declared_symbol_head in d0. all: eauto.
    - exfalso. apply (f_equal isElimSymb) in Heqfixt.
      rewrite isElimSymb_mkApps in Heqfixt. cbn in Heqfixt.
      eapply diff_false_true. rewrite <- Heqfixt.
      eapply isElimSymb_subst. apply untyped_subslet_length in u.
      rewrite subst_context_length in u. rewrite u.
      eapply isElimSymb_lhs.
      eapply declared_symbol_par_head in d0. all: eauto.
    - destruct args0 using rev_ind. 1: noconf Heqfixt.
      clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2. specialize (IHpred1 _ _ _ eq_refl).
      specialize (IHpred1 hnth). apply is_constructor_prefix in isc.
      specialize (IHpred1 isc).
      destruct IHpred1 as [? [? [[? ?] ?]]].
      eexists _. eexists (_ ++ [N1])%list. rewrite <- mkApps_nested.
      intuition eauto.
      + simpl. subst M1. reflexivity.
      + eapply All2_app; eauto.
    - exists mfix1, []. intuition auto.
    - subst t. solve_discr.
  Qed.

  Lemma pred1_mkApps_tFix_refl_inv `{cf : checker_flags} (Σ : global_env) (Γ Δ : context)
        mfix0 mfix1 idx0 idx1 (args0 args1 : list term) d :
    wf Σ ->
    nth_error mfix0 idx0 = Some d ->
    is_constructor (rarg d) args0 = false ->
    pred1 Σ Γ Δ (mkApps (tFix mfix0 idx0) args0) (mkApps (tFix mfix1 idx1) args1) ->
    (All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                   dtype dbody
                   (fun x => (dname x, rarg x))
                   (pred1 Σ) mfix0 mfix1 *
     (All2 (pred1 Σ Γ Δ) ) args0 args1).
  Proof with solve_discr.
    intros wfΣ Hnth Hisc.
    remember (mkApps _ _) as fixt.
    remember (mkApps _ args1) as fixt'.
    intros pred. revert mfix0 mfix1 idx0 args0 d Hnth Hisc idx1 args1 Heqfixt Heqfixt'.
    induction pred; intros; solve_discr.
    - (* Not reducible *)
      red in a1. eapply All2_nth_error_Some in a1; eauto.
      destruct a1 as [t' [Hnth' [Hty [Hpred Hann]]]].
      unfold unfold_fix in e. destruct (nth_error mfix1 idx) eqn:hfix1.
      + noconf e. noconf Hnth'.
        move: Hann => [=] Hname Hrarg.
        congruence.
      + congruence.

    - exfalso. apply (f_equal isElimSymb) in Heqfixt.
      rewrite isElimSymb_mkApps in Heqfixt. cbn in Heqfixt.
      eapply diff_false_true. rewrite <- Heqfixt.
      eapply isElimSymb_subst. apply untyped_subslet_length in u.
      rewrite subst_context_length in u. rewrite u.
      eapply isElimSymb_lhs.
      eapply declared_symbol_head in d. all: eauto.
    - exfalso. apply (f_equal isElimSymb) in Heqfixt.
      rewrite isElimSymb_mkApps in Heqfixt. cbn in Heqfixt.
      eapply diff_false_true. rewrite <- Heqfixt.
      eapply isElimSymb_subst. apply untyped_subslet_length in u.
      rewrite subst_context_length in u. rewrite u.
      eapply isElimSymb_lhs.
      eapply declared_symbol_par_head in d. all: eauto.

    - destruct args0 using rev_ind; noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      destruct args1 using rev_ind; noconf Heqfixt'. clear IHargs1.
      rewrite <- mkApps_nested in Heqfixt'. noconf Heqfixt'.
      clear IHpred2.
      assert (is_constructor (rarg d) args0 = false).
      { move: Hisc. rewrite /is_constructor.
        elim: nth_error_spec.
        - rewrite app_length.
          move=> i hi harg. elim: nth_error_spec.
          + move=> i' hi' hrarg'.
            rewrite nth_error_app_lt in hi; eauto. congruence.
          + auto.
        - rewrite app_length. move=> ge _.
          elim: nth_error_spec; intros; try lia. auto.
      }
      specialize (IHpred1 _ _ _ _ _ Hnth H _ _ eq_refl eq_refl).
      destruct IHpred1 as [? ?]. red in a.
      unfold All2_prop2_eq. split.
      + apply a.
      + apply All2_app; auto.
    - constructor; auto.
    - subst. solve_discr.
  Qed.

  Lemma pred1_mkApps_tCoFix_inv `{cf : checker_flags} (Σ : global_env) (Γ Δ : context)
        mfix0 idx (args0 : list term) c :
    wf Σ ->
    pred1 Σ Γ Δ (mkApps (tCoFix mfix0 idx) args0) c ->
    ∑ mfix1 args1,
      (c = mkApps (tCoFix mfix1 idx) args1) *
      All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1) dtype dbody
                    (fun x => (dname x, rarg x))
                    (pred1 Σ) mfix0 mfix1 *
      (All2 (pred1 Σ Γ Δ) ) args0 args1.
  Proof with solve_discr.
    intros wfΣ pred. remember (mkApps _ _) as fixt. revert mfix0 idx args0 Heqfixt.
    induction pred; intros; solve_discr.
    - exfalso. apply (f_equal isElimSymb) in Heqfixt.
      rewrite isElimSymb_mkApps in Heqfixt. cbn in Heqfixt.
      eapply diff_false_true. rewrite <- Heqfixt.
      eapply isElimSymb_subst. apply untyped_subslet_length in u.
      rewrite subst_context_length in u. rewrite u.
      eapply isElimSymb_lhs.
      eapply declared_symbol_head in d. all: eauto.
    - exfalso. apply (f_equal isElimSymb) in Heqfixt.
      rewrite isElimSymb_mkApps in Heqfixt. cbn in Heqfixt.
      eapply diff_false_true. rewrite <- Heqfixt.
      eapply isElimSymb_subst. apply untyped_subslet_length in u.
      rewrite subst_context_length in u. rewrite u.
      eapply isElimSymb_lhs.
      eapply declared_symbol_par_head in d. all: eauto.
    - destruct args0 using rev_ind. 1: noconf Heqfixt.
      clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2. specialize (IHpred1 _ _ _ eq_refl).
      destruct IHpred1 as [? [? [[-> ?] ?]]].
      eexists x, (x0 ++ [N1])%list. intuition auto.
      + now rewrite <- mkApps_nested.
      + eapply All2_app; eauto.
    - exists mfix1, []; intuition (simpl; auto).
    - subst t; solve_discr.
  Qed.

  Lemma pred1_mkApps_tCoFix_refl_inv `{cf : checker_flags} (Σ : global_env) (Γ Δ : context)
        mfix0 mfix1 idx (args0 args1 : list term) :
    wf Σ ->
    pred1 Σ Γ Δ (mkApps (tCoFix mfix0 idx) args0) (mkApps (tCoFix mfix1 idx) args1) ->
      All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1) dtype dbody
                    (fun x => (dname x, rarg x))
                    (pred1 Σ) mfix0 mfix1 *
      (All2 (pred1 Σ Γ Δ)) args0 args1.
  Proof with solve_discr.
    intros wfΣ pred. remember (mkApps _ _) as fixt.
    remember (mkApps _ args1) as fixt'.
    revert mfix0 mfix1 idx args0 args1 Heqfixt Heqfixt'.
    induction pred; intros; symmetry in Heqfixt; solve_discr.
    - exfalso. apply (f_equal isElimSymb) in Heqfixt.
      rewrite isElimSymb_mkApps in Heqfixt. cbn in Heqfixt.
      eapply diff_false_true. rewrite Heqfixt.
      eapply isElimSymb_subst. apply untyped_subslet_length in u.
      rewrite subst_context_length in u. rewrite u.
      eapply isElimSymb_lhs.
      eapply declared_symbol_head in d. all: eauto.
    - exfalso. apply (f_equal isElimSymb) in Heqfixt.
      rewrite isElimSymb_mkApps in Heqfixt. cbn in Heqfixt.
      eapply diff_false_true. rewrite Heqfixt.
      eapply isElimSymb_subst. apply untyped_subslet_length in u.
      rewrite subst_context_length in u. rewrite u.
      eapply isElimSymb_lhs.
      eapply declared_symbol_par_head in d. all: eauto.
    - destruct args0 using rev_ind. 1: noconf Heqfixt.
      clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2.
      symmetry in Heqfixt'.
      destruct args1 using rev_ind. 1: discriminate.
      rewrite <- mkApps_nested in Heqfixt'.
      noconf Heqfixt'.
      destruct (IHpred1 _ _ _ _ _ eq_refl eq_refl) as [H H'].
      unfold All2_prop2_eq. split.
      + apply H.
      + apply All2_app; auto.
    - repeat finish_discr.
      unfold All2_prop2_eq. intuition (simpl; auto).
    - subst t; solve_discr.
  Qed.

End Pred1_inversion.

Hint Constructors pred1 : pcuic.

(* TODO MOVE *)
Definition on_option {A} (P : A -> Type) : option A -> Type :=
  fun o =>
    match o with
    | Some a => P a
    | None => True
    end.

Section Rho.
  Context {cf : checker_flags}.
  Context (Σ : global_env).

  #[program] Definition map_fix_rho {t} (rho : context -> forall x, size x < size t -> term) Γ mfixctx (mfix : mfixpoint term)
    (H : mfixpoint_size size mfix < size t) :=
    (map_In mfix (fun d (H : In d mfix) => {| dname := dname d;
        dtype := rho Γ (dtype d) _;
        dbody := rho (Γ ,,, mfixctx) (dbody d) _; rarg := (rarg d) |})).
  Next Obligation.
    eapply (In_list_size (def_size size)) in H.
    eapply le_lt_trans with (def_size size d).
    - unfold def_size. lia.
    - unfold mfixpoint_size in H0. lia.
  Qed.
  Next Obligation.
    eapply (In_list_size (def_size size)) in H.
    eapply le_lt_trans with (def_size size d).
    - unfold def_size. lia.
    - unfold mfixpoint_size in H0. lia.
  Qed.

  Equations? fold_fix_context_wf mfix
      (rho : context -> forall x, size x < (mfixpoint_size size mfix) -> term)
      (Γ acc : context) : context :=
  fold_fix_context_wf [] rho Γ acc => acc ;
  fold_fix_context_wf (d :: mfix) rho Γ acc =>
    fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x _) Γ (vass (dname d) (lift0 #|acc| (rho Γ (dtype d) _)) :: acc).
  Proof.
    - lia.
    - unfold def_size. lia.
  Qed.
  Transparent fold_fix_context_wf.

  #[program] Definition map_terms {t} (rho : context -> forall x, size x < size t -> term) Γ (l : list term)
    (H : list_size size l < size t) :=
    (map_In l (fun t (H : In t l) => rho Γ t _)).
  Next Obligation.
    eapply (In_list_size size) in H. lia.
  Qed.

  #[program] Definition map_brs {t} (rho : context -> forall x, size x < size t -> term) Γ (l : list (nat * term))
    (H : list_size (fun x : nat * term => size x.2) l < size t) :=
  (map_In l (fun x (H : In x l) => (x.1, rho Γ x.2 _))).
  Next Obligation.
    eapply (In_list_size (fun x => size x.2)) in H. simpl in *. lia.
  Qed.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

  (* First a view to decompose eliminations (maybe useless?) *)
  Equations elim_discr (t : term) : Prop :=
    elim_discr (tApp u v) := False ;
    elim_discr (tCase indn p c brs) := False ;
    elim_discr (tProj t p) := False ;
    elim_discr _ := True.

  Inductive decompose_elim_view : term -> Type :=
  | is_elims t l : elim_discr t -> decompose_elim_view (mkElims t l).

  Equations? decompose_elim_viewc (t : term) : decompose_elim_view t :=
    decompose_elim_viewc (tApp u v) with decompose_elim_viewc u := {
    | is_elims w l h := _ # is_elims w (l ++ [ eApp v ]) _
    } ;
    decompose_elim_viewc (tCase indn p c brs) with decompose_elim_viewc c := {
    | is_elims w l h := _ # is_elims w (l ++ [ eCase indn p brs ]) _
    } ;
    decompose_elim_viewc (tProj p t) with decompose_elim_viewc t := {
    | is_elims w l h := _ # is_elims w (l ++ [ eProj p ]) _
    } ;
    decompose_elim_viewc t := is_elims t [] I.
  Proof.
    all: rewrite mkElims_app.
    all: reflexivity.
  Qed.

  Definition onrr nsymb r :=
    r.(head) < nsymb ×
    All (elim_pattern #|r.(pat_context)|) r.(elims) ×
    closedn (#|r.(pat_context)| + nsymb) (rhs r).

  Definition onrd rd :=
    (* let Δ := map (vass nAnon) rd.(symbols) in *)
    let nsymb := #|rd.(symbols)| in
    All (onrr nsymb) rd.(rules) ×
    All (onrr nsymb) rd.(prules).

  (* Potential extra rules, might be redundant *)
  Context (extra : option (kername × rewrite_decl)).

  Lemma all_rewrite_rules_on_rd :
    forall rd,
      onrd rd ->
      All (onrr #|rd.(symbols)|) (all_rewrite_rules rd).
  Proof.
    intros rd h.
    unfold onrd in h. unfold all_rewrite_rules.
    destruct h.
    apply All_app_inv. all: auto.
  Qed.

  (* Getting the rewrite decl corresponding to a kername *)
  Definition lookup_rd (k : kername) : option rewrite_decl :=
    match lookup_env Σ k with
    | Some (RewriteDecl rd) => Some rd
    | _ => None
    end.

  Definition lookup_rewrite_decl (k : kername) : option rewrite_decl :=
    match extra with
    | Some (kn, rd) =>
        if eq_kername k kn
        then Some rd
        else lookup_rd k
    | None => lookup_rd k
    end.

  (* Getting the list of rewrite rules corresponding to a symbol *)
  (* Definition all_rewrite_rules (k : kername) :=
    match lookup_rewrite_decl k with
    | Some rd => Some (all_rd_rule rd)
    | None => None
    end. *)

  (* First lhs matching in a list of rules *)
  Fixpoint first_match k (l : list rewrite_rule) (t : term) :=
    match l with
    | [] => None
    | r :: l =>
      match match_lhs #|r.(pat_context)| k r.(head) r.(elims) t with
      | Some (ui, σ) => Some (ui, σ, r)
      | None => first_match k l t
      end
    end.

  Lemma first_match_sound :
    forall k l t ui σ r,
      first_match k l t = Some (ui, σ, r) ->
      All (elim_pattern #|r.(pat_context)|) r.(elims) ->
      t = subst0 σ (mkElims (tSymb k r.(head) ui) r.(elims)).
  Proof.
    intros k l t ui σ r h hr.
    induction l in ui, σ, r, h, hr |- *.
    - cbn in h. discriminate.
    - cbn - [ match_lhs ] in h.
      lazymatch type of h with
      | context [ match ?t with _ => _ end ] =>
        destruct t as [[ui' σ']|] eqn:e
      end.
      + noconf h. apply match_lhs_sound in e. all: auto.
      + apply IHl. all: auto.
  Qed.

  Lemma first_match_rule_list :
    forall k l t ui σ r,
      first_match k l t = Some (ui, σ, r) ->
      ∑ n, nth_error l n = Some r.
  Proof.
    intros k l t ui σ r h.
    induction l in ui, σ, r, h |- *.
    - cbn in h. discriminate.
    - cbn - [ match_lhs ] in h.
      lazymatch type of h with
      | context [ match ?t with _ => _ end ] =>
        destruct t as [[ui' σ']|] eqn:e
      end.
      + noconf h. exists 0. reflexivity.
      + apply IHl in h as [n h]. exists (S n). auto.
  Qed.

  Lemma first_match_subst_length :
    forall k l t ui σ r,
      first_match k l t = Some (ui, σ, r) ->
      #|σ| = #|r.(pat_context)|.
  Proof.
    intros k l t ui σ r h.
    induction l in ui, σ, r, h |- *.
    - cbn in h. discriminate.
    - cbn - [ match_lhs ] in h.
      lazymatch type of h with
      | context [ match ?t with _ => _ end ] =>
        destruct t as [[ui' σ']|] eqn:e
      end.
      + noconf h. eapply match_lhs_subst_length in e. auto.
      + eapply IHl. eauto.
  Qed.

  Lemma symbols_subst_pattern :
    forall p k ui nsymb npat,
      pattern npat p ->
      subst (symbols_subst k 0 ui nsymb) npat p = p.
  Proof.
    intros p k ui nsymb npat hp.
    induction hp
    as [n hn | ind n ui' args ha ih]
    using pattern_all_rect.
    - cbn. destruct (Nat.leb_spec npat n). 1: lia.
      reflexivity.
    - rewrite subst_mkApps. cbn. f_equal.
      induction ih. 1: constructor.
      cbn. f_equal.
      + auto.
      + apply IHih. inversion ha. assumption.
  Qed.

  Lemma subst_elim_symbols_subst :
    forall e npat nsymb k ui,
      elim_pattern npat e ->
      subst_elim (symbols_subst k 0 ui nsymb) npat e = e.
  Proof.
    intros e npat nsymb k ui he.
    destruct he as [| indn p brs hp ha|].
    - cbn. f_equal. apply symbols_subst_pattern. auto.
    - cbn. f_equal.
      + apply symbols_subst_pattern. auto.
      + induction ha as [| [? ?]]. 1: constructor.
        cbn. f_equal.
        * unfold on_snd. cbn. f_equal. apply symbols_subst_pattern. auto.
        * auto.
    - cbn. reflexivity.
  Qed.

  Lemma subst_elims_symbols_subst :
    forall l npat nsymb k ui,
      All (elim_pattern npat) l ->
      map (subst_elim (symbols_subst k 0 ui nsymb) npat) l = l.
  Proof.
    intros l npat nsymb k ui h.
    induction h. 1: constructor.
    cbn. f_equal. 2: auto.
    apply subst_elim_symbols_subst. assumption.
  Qed.

  Lemma first_match_rd_sound :
    forall k rd t ui σ r,
      onrd rd ->
      let l := all_rewrite_rules rd in
      first_match k l t = Some (ui, σ, r) ->
      t = subst0 σ (subst (symbols_subst k 0 ui #|symbols rd|) #|σ| (lhs r)).
  Proof.
    intros k rd t ui σ r hrd l h.
    apply all_rewrite_rules_on_rd in hrd.
    apply first_match_rule_list in h as hr. destruct hr as [m hr].
    eapply nth_error_all in hr. 2: eauto.
    unfold onrr in hr. destruct hr as [hh [he hc]].
    apply first_match_subst_length in h as hl.
    apply first_match_sound in h. 2: auto.
    subst. f_equal. unfold lhs.
    rewrite mkElims_subst. f_equal.
    - unfold symbols_subst. cbn.
      destruct (Nat.leb_spec #|σ| (#|r.(pat_context)| + r.(head))). 2: lia.
      replace (#|rd.(symbols)| - 0) with #|rd.(symbols)| by lia.
      replace (#|r.(pat_context)| + r.(head) - #|σ|) with r.(head) by lia.
      destruct nth_error eqn:e.
      2:{
        apply nth_error_None in e. rewrite list_make_length in e. lia.
      }
      apply list_make_nth_error in e. subst.
      cbn. f_equal. lia.
    - rewrite subst_elims_symbols_subst. 2: reflexivity.
      rewrite hl. assumption.
  Qed.

  (* Get kername corresponding to term *)
  Fixpoint elim_kn t :=
    match t with
    | tApp u v => elim_kn u
    | tCase ind p c brs => elim_kn c
    | tProj p t => elim_kn t
    | tSymb k n ui => Some k
    | _ => None
    end.

  Lemma elim_kn_mkElims :
    forall t l,
      elim_kn (mkElims t l) = elim_kn t.
  Proof.
    intros t l.
    induction l as [| [] l ih] in t |- *.
    1: reflexivity.
    all: rewrite ih.
    all: reflexivity.
  Qed.

  Definition not_lhs (t : term) :=
    (∑ k rd x,
      lookup_rewrite_decl k = Some rd ×
      let l := all_rewrite_rules rd in
      first_match k l t = Some x
    ) ->
    False.

  Inductive lhs_view (t : term) : Type :=
  | is_lhs k rd r ui σ :
      lookup_rewrite_decl k = Some rd ->
      first_match k (all_rewrite_rules rd) t = Some (ui, σ, r) ->
      lhs_view t

  | is_not_lhs :
      (* not_lhs t -> *)
      lhs_view t.

  Arguments is_lhs {_}.
  Arguments is_not_lhs {_}.

  Equations lhs_viewc (t : term) : lhs_view t :=
    lhs_viewc t with inspect (elim_kn t) := {
    | @exist (Some k) e1 with inspect (lookup_rewrite_decl k) := {
      | @exist (Some rd) e2 with inspect (first_match k (all_rewrite_rules rd) t) := {
        | @exist (Some (ui, σ, r)) e3 := is_lhs k rd r ui σ _ _ ;
        | @exist None e3 := is_not_lhs
        } ;
      | @exist None e2 := is_not_lhs
      } ;
    | @exist None e1 := is_not_lhs
    }.

  Lemma first_match_subst_size :
    forall k l t ui σ r,
      first_match k l t = Some (ui, σ, r) ->
      list_size size σ < size t.
  Proof.
    intros k l t ui σ r h.
    induction l in ui, σ, r, h |- *. 1: discriminate.
    cbn - [ match_lhs ] in h.
    destruct match_lhs as [[] |] eqn:e.
    - eapply match_lhs_subst_size in e.
      inversion h. subst. auto.
    - eapply IHl. eassumption.
  Qed.

  Equations? rho (Γ : context) (t : term) : term by wf (size t) :=
    rho Γ t with lhs_viewc t := {
    | is_lhs k rd r ui σ hrd e :=
      let ss := symbols_subst k 0 ui #|rd.(symbols)| in
      subst0 (map_terms rho Γ σ _) (subst ss #|σ| (rhs r)) ;

    | is_not_lhs with t := {
      | tApp t u with view_lambda_fix_app t u := {
        | fix_lambda_app_lambda na T b [] u' :=
          (rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ u'};
        | fix_lambda_app_lambda na T b (a :: l) u' :=
          mkApps ((rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ a})
            (map_terms rho Γ (l ++ [u']) _);
        | fix_lambda_app_fix mfix idx l a :=
          let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in
          let mfix' := map_fix_rho (t:=tFix mfix idx) (fun Γ x Hx => rho Γ x) Γ mfixctx mfix _ in
          let args := map_terms rho Γ (l ++ [a]) _ in
          match unfold_fix mfix' idx with
          | Some (rarg, fn) =>
            if is_constructor rarg (l ++ [a]) then
              mkApps fn args
            else mkApps (tFix mfix' idx) args
          | None => mkApps (tFix mfix' idx) args
          end ;
        | fix_lambda_app_other t' u' nisfixlam := tApp (rho Γ t') (rho Γ u')
        } ;

      | tLetIn na d t b := (subst10 (rho Γ d) (rho (vdef na (rho Γ d) (rho Γ t) :: Γ) b)) ;

      | tRel i with option_map decl_body (nth_error Γ i) := {
        | Some (Some body) => (lift0 (S i) body);
        | Some None => tRel i;
        | None => tRel i
        } ;

      | tCase (ind, pars) p x brs with inspect (decompose_app x) := {
        | exist (f, args) eqx with view_construct_cofix f := {
          | construct_cofix_construct ind' c u with eq_inductive ind ind' := {
            | true =>
              let p' := rho Γ p in
              let args' := map_terms rho Γ args _ in
              let brs' := map_brs rho Γ brs _ in
              iota_red pars c args' brs';
            | false =>
              let p' := rho Γ p in
              let x' := rho Γ x in
              let brs' := map_brs rho Γ brs _ in
              tCase (ind, pars) p' x' brs'
            } ;
          | construct_cofix_cofix mfix idx :=
            let p' := rho Γ p in
            let args' := map_terms rho Γ args _ in
            let brs' := map_brs rho Γ brs _ in
            let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in
            let mfix' := map_fix_rho (t:=tCase (ind, pars) p x brs) rho Γ mfixctx mfix _ in
            match nth_error mfix' idx with
            | Some d =>
              tCase (ind, pars) p' (mkApps (subst0 (cofix_subst mfix') (dbody d)) args') brs'
            | None => tCase (ind, pars) p' (rho Γ x) brs'
            end ;
          | construct_cofix_other t nconscof =>
            let p' := rho Γ p in
            let x' := rho Γ x in
            let brs' := map_brs rho Γ brs _ in
            tCase (ind, pars) p' x' brs'
          }
        } ;

      | tProj (i, pars, narg) x with inspect (decompose_app x) := {
        | exist (f, args) eqx with view_construct_cofix f :=
        | construct_cofix_construct ind c u with inspect (nth_error (map_terms rho Γ args _) (pars + narg)) := {
          | exist (Some arg1) eq =>
            if eq_inductive i ind then arg1
            else tProj (i, pars, narg) (rho Γ x);
          | exist None neq => tProj (i, pars, narg) (rho Γ x) };
        | construct_cofix_cofix mfix idx :=
          let args' := map_terms rho Γ args _ in
          let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in
          let mfix' := map_fix_rho (t:=tProj (i, pars, narg) x) rho Γ mfixctx mfix _ in
          match nth_error mfix' idx with
          | Some d => tProj (i, pars, narg) (mkApps (subst0 (cofix_subst mfix') (dbody d)) args')
          | None =>  tProj (i, pars, narg) (rho Γ x)
          end;
        | construct_cofix_other t nconscof => tProj (i, pars, narg) (rho Γ x)
        } ;

      | tConst c u with lookup_env Σ c := {
        | Some (ConstantDecl decl) with decl.(cst_body) := {
          | Some body => subst_instance_constr u body;
          | None => tConst c u
          } ;
        | _ => tConst c u
        } ;

      | tLambda na t u := tLambda na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u) ;

      | tProd na t u := tProd na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u) ;

      | tVar i := tVar i ;

      | tEvar n l := tEvar n (map_terms rho Γ l _) ;

      | tSort s := tSort s ;

      | tFix mfix idx :=
        let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in
        tFix (map_fix_rho (t:=tFix mfix idx) (fun Γ x Hx => rho Γ x) Γ mfixctx mfix _) idx ;

      | tCoFix mfix idx :=
        let mfixctx := fold_fix_context_wf mfix (fun Γ x Hx => rho Γ x) Γ [] in
        tCoFix (map_fix_rho (t:=tCoFix mfix idx) rho Γ mfixctx mfix _) idx ;

      | x := x
      }
    }.
  Proof.
    all:try abstract lia.
    - eapply first_match_subst_size. eassumption.
    - abstract (rewrite size_mkApps ?list_size_app /=; lia).
    - simpl in Hx. abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite list_size_app size_mkApps /=; lia).
    - clear; abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (rewrite list_size_app size_mkApps /=; lia).
    - clear -eqx; eapply symmetry, decompose_app_inv in eqx. subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear; abstract (lia).
    - clear -eqx; eapply symmetry, decompose_app_inv in eqx. subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear. abstract lia.
    - clear -eqx Hx. eapply symmetry, decompose_app_inv in eqx; subst x0.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx Hx. eapply symmetry, decompose_app_inv in eqx; subst x0.
      abstract (rewrite size_mkApps /=; lia).
    - clear -eqx. eapply symmetry, decompose_app_inv in eqx; subst x.
      abstract (rewrite size_mkApps /=; lia).
  Defined.

  Context (wfΣ : wf Σ).
  Context (on_extra : on_option (fun '(k,rd) => onrd rd) extra).

  Lemma lookup_rd_onrd :
    forall k rd,
      lookup_rd k = Some rd ->
      onrd rd.
  Proof.
    intros k rd h.
    unfold lookup_rd in h.
    destruct lookup_env as [[]|] eqn:e. all: try discriminate.
    noconf h.
    eapply lookup_on_global_env in wfΣ. 2: eassumption.
    destruct wfΣ as [Σ' [? hd]].
    destruct hd as [? [hr [hpr ?]]].
    unfold onrd. split.
    - eapply All_impl. 1: exact hr.
      intros r [? ? hrhs hh ? he ?]. unfold onrr. split. 2: split.
      + rewrite map_length in hh. assumption.
      + assumption.
      + rewrite map_length in hrhs.
        replace (#|pat_context r| + #|symbols rd|)
        with (#|symbols rd| + #|pat_context r|)
        by lia.
        assumption.
    - eapply All_impl. 1: exact hpr.
      intros r [? ? hrhs hh ? he ?]. unfold onrr. split. 2: split.
      + rewrite map_length in hh. assumption.
      + assumption.
      + rewrite map_length in hrhs.
        replace (#|pat_context r| + #|symbols rd|)
        with (#|symbols rd| + #|pat_context r|)
        by lia.
        assumption.
  Qed.

  Lemma lookup_rewrite_decl_onrd :
    forall k rd,
      lookup_rewrite_decl k = Some rd ->
      onrd rd.
  Proof.
    intros k rd h.
    unfold lookup_rewrite_decl in h.
    destruct extra as [[kn rd']|].
    - destruct eq_kername.
      + noconf h. cbn in on_extra. assumption.
      + eapply lookup_rd_onrd. eassumption.
    - eapply lookup_rd_onrd. eassumption.
  Qed.

  Lemma first_match_lookup_sound :
    forall k rd t ui σ r,
      lookup_rewrite_decl k = Some rd ->
      first_match k (all_rewrite_rules rd) t = Some (ui, σ, r) ->
      let ss := symbols_subst k 0 ui #|rd.(symbols)| in
      t = subst0 σ (subst ss #|σ| (lhs r)).
  Proof.
    intros k rd t ui σ r hrd e.
    eapply first_match_rd_sound. 2: eassumption.
    eapply lookup_rewrite_decl_onrd.
    eassumption.
  Qed.

  Lemma lhs_viewc_not_lhs :
    ∀ t,
      lhs_viewc t = is_not_lhs →
      not_lhs t.
  Proof.
    intros t.
    funelim (lhs_viewc t). 3: discriminate.
    all: intros _ X.
    - rename e into e1. clear H.
      destruct X as [? [? [[[? ?] ?] [e e0]]]]. cbn in e0.
      apply lookup_rewrite_decl_onrd in e as hrd.
      apply first_match_rd_sound in e0 as ?. 2: assumption.
      subst. unfold lhs in e1. rewrite 2!mkElims_subst in e1.
      rewrite elim_kn_mkElims in e1.
      cbn in e1.
      eapply first_match_subst_length in e0 as hl.
      destruct (Nat.leb_spec #|l| (#|r.(pat_context)| + r.(head))). 2: lia.
      destruct nth_error eqn:e4.
      2:{
        apply nth_error_None in e4. rewrite symbols_subst_length in e4.
        eapply all_rewrite_rules_on_rd in hrd as h'.
        eapply first_match_rule_list in e0 as hr.
        destruct hr as [n er].
        eapply All_nth_error in er. 2: eassumption.
        destruct er as [? ?].
        lia.
      }
      unfold symbols_subst in e4.
      apply list_make_nth_error in e4. subst.
      cbn in e1. noconf e1.
    - clear H H0.
      rename e into e1, e0 into e2.
      destruct X as [? [? [[[? ?] ?] [e e0]]]]. cbn in e0.
      apply lookup_rewrite_decl_onrd in e as hrd.
      apply first_match_rd_sound in e0 as ?. 2: assumption.
      subst. unfold lhs in e1. rewrite 2!mkElims_subst in e1.
      rewrite elim_kn_mkElims in e1.
      cbn in e1.
      eapply first_match_subst_length in e0 as hl.
      destruct (Nat.leb_spec #|l| (#|r.(pat_context)| + r.(head))). 2: lia.
      destruct nth_error eqn:e4.
      2:{
        apply nth_error_None in e4. rewrite symbols_subst_length in e4.
        eapply all_rewrite_rules_on_rd in hrd as h'.
        eapply first_match_rule_list in e0 as hr.
        destruct hr as [n er].
        eapply All_nth_error in er. 2: eassumption.
        destruct er as [? ?].
        lia.
      }
      unfold symbols_subst in e4.
      apply list_make_nth_error in e4. subst.
      cbn in e1. noconf e1.
      rewrite e in e2. noconf e2.
    - clear H H0 H1.
      rename e into e1, e0 into e2, e1 into e3.
      destruct X as [? [? [[[? ?] ?] [e e0]]]]. cbn in e0.
      apply lookup_rewrite_decl_onrd in e as hrd.
      apply first_match_rd_sound in e0 as ?. 2: assumption.
      subst. unfold lhs in e1. rewrite 2!mkElims_subst in e1.
      rewrite elim_kn_mkElims in e1.
      cbn in e1.
      eapply first_match_subst_length in e0 as hl.
      destruct (Nat.leb_spec #|l| (#|r0.(pat_context)| + r0.(head))). 2: lia.
      destruct nth_error eqn:e4.
      2:{
        apply nth_error_None in e4. rewrite symbols_subst_length in e4.
        eapply all_rewrite_rules_on_rd in hrd as h'.
        eapply first_match_rule_list in e0 as hr.
        destruct hr as [n er].
        eapply All_nth_error in er. 2: eassumption.
        destruct er as [? ?].
        lia.
      }
      unfold symbols_subst in e4.
      apply list_make_nth_error in e4. subst.
      cbn in e1. noconf e1.
      rewrite e in e2. noconf e2.
      rewrite e0 in e3.
      discriminate.
  Qed.

  Definition rho_fix_context Γ mfix :=
    fold_fix_context rho Γ [] mfix.

  Lemma rho_fix_context_length Γ mfix : #|rho_fix_context Γ mfix| = #|mfix|.
  Proof. now rewrite fold_fix_context_length Nat.add_0_r. Qed.

  Lemma map_terms_map t Γ l H : @map_terms t (fun Γ x Hx => rho Γ x) Γ l H = map (rho Γ) l.
  Proof.
    unfold map_terms. now rewrite map_In_spec.
  Qed.
  Hint Rewrite map_terms_map : rho.

  Lemma map_brs_map t Γ l H : @map_brs t (fun Γ x Hx => rho Γ x) Γ l H = map (fun x => (x.1, rho Γ x.2)) l.
  Proof.
    unfold map_brs. now rewrite map_In_spec.
  Qed.
  Hint Rewrite map_brs_map : rho.

  Definition map_fix (rho : context -> term -> term) Γ mfixctx (mfix : mfixpoint term) :=
    (map (map_def (rho Γ) (rho (Γ ,,, mfixctx))) mfix).

  Lemma map_fix_rho_map t Γ mfix ctx H :
    @map_fix_rho t (fun Γ x Hx => rho Γ x) Γ ctx mfix H =
    map_fix rho Γ ctx mfix.
  Proof.
    unfold map_fix_rho. now rewrite map_In_spec.
  Qed.

  Lemma fold_fix_context_wf_fold mfix Γ ctx :
    fold_fix_context_wf mfix (fun Γ x _ => rho Γ x) Γ ctx =
    fold_fix_context rho Γ ctx mfix.
  Proof.
    induction mfix in ctx |- *; simpl; auto.
  Qed.

  Hint Rewrite map_fix_rho_map fold_fix_context_wf_fold : rho.

  Lemma mkApps_tApp f a l : mkApps (tApp f a) l = mkApps f (a :: l).
  Proof. reflexivity. Qed.

  Lemma tApp_mkApps f a : tApp f a = mkApps f [a].
  Proof. reflexivity. Qed.

  Lemma isFixLambda_app_mkApps t l : isFixLambda_app t -> isFixLambda_app (mkApps t l).
  Proof.
    induction l using rev_ind; simpl; auto.
    rewrite -mkApps_nested.
    intros isf. specialize (IHl isf).
    simpl. rewrite IHl. destruct (mkApps t l); auto.
  Qed.
  Definition isFixLambda (t : term) : bool :=
  match t with
  | tFix _ _ => true
  | tLambda _ _ _ => true
  | _ => false
  end.

  Inductive fix_lambda_view : term -> Type :=
  | fix_lambda_lambda na b t : fix_lambda_view (tLambda na b t)
  | fix_lambda_fix mfix i : fix_lambda_view (tFix mfix i)
  | fix_lambda_other t : ~~ isFixLambda t -> fix_lambda_view t.

  Lemma view_fix_lambda (t : term) : fix_lambda_view t.
  Proof.
    destruct t; repeat constructor.
  Qed.

  Lemma isFixLambda_app_mkApps' t l x : isFixLambda t -> isFixLambda_app (tApp (mkApps t l) x).
  Proof.
    induction l using rev_ind; simpl; auto.
    - destruct t; auto.
    - intros isl. specialize (IHl isl).
      simpl in IHl.
      now rewrite -mkApps_nested /=.
  Qed.

  Ltac discr_mkApps H :=
    let Hf := fresh in let Hargs := fresh in
    rewrite ?tApp_mkApps ?mkApps_nested in H;
      (eapply mkApps_nApp_inj in H as [Hf Hargs] ||
        eapply (mkApps_nApp_inj _ _ []) in H as [Hf Hargs] ||
        eapply (mkApps_nApp_inj _ _ _ []) in H as [Hf Hargs]);
        [noconf Hf|reflexivity].

  Set Equations With UIP. (* This allows to use decidable equality on terms. *)

  (* TODO MOVE *)
  Lemma elim_kn_mkApps :
    forall t l,
      elim_kn (mkApps t l) = elim_kn t.
  Proof.
    intros t l.
    induction l in t |- *.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma elim_kn_lhs :
    forall σ k ui rd r n,
      lookup_rewrite_decl k = Some rd ->
      nth_error (all_rewrite_rules rd) n = Some r ->
      let ss := symbols_subst k 0 ui #|rd.(symbols)| in
      elim_kn (subst0 σ (subst ss #|r.(pat_context)| (lhs r))) = Some k.
  Proof.
    intros σ k ui rd r n hrd hr ss.
    apply lookup_rewrite_decl_onrd in hrd.
    apply all_rewrite_rules_on_rd in hrd.
    eapply All_nth_error in hrd. 2: eauto.
    destruct hrd as [? ?].
    unfold lhs. rewrite 2!mkElims_subst. rewrite elim_kn_mkElims.
    cbn.
    match goal with
    | |- context [ ?x <=? ?y ] =>
      destruct (Nat.leb_spec x y)
    end.
    2: lia.
    replace (#|pat_context r| + head r - #|pat_context r|)
    with r.(head) by lia.
    destruct (nth_error ss _) eqn:e.
    2:{
      apply nth_error_None in e. unfold ss in e.
      rewrite symbols_subst_length in e.
      lia.
    }
    unfold ss in e.
    apply symbols_subst_nth_error in e. subst.
    cbn. reflexivity.
  Qed.

  (* TODO MOVE *)
  (* Ltac fold_rho :=
    lazymatch goal with
    | |- context [ rho_unfold_clause_1 ?t (lhs_viewc_clause_1 ?t (inspect (elim_kn ?t))) ?Γ ] =>
      replace (rho_unfold_clause_1 t (lhs_viewc_clause_1 t (inspect (elim_kn t))) Γ)
      with (rho Γ t)
      by (simp rho lhs_viewc ; reflexivity)
    end. *)

  Lemma fold_rho :
    forall Γ t,
      rho Γ t =
      rho_unfold_clause_1 t (lhs_viewc_clause_1 t (inspect (elim_kn t))) Γ.
  Proof.
    intros Γ t.
    simp rho lhs_viewc. reflexivity.
  Qed.

  Ltac fold_rho :=
    rewrite <- fold_rho.

  (* Most of this is discrimination, we should have a more robust tactic to
    solve this. *)
  Lemma rho_app_lambda Γ na ty b a l :
    rho Γ (mkApps (tApp (tLambda na ty b) a) l) =
    mkApps ((rho (vass na (rho Γ ty) :: Γ) b) {0 := rho Γ a}) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho (* lhs_viewc *).
    - simpl. autorewrite with lhs_viewc rho. reflexivity.
    - destruct lhs_viewc.
      1:{
        eapply first_match_lookup_sound in e0 as et. 2: auto.
        apply (f_equal elim_kn) in et.
        apply first_match_subst_length in e0 as σl.
        rewrite σl in et.
        eapply first_match_rule_list in e0 as hr. destruct hr as [n ?].
        erewrite elim_kn_lhs in et. 2-3: eauto.
        rewrite elim_kn_mkApps in et.
        cbn in et.
        discriminate.
      }
      cbn. repeat fold_rho.
      rewrite -mkApps_nested.
      cbn.
      change (mkApps (tApp (tLambda na ty b) a) l) with
        (mkApps (tLambda na ty b) (a :: l)).
      now simp rho.
  Qed.

  Lemma bool_pirr (b b' : bool) (p q : b = b') : p = q.
  Proof. noconf p. now noconf q. Qed.

  Lemma view_lambda_fix_app_other t u (H : ~~ isFixLambda_app (tApp t u)) :
    view_lambda_fix_app t u = fix_lambda_app_other t u H.
  Proof.
    induction t; simpl; f_equal; try apply bool_pirr.
    - simpl in H => //.
    - specialize (IHt1 H).
      rewrite IHt1. destruct t1; auto.
    - simpl in H => //.
  Qed.

  Lemma rho_app_lambda' Γ na ty b l :
    rho Γ (mkApps (tLambda na ty b) l) =
    match l with
    | [] => rho Γ (tLambda na ty b)
    | a :: l =>
      mkApps ((rho (vass na (rho Γ ty) :: Γ) b) {0 := rho Γ a}) (map (rho Γ) l)
    end.
  Proof.
    destruct l using rev_case; autorewrite with rho; auto.
    destruct lhs_viewc.
    1:{
      eapply first_match_lookup_sound in e0 as et. 2: auto.
      apply (f_equal elim_kn) in et.
      apply first_match_subst_length in e0 as σl.
      rewrite σl in et.
      eapply first_match_rule_list in e0 as hr. destruct hr as [n ?].
      erewrite elim_kn_lhs in et. 2-3: eauto.
      rewrite elim_kn_mkApps in et.
      cbn in et.
      discriminate.
    }
    repeat fold_rho.
    simpl. rewrite -mkApps_nested. simp rho.
    repeat fold_rho.
    destruct l; simpl; auto. now simp rho.
  Qed.

  Lemma rho_app_construct Γ c u i l :
    rho Γ (mkApps (tConstruct c u i) l) =
    mkApps (tConstruct c u i) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho; auto.
    repeat fold_rho.
    simpl. rewrite -mkApps_nested. simp rho.
    destruct lhs_viewc.
    1:{
      eapply first_match_lookup_sound in e0 as et. 2: auto.
      apply (f_equal elim_kn) in et.
      apply first_match_subst_length in e0 as σl.
      rewrite σl in et.
      eapply first_match_rule_list in e0 as hr. destruct hr as [n ?].
      erewrite elim_kn_lhs in et. 2-3: eauto.
      cbn in et. rewrite elim_kn_mkApps in et.
      discriminate.
    }
    simpl.
    unshelve erewrite view_lambda_fix_app_other.
    - simpl.
      clear. induction l using rev_ind; simpl; auto.
      rewrite -mkApps_nested. simpl. apply IHl.
    - simp rho. repeat fold_rho.
      rewrite IHl. now rewrite map_app -mkApps_nested.
  Qed.
  Hint Rewrite rho_app_construct : rho.

  Lemma rho_app_cofix Γ mfix idx l :
    rho Γ (mkApps (tCoFix mfix idx) l) =
    mkApps (tCoFix (map_fix rho Γ (rho_fix_context Γ mfix) mfix) idx) (map (rho Γ) l).
  Proof.
    induction l using rev_ind; autorewrite with rho; auto.
    - simpl. simp rho lhs_viewc. reflexivity.
    - rewrite -mkApps_nested.
      destruct lhs_viewc.
      1:{
        eapply first_match_lookup_sound in e0 as et. 2: auto.
        apply (f_equal elim_kn) in et.
        apply first_match_subst_length in e0 as σl.
        rewrite σl in et.
        eapply first_match_rule_list in e0 as hr. destruct hr as [n ?].
        erewrite elim_kn_lhs in et. 2-3: eauto.
        cbn in et. rewrite elim_kn_mkApps in et.
        discriminate.
      }
      simpl.
      unshelve erewrite view_lambda_fix_app_other.
      + simpl. clear. induction l using rev_ind; simpl; auto.
        rewrite -mkApps_nested. simpl. apply IHl.
      + simp rho. repeat fold_rho. rewrite IHl.
        now rewrite map_app -mkApps_nested.
  Qed.

  Hint Rewrite rho_app_cofix : rho.

  Lemma map_cofix_subst (f : context -> term -> term)
        (f' : context -> context -> term -> term) mfix Γ Γ' :
    (forall n, tCoFix (map (map_def (f Γ) (f' Γ Γ')) mfix) n = f Γ (tCoFix mfix n)) ->
    cofix_subst (map (map_def (f Γ) (f' Γ Γ')) mfix) =
    map (f Γ) (cofix_subst mfix).
  Proof.
    unfold cofix_subst. intros.
    rewrite map_length. generalize (#|mfix|). induction n.
    - simpl. reflexivity.
    - simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma map_cofix_subst' f g mfix :
    (forall n, tCoFix (map (map_def f g) mfix) n = f (tCoFix mfix n)) ->
    cofix_subst (map (map_def f g) mfix) =
    map f (cofix_subst mfix).
  Proof.
    unfold cofix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 1 2. induction n.
    - simpl. reflexivity.
    - simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma map_fix_subst f g mfix :
    (forall n, tFix (map (map_def f g) mfix) n = f (tFix mfix n)) ->
    fix_subst (map (map_def f g) mfix) =
    map f (fix_subst mfix).
  Proof.
    unfold fix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 1 2. induction n.
    - simpl. reflexivity.
    - simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma rho_app_fix Γ mfix idx args :
    let rhoargs := map (rho Γ) args in
    rho Γ (mkApps (tFix mfix idx) args) =
      match nth_error mfix idx with
      | Some d =>
        if is_constructor (rarg d) args then
          let fn := (subst0 (map (rho Γ) (fix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
          mkApps fn rhoargs
        else mkApps (rho Γ (tFix mfix idx)) rhoargs
      | None => mkApps (rho Γ (tFix mfix idx)) rhoargs
      end.
  Proof.
    induction args using rev_ind; autorewrite with rho.
    - intros rhoargs.
      destruct nth_error as [d|] eqn:eqfix => //.
      rewrite /is_constructor nth_error_nil //.
    - simpl. rewrite map_app /=.
      destruct lhs_viewc.
      1:{
        eapply first_match_lookup_sound in e0 as et. 2: auto.
        apply (f_equal elim_kn) in et.
        apply first_match_subst_length in e0 as σl.
        rewrite σl in et.
        eapply first_match_rule_list in e0 as hr. destruct hr as [n ?].
        erewrite elim_kn_lhs in et. 2-3: eauto.
        cbn in et. rewrite elim_kn_mkApps in et.
        discriminate.
      }
      simpl.
      destruct nth_error as [d|] eqn:eqfix => //.
      + destruct (is_constructor (rarg d) (args ++ [x])) eqn:isc; simp rho.
        * rewrite -mkApps_nested /=.
          autorewrite with rho.
          simpl. simp rho. repeat fold_rho. rewrite /unfold_fix.
          rewrite /map_fix nth_error_map eqfix /= isc map_fix_subst ?map_app //.
          intros m; simp rho lhs_viewc. simpl. f_equal; now simp rho.
        * rewrite -mkApps_nested /=.
          simp rho lhs_viewc. simpl. simp rho lhs_viewc.
          repeat fold_rho.
          now rewrite /unfold_fix /map_fix nth_error_map eqfix /= isc map_app.
      + rewrite -mkApps_nested /=. simp rho lhs_viewc.
        simpl. simp rho lhs_viewc.
        repeat fold_rho.
        now rewrite /unfold_fix /map_fix nth_error_map eqfix /= map_app.
  Qed.

  (* Helps factors proofs: only two cases to consider: the fixpoint unfolds or is stuck. *)
  Inductive rho_fix_spec Γ mfix i l : term -> Type :=
  | rho_fix_red d :
      let fn := (subst0 (map (rho Γ) (fix_subst mfix))) (rho (Γ ,,, rho_fix_context Γ mfix) (dbody d)) in
      nth_error mfix i = Some d ->
      is_constructor (rarg d) l ->
      rho_fix_spec Γ mfix i l (mkApps fn (map (rho Γ) l))
  | rho_fix_stuck :
      (match nth_error mfix i with
       | None => true
       | Some d => ~~ is_constructor (rarg d) l
       end) ->
      rho_fix_spec Γ mfix i l (mkApps (rho Γ (tFix mfix i)) (map (rho Γ) l)).

  Lemma rho_fix_elim Γ mfix i l :
    rho_fix_spec Γ mfix i l (rho Γ (mkApps (tFix mfix i) l)).
  Proof.
    rewrite rho_app_fix /= /unfold_fix.
    case e: nth_error => [d|] /=.
    - case isc: is_constructor => /=.
      + eapply (rho_fix_red Γ mfix i l d) => //.
      + apply rho_fix_stuck.
        now rewrite e isc.
    - apply rho_fix_stuck. now rewrite e /=.
  Qed.

  Lemma rho_app_case Γ ind pars p x brs :
    not_lhs (tCase (ind, pars) p x brs) ->
    rho Γ (tCase (ind, pars) p x brs) =
    let (f, args) := decompose_app x in
    match f with
    | tConstruct ind' c u =>
      if eq_inductive ind ind' then
        let p' := rho Γ p in
        let args' := map (rho Γ) args in
        let brs' := map (on_snd (rho Γ)) brs in
        iota_red pars c args' brs'
      else tCase (ind, pars) (rho Γ p) (rho Γ x) (map (on_snd (rho Γ)) brs)
    | tCoFix mfix idx =>
      match nth_error mfix idx with
      | Some d =>
        let fn := (subst0 (map (rho Γ) (cofix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
        tCase (ind, pars) (rho Γ p) (mkApps fn (map (rho Γ) args)) (map (on_snd (rho Γ)) brs)
      | None => tCase (ind, pars) (rho Γ p) (rho Γ x) (map (on_snd (rho Γ)) brs)
      end
    | _ => tCase (ind, pars) (rho Γ p) (rho Γ x) (map (on_snd (rho Γ)) brs)
    end.
  Proof.
    intros notlhs.
    autorewrite with rho.
    destruct lhs_viewc.
    1:{
      exfalso. apply notlhs.
      exists k, rd, (ui, σ, r). split. all: auto.
    }
    simp rho.
    repeat fold_rho.
    set (app := inspect _).
    destruct app as [[f l] eqapp].
    rewrite -{2}eqapp. autorewrite with rho. repeat fold_rho.
    destruct view_construct_cofix; autorewrite with rho.
    - destruct eq_inductive eqn:eqi; simp rho => //.
    - destruct unfold_cofix as [[rarg fn]|]; simp rho => //.
      + simpl. autorewrite with rho. rewrite /map_fix nth_error_map.
        destruct nth_error => /=.
        * f_equal.
          f_equal. rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
          intros. autorewrite with rho lhs_viewc. simpl.
          now autorewrite with rho.
        * reflexivity.
      + simpl.
        autorewrite with rho.
        rewrite /map_fix nth_error_map.
        destruct nth_error => /= //.
        rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
        intros. simp rho lhs_viewc. simpl. now simp rho.
    - simpl. eapply symmetry, decompose_app_inv in eqapp.
      subst x. destruct t; simpl in d => //.
  Qed.

  Lemma rho_app_proj Γ ind pars arg x :
    not_lhs (tProj (ind, pars, arg) x) ->
    rho Γ (tProj (ind, pars, arg) x) =
    let (f, args) := decompose_app x in
    match f with
    | tConstruct ind' c u =>
      if eq_inductive ind ind' then
        match nth_error args (pars + arg) with
        | Some arg1 => rho Γ arg1
        | None => tProj (ind, pars, arg) (rho Γ x)
        end
      else tProj (ind, pars, arg) (rho Γ x)
    | tCoFix mfix idx =>
      match nth_error mfix idx with
      | Some d =>
        let fn := (subst0 (map (rho Γ) (cofix_subst mfix))) (rho (Γ ,,, fold_fix_context rho Γ [] mfix) (dbody d)) in
        tProj (ind, pars, arg) (mkApps fn (map (rho Γ) args))
      | None => tProj (ind, pars, arg) (rho Γ x)
      end
    | _ => tProj (ind, pars, arg) (rho Γ x)
    end.
  Proof.
    intro notlhs.
    autorewrite with rho.
    destruct lhs_viewc.
    1:{
      exfalso. apply notlhs.
      exists k, rd, (ui, σ, r). split. all: auto.
    }
    simp rho.
    repeat fold_rho.
    set (app := inspect _).
    destruct app as [[f l] eqapp].
    rewrite -{2}eqapp. autorewrite with rho. repeat fold_rho.
    destruct view_construct_cofix; autorewrite with rho.
    - destruct eq_inductive eqn:eqi; simp rho => //.
      + set (arg' := inspect _). clearbody arg'.
        destruct arg' as [[arg'|] eqarg'];
        autorewrite with rho.
        * rewrite eqi.
          simp rho in eqarg'. rewrite nth_error_map in eqarg'.
          destruct nth_error => //. now simpl in eqarg'.
        * simp rho in eqarg'; rewrite nth_error_map in eqarg'.
          destruct nth_error => //.
      + repeat fold_rho. destruct inspect as [[arg'|] eqarg'] => //; simp rho.
        now rewrite eqi.
    - simpl. autorewrite with rho.
      rewrite /map_fix nth_error_map.
      destruct nth_error eqn:nth => /= //.
      f_equal. f_equal. f_equal.
      rewrite (map_cofix_subst rho (fun x y => rho (x ,,, y))) //.
      intros. autorewrite with rho lhs_viewc. simpl. now autorewrite with rho.
    - simpl. eapply symmetry, decompose_app_inv in eqapp.
      subst x. destruct t; simpl in d => //.
  Qed.



  Lemma fold_fix_context_rev_mapi {Γ l m} :
    fold_fix_context rho Γ l m =
    List.rev (mapi (λ (i : nat) (x : def term),
                    vass (dname x) ((lift0 (#|l| + i)) (rho Γ (dtype x)))) m) ++ l.
  Proof.
    unfold mapi.
    rewrite rev_mapi.
    induction m in l |- *.
    - simpl. auto.
    - intros. simpl. rewrite mapi_app. simpl.
      rewrite IHm. cbn.
      rewrite - app_assoc. simpl. rewrite List.rev_length.
      rewrite Nat.add_0_r. rewrite minus_diag. simpl.
      f_equal.
      + apply mapi_ext_size. simpl. intros.
        rewrite List.rev_length in H.
        f_equal. f_equal. lia.
      + f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma fold_fix_context_rev {Γ m} :
    fold_fix_context rho Γ [] m =
    List.rev (mapi (λ (i : nat) (x : def term),
                    vass (dname x) (lift0 i (rho Γ (dtype x)))) m).
  Proof.
    pose proof (@fold_fix_context_rev_mapi Γ [] m).
    now rewrite app_nil_r in H.
  Qed.

  Lemma nth_error_map_fix i f Γ Δ m :
    nth_error (map_fix f Γ Δ m) i = option_map (map_def (f Γ) (f (Γ ,,, Δ))) (nth_error m i).
  Proof.
    now rewrite /map_fix nth_error_map.
  Qed.

  Lemma fold_fix_context_app Γ l acc acc' :
    fold_fix_context rho Γ l (acc ++ acc') =
    fold_fix_context rho Γ (fold_fix_context rho Γ l acc) acc'.
  Proof.
    induction acc in l, acc' |- *.
    - simpl. auto.
    - simpl. rewrite IHacc. reflexivity.
  Qed.

  Section All2i.
    (** A special notion of All2 just for this proof *)

    Inductive All2i {A B : Type} (R : nat -> A -> B -> Type) : list A -> list B -> Type :=
      All2i_nil : All2i R [] []
    | All2i_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
            R (List.length l) x y -> All2i R l l' -> All2i R (x :: l) (y :: l').
    Hint Constructors All2i : core pcuic.

    Lemma All2i_app {A B} (P : nat -> A -> B -> Type) l0 l0' l1 l1' :
      All2i P l0' l1' ->
      All2i (fun n => P (n + #|l0'|)) l0 l1 ->
      All2i P (l0 ++ l0') (l1 ++ l1').
    Proof.
      intros H. induction 1; simpl.
      - apply H.
      - constructor.
        + now rewrite app_length.
        + apply IHX.
    Qed.

    Lemma All2i_length {A B} (P : nat -> A -> B -> Type) l l' :
      All2i P l l' -> #|l| = #|l'|.
    Proof. induction 1; simpl; auto. Qed.

    Lemma All2i_impl {A B} (P Q : nat -> A -> B -> Type) l l' :
      All2i P l l' -> (forall n x y, P n x y -> Q n x y) -> All2i Q l l'.
    Proof. induction 1; simpl; auto. Qed.

    Lemma All2i_rev {A B} (P : nat -> A -> B -> Type) l l' :
      All2i P l l' ->
      All2i (fun n => P (#|l| - S n)) (List.rev l) (List.rev l').
    Proof.
      induction 1.
      - constructor.
      - simpl List.rev.
        apply All2i_app.
        + repeat constructor. simpl. rewrite Nat.sub_0_r. auto.
        + simpl. eapply All2i_impl; eauto. intros. simpl in X0.
          now rewrite Nat.add_1_r.
    Qed.

    Inductive All2i_ctx {A B : Type} (R : nat -> A -> B -> Type) (n : nat) : list A -> list B -> Type :=
      All2i_ctx_nil : All2i_ctx R n [] []
    | All2i_ctx_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
        R n x y -> All2i_ctx R (S n) l l' -> All2i_ctx R n (x :: l) (y :: l').
    Hint Constructors All2i_ctx : core pcuic.

    Lemma All2i_ctx_app {A B} (P : nat -> A -> B -> Type) n l0 l0' l1 l1' :
      All2i_ctx P (n + #|l0|) l0' l1' ->
      All2i_ctx P n l0 l1 ->
      All2i_ctx P n (l0 ++ l0') (l1 ++ l1').
    Proof.
      intros H.
      induction 1.
      - simpl. now rewrite Nat.add_0_r in H.
      - simpl. rewrite Nat.add_succ_comm in IHX. specialize (IHX H).
        now constructor.
    Qed.

    Lemma All2i_rev_ctx {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
      All2i R l l' -> All2i_ctx R 0 (List.rev l) (List.rev l').
    Proof.
      induction 1.
      - simpl. constructor.
      - simpl. apply All2i_ctx_app.
        + simpl. rewrite List.rev_length. auto.
        + auto.
    Qed.

    Lemma All2i_rev_ctx_gen {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
      All2i_ctx R n l l' -> All2i (fun m => R (n + m)) (List.rev l) (List.rev l').
    Proof.
      induction 1.
      - simpl. constructor.
      - simpl. eapply All2i_app.
        + constructor. 2: constructor.
          now rewrite Nat.add_0_r.
        + eapply All2i_impl; eauto. intros.
          simpl in *. rewrite [S _]Nat.add_succ_comm in X0.
          now rewrite Nat.add_1_r.
    Qed.

    Lemma All2i_rev_ctx_inv {A B} (R : nat -> A -> B -> Type) (l : list A) (l' : list B) :
      All2i_ctx R 0 l l' -> All2i R (List.rev l) (List.rev l').
    Proof.
      intros. eapply All2i_rev_ctx_gen in X. simpl in X. apply X.
    Qed.

    Lemma All2i_ctx_mapi {A B C D} (R : nat -> A -> B -> Type)
          (l : list C) (l' : list D) (f : nat -> C -> A) (g : nat -> D -> B) n :
      All2i_ctx (fun n x y => R n (f n x) (g n y)) n l l' ->
      All2i_ctx R n (mapi_rec f l n) (mapi_rec g l' n).
    Proof.
      induction 1; constructor; auto.
    Qed.

    Lemma All2i_ctx_trivial {A B} (R : nat -> A -> B -> Type) (H : forall n x y, R n x y) n l l' :
      #|l| = #|l'| -> All2i_ctx R n l l'.
    Proof.
      induction l in n, l' |- *; destruct l'; simpl; try discriminate; intros; constructor; auto.
    Qed.
  End All2i.

  Definition pres_bodies Γ Δ σ :=
    All2i (fun n decl decl' => (decl_body decl' = option_map (fun x => x.[⇑^n σ]) (decl_body decl)))
        Γ Δ.

  Lemma pres_bodies_inst_context Γ σ : pres_bodies Γ (inst_context σ Γ) σ.
  Proof.
    red; induction Γ. 1: constructor.
    rewrite inst_context_snoc. constructor.
    - simpl. reflexivity.
    - apply IHΓ.
  Qed.
  Hint Resolve pres_bodies_inst_context : pcuic.

  Lemma inst_subst0 :
    forall σ s t,
      (subst0 s t).[σ] = (subst0 (map (inst σ) s) t.[⇑^#|s| σ]).
  Proof.
    intros σ s t. autorewrite with sigma. eapply inst_ext.
    intro i. unfold subst_compose, Upn, subst_consn.
    destruct (nth_error s i) eqn:e.
    - rewrite nth_error_idsn_Some.
      1:{ apply nth_error_Some_length in e. assumption. }
      cbn. rewrite nth_error_map. rewrite e. cbn. reflexivity.
    - rewrite nth_error_idsn_None.
      1:{ apply nth_error_None in e. lia. }
      cbn. rewrite idsn_length.
      unfold subst_compose, shiftk.
      autorewrite with sigma.
      rewrite <- (subst_ids (σ (i - #|s|))) at 1.
      eapply inst_ext. intro j.
      unfold subst_compose. cbn.
      rewrite nth_error_map.
      pose proof (nth_error_None s (#|s| + j)) as [_ h].
      rewrite -> h by lia. cbn.
      rewrite map_length. f_equal. lia.
  Qed.

  Lemma map_decl_vdef :
    forall f na t T,
      map_decl f (vdef na t T) = vdef na (f t) (f T).
  Proof.
    intros f na t T. reflexivity.
  Qed.

  Definition ctxmap (Γ Δ : context) (s : nat -> term) :=
    forall x d, nth_error Γ x = Some d ->
                match decl_body d return Type with
                | Some b =>
                  ∑ i b', s x = tRel i /\
                          option_map decl_body (nth_error Δ i) = Some (Some b') /\
                          b'.[↑^(S i)] = b.[↑^(S x) ∘s s]
                | None => True
                end.

  Lemma untyped_subslet_inst :
    forall Γ Δ Θ s σ,
      untyped_subslet Γ s Δ ->
      ctxmap Γ Θ σ ->
      untyped_subslet Θ (map (inst σ) s) (inst_context σ Δ).
  Proof.
    intros Γ Δ Θ s σ hs hσ.
    induction hs in Θ, σ, hσ |- *.
    - constructor.
    - rewrite inst_context_snoc. cbn.
      econstructor. eapply IHhs. assumption.
    - rewrite inst_context_snoc. cbn.
      rewrite inst_subst0. rewrite map_decl_vdef.
      apply untyped_subslet_length in hs. rewrite hs.
      eapply untyped_cons_let_def.
      eapply IHhs. assumption.
  Qed.

  Lemma All2_prop2_eq_split (Γ Γ' Γ2 Γ2' : context) (A B : Type) (f g : A → term)
        (h : A → B) (rel : context → context → term → term → Type) x y :
    All2_prop2_eq Γ Γ' Γ2 Γ2' f g h rel x y ->
    All2 (on_Trel (rel Γ Γ') f) x y *
    All2 (on_Trel (rel Γ2 Γ2') g) x y *
    All2 (on_Trel eq h) x y.
  Proof.
    induction 1; intuition.
  Qed.

  Lemma refine_pred Γ Δ t u u' : u = u' -> pred1 Σ Γ Δ t u' -> pred1 Σ Γ Δ t u.
  Proof. now intros ->. Qed.

  Lemma ctxmap_ext Γ Δ : CMorphisms.Proper (CMorphisms.respectful (pointwise_relation _ eq) isEquiv) (ctxmap Γ Δ).
  Proof.
    red. red. intros.
    split; intros X.
    - intros n d Hn. specialize (X n d Hn).
      destruct d as [na [b|] ty]; simpl in *; auto.
      destruct X as [i [b' [? ?]]]. exists i, b'.
      rewrite -H. split; auto.
    - intros n d Hn. specialize (X n d Hn).
      destruct d as [na [b|] ty]; simpl in *; auto.
      destruct X as [i [b' [? ?]]]. exists i, b'.
      rewrite H. split; auto.
  Qed.

  Lemma Up_ctxmap Γ Δ c c' σ :
    ctxmap Γ Δ σ ->
    (decl_body c' = option_map (fun x => x.[σ]) (decl_body c)) ->
    ctxmap (Γ ,, c) (Δ ,, c') (⇑ σ).
  Proof.
    intros.
    intros x d Hnth.
    destruct x; simpl in *; noconf Hnth.
    - destruct c as [na [b|] ty]; simpl; auto.
      exists 0. eexists. repeat split; eauto.
      + simpl in H. simpl. now rewrite H.
      + now autorewrite with sigma.
    - specialize (X _ _ Hnth). destruct decl_body; auto.
      destruct X as [i [b' [? [? ?]]]]; auto.
      exists (S i), b'. simpl. repeat split; auto.
      + unfold subst_compose. now rewrite H0.
      + autorewrite with sigma in H2 |- *.
        rewrite -subst_compose_assoc.
        rewrite -subst_compose_assoc.
        rewrite -subst_compose_assoc.
        rewrite -inst_assoc. rewrite H2.
        now autorewrite with sigma.
  Qed.

  Lemma Upn_ctxmap Γ Δ Γ' Δ' σ :
    pres_bodies Γ' Δ' σ ->
    ctxmap Γ Δ σ ->
    ctxmap (Γ ,,, Γ') (Δ ,,, Δ') (⇑^#|Γ'| σ).
  Proof.
    induction 1.
    - simpl. intros.
      eapply ctxmap_ext.
      + rewrite Upn_0. reflexivity.
      + apply X.
    - simpl. intros Hσ.
      eapply ctxmap_ext.
      + now sigma.
      + eapply Up_ctxmap; eauto.
  Qed.
  Hint Resolve Upn_ctxmap : pcuic.

  (** Untyped renamings *)
  Definition renaming Γ Δ r :=
    forall x, match nth_error Γ x with
              | Some d =>
                match decl_body d return Prop with
                | Some b =>
                  exists b', option_map decl_body (nth_error Δ (r x)) = Some (Some b') /\
                             b'.[↑^(S (r x))] = b.[↑^(S x) ∘s ren r]
                (* whose body is b substituted with the previous variables *)
                | None => option_map decl_body (nth_error Δ (r x)) = Some None
                end
              | None => nth_error Δ (r x) = None
              end.

  Instance renaming_ext Γ Δ :
    Morphisms.Proper (`=1` ==> iff)%signature (renaming Γ Δ).
  Proof.
    red. red. intros.
    split; intros.
    - intros n. specialize (H0 n).
      destruct nth_error; auto.
      + destruct c as [na [b|] ty]; simpl in *; auto.
        * destruct H0 as [b' [Heq Heq']]; auto.
          exists b'. rewrite -(H n).
          intuition auto. now rewrite Heq' H.
        * now rewrite -H.
      + now rewrite -H.
    - intros n. specialize (H0 n).
      destruct nth_error; auto.
      + destruct c as [na [b|] ty]; simpl in *; auto.
        * destruct H0 as [b' [Heq Heq']]; auto.
          exists b'. rewrite (H n).
          intuition auto. now rewrite Heq' H.
        * now rewrite H.
      + now rewrite H.
  Qed.

  Lemma shiftn1_renaming Γ Δ c c' r :
    renaming Γ Δ r ->
    (decl_body c' = option_map (fun x => x.[ren r]) (decl_body c)) →
    renaming (c :: Γ) (c' :: Δ) (shiftn 1 r).
  Proof.
    intros.
    red.
    destruct x.
    - simpl.
      destruct (decl_body c) eqn:Heq; rewrite H0; auto.
      eexists. simpl. split; eauto.
      sigma. rewrite -ren_shiftn. now sigma.

    - simpl.
      rewrite Nat.sub_0_r. specialize (H x).
      destruct nth_error eqn:Heq. 2: auto.
      destruct c0 as [na [b|] ty]; cbn in *.
      + destruct H as [b' [Hb Heq']].
        exists b'; intuition auto.
        rewrite -ren_shiftn. autorewrite with sigma in Heq' |- *.
        rewrite Nat.sub_0_r.
        rewrite -?subst_compose_assoc -inst_assoc.
        rewrite -[b.[_]]inst_assoc. rewrite Heq'.
        now sigma.
      + auto.
  Qed.

  Lemma shift_renaming Γ Δ ctx ctx' r :
    All2i (fun n decl decl' =>
      decl_body decl' =
      option_map (fun x => x.[ren (shiftn n r)]) (decl_body decl)
    ) ctx ctx' →
    renaming Γ Δ r →
    renaming (Γ ,,, ctx) (Δ ,,, ctx') (shiftn #|ctx| r).
  Proof.
    induction 1.
    - intros. rewrite shiftn0. apply H.
    - intros. simpl.
      rewrite shiftnS. apply shiftn1_renaming.
      + apply IHX; try lia. auto.
      + apply r0.
  Qed.

  Lemma renaming_shift_rho_fix_context:
    ∀ (mfix : mfixpoint term) (Γ Δ : list context_decl) (r : nat → nat),
      renaming Γ Δ r ->
      renaming (Γ ,,, rho_fix_context Γ mfix)
               (Δ ,,, rho_fix_context Δ (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
               (shiftn #|mfix| r).
  Proof.
    intros mfix Γ Δ r Hr.
    rewrite -{2}(rho_fix_context_length Γ mfix).
    eapply shift_renaming; auto.
    rewrite /rho_fix_context !fold_fix_context_rev.
    apply All2i_rev_ctx_inv, All2i_ctx_mapi.
    simpl. apply All2i_ctx_trivial; auto. now rewrite map_length.
  Qed.

  Lemma map_fix_rho_rename:
    ∀ (mfix : mfixpoint term) (i : nat) (l : list term),
      (∀ t' : term, size t' < size (mkApps (tFix mfix i) l)
                    → ∀ (Γ Δ : list context_decl) (r : nat → nat),
            renaming Γ Δ r
            → rename r (rho Γ t') = rho Δ (rename r t'))
      → ∀ (Γ Δ : list context_decl) (r : nat → nat),
        renaming Γ Δ r
        → map (map_def (rename r) (rename (shiftn #|mfix| r)))
              (map_fix rho Γ (fold_fix_context rho Γ [] mfix) mfix) =
          map_fix rho Δ (fold_fix_context rho Δ [] (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
                  (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix).
  Proof.
    intros mfix i l H Γ Δ r H2.
    rewrite /map_fix !map_map_compose !compose_map_def.
    apply map_ext_in => d /mfixpoint_size_In dsize.
    apply map_def_eq_spec.
    - specialize (H (dtype d)).
      forward H.
      + rewrite mkApps_size. simpl. lia.
      + now apply H.
    - specialize (H (dbody d)).
      forward H.
      + rewrite mkApps_size. simpl. lia.
      + apply (H). eapply renaming_shift_rho_fix_context; tea.
  Qed.

  Lemma All_IH {A size} (l : list A) k (P : A -> Type) :
    list_size size l <= k ->
    (forall x, size x < k -> P x) ->
    All P l.
  Proof.
    induction l in k |- *. 1: constructor.
    simpl. intros Hk IH.
    constructor.
    - apply IH. lia.
    - eapply (IHl k).
      + lia.
      + intros x sx. apply IH. lia.
  Qed.

  Lemma All_IH' {A size B size'} (f : A -> B) (l : list A) k (P : B -> Type) :
    list_size size l <= k ->
    (forall x, size' (f x) <= size x) ->
    (forall x, size' x < k -> P x) ->
    All (fun x => P (f x)) l.
  Proof.
    induction l in k |- *. 1: constructor.
    simpl. intros Hk Hs IH.
    constructor.
    - apply IH. specialize (Hs a). lia.
    - eapply (IHl k).
      + lia.
      + apply Hs.
      + apply IH.
  Qed.

  Lemma isConstruct_app_rename r t :
    isConstruct_app t = isConstruct_app (rename r t).
  Proof.
    unfold isConstruct_app. unfold decompose_app.
    generalize (@nil term) at 1.
    change (@nil term) with (map (rename r) []).
    generalize (@nil term).
    induction t; simpl; auto.
    intros l l0. specialize (IHt1 (t2 :: l) (t2 :: l0)).
    now rewrite IHt1.
  Qed.

  Lemma is_constructor_rename x l r : is_constructor x l = is_constructor x (map (rename r) l).
  Proof.
    rewrite /is_constructor nth_error_map.
    elim: nth_error_spec => //.
    move=> n hnth xl /=.
    now apply isConstruct_app_rename.
  Qed.

  Lemma isFixLambda_app_rename r t : ~~ isFixLambda_app t -> ~~ isFixLambda_app (rename r t).
  Proof.
    induction t; simpl; auto.
    destruct t1; simpl in *; auto.
  Qed.

  Lemma construct_cofix_rename r t : discr_construct_cofix t -> discr_construct_cofix (rename r t).
  Proof.
    destruct t; simpl; try congruence.
  Qed.

  Lemma All_size :
    forall A P l f,
      (forall x, f x < list_size f l -> P x) ->
      @All A P l.
  Proof.
    intros A P l f h.
    induction l in h |- *. 1: constructor.
    constructor.
    - apply h. cbn. lia.
    - apply IHl. intros x hx. apply h. cbn. lia.
  Qed.

  Lemma elim_kn_rename :
    forall r t,
      elim_kn (rename r t) = elim_kn t.
  Proof.
    intros r t.
    induction t.
    all: simpl. all: try reflexivity.
    all: auto.
  Qed.

  Lemma first_match_rename :
    forall k l t ui σ r f,
      All (fun r => All (elim_pattern #|r.(pat_context)|) r.(elims)) l ->
      first_match k l t = Some (ui, σ, r) ->
      first_match k l (rename f t) = Some (ui, map (rename f) σ, r).
  Proof.
    intros k l t ui σ r f hr e.
    induction l in ui, σ, r, e, hr |- *.
    - cbn in e. discriminate.
    - cbn - [ match_lhs ] in e. cbn - [ match_lhs ].
      inversion hr. subst.
      destruct match_lhs as [[? ?]|] eqn:e1.
      + noconf e. eapply match_lhs_rename with (r := f) in e1. 2: auto.
        rewrite e1. reflexivity.
      + eapply match_lhs_rename_None with (r := f) in e1. 2: auto.
        rewrite e1. eapply IHl. all: auto.
  Qed.

  Lemma first_match_rename_None :
    forall k l t f,
      All (fun r => All (elim_pattern #|r.(pat_context)|) r.(elims)) l ->
      first_match k l t = None ->
      first_match k l (rename f t) = None.
  Proof.
    intros k l t f hr e.
    induction l in e, hr |- *.
    - reflexivity.
    - cbn - [ match_lhs ] in e. cbn - [ match_lhs ].
      inversion hr. subst.
      destruct match_lhs as [[? ?]|] eqn:e1. 1: discriminate.
      eapply match_lhs_rename_None with (r := f) in e1. 2: auto.
      rewrite e1. eapply IHl. all: auto.
  Qed.

  Lemma not_lhs_rename :
    forall t r,
      not_lhs t ->
      not_lhs (rename r t).
  Proof.
    intros t r h.
    unfold not_lhs in *.
    intros [k [rd [[[ui σ] rw] [e1 e2]]]].
    apply h.
    exists k, rd.
    apply lookup_rewrite_decl_onrd in e1 as hrd.
    eapply all_rewrite_rules_on_rd in hrd.
    destruct (first_match _ _ t) as [[[? ?] ?]|] eqn:e3.
    - eapply first_match_rename with (f := r) in e3.
      2:{
        eapply All_impl. 1: eauto.
        intros rr [h1 [h2 h3]]. assumption.
      }
      rewrite e3 in e2. noconf e2.
      eexists. intuition auto.
    - eapply first_match_rename_None with (f := r) in e3.
      2:{
        eapply All_impl. 1: eauto.
        intros rr [h1 [h2 h3]]. assumption.
      }
      rewrite e3 in e2. discriminate.
  Qed.

  Lemma is_not_lhs_rename :
    forall r t,
      lhs_viewc t = is_not_lhs ->
      lhs_viewc (rename r t) = is_not_lhs.
  Proof.
    intros r t e.
    destruct (lhs_viewc t) eqn:h1. 1: discriminate.
    destruct (lhs_viewc (rename r t)) eqn:h2.
    1:{
      exfalso. clear e.
      eapply lhs_viewc_not_lhs in h1 as h.
      eapply not_lhs_rename with (r := r) in h.
      apply h. eexists k, rd, _. intuition eauto.
    }
    reflexivity.
  Qed.

  Lemma app_cong :
    forall {A} (a b c d : list A),
      a = c ->
      b = d ->
      a ++ b = c ++ d.
  Proof.
    intros A a b c d [] []. reflexivity.
  Qed.

  Lemma rho_rename Γ Δ r t :
    renaming Γ Δ r ->
    rename r (rho Γ t) = rho Δ (rename r t).
  Proof.
    (* intro h. *)
    revert Δ.
    funelim (rho Γ t).
    all: intros Δ h.
    all: rewrite ?map_terms_map.
    all: auto 2.

    (* lhs *)
    - eapply first_match_lookup_sound in e0 as et. 2: auto.
      apply lookup_rewrite_decl_onrd in e as hrd.
      eapply all_rewrite_rules_on_rd in hrd as ?.
      eapply first_match_rename with (f := r0) in e0 as e3.
      2:{
        eapply All_impl. 1: eauto.
        intros rr [h1 [h2 h3]]. assumption.
      }
      simp rho. destruct (lhs_viewc (rename _ _)) as [? ? ? ?|] eqn:hv.
      2:{
        exfalso.
        eapply lhs_viewc_not_lhs in hv.
        apply hv.
        eexists k, rd, _. intuition eauto.
      }
      clear hv.
      cbn. rewrite map_terms_map.
      eapply first_match_rd_sound in e3 as et3. 2: auto.
      apply lookup_rewrite_decl_onrd in e1 as hrd0.
      eapply first_match_rd_sound in e2 as et2. 2: auto.
      rewrite et3 in et2. clear et3.
      apply (f_equal elim_kn) in et2.
      apply first_match_subst_length in e2 as σl2.
      rewrite σl2 in et2.
      eapply first_match_rule_list in e2 as hr. destruct hr as [? ?].
      erewrite elim_kn_lhs in et2. 2-3: eauto.
      apply first_match_subst_length in e3 as σl3.
      rewrite σl3 in et2.
      eapply first_match_rule_list in e3 as hr. destruct hr as [? ?].
      erewrite elim_kn_lhs in et2. 2-3: eauto.
      apply some_inj in et2. subst k0.
      rewrite e in e1. apply some_inj in e1. subst rd0.
      rewrite e3 in e2. inversion e2.
      rewrite map_length. rewrite rename_subst0. f_equal.
      + rewrite !map_map_compose. solve_all.
        eapply All_size with (f := size).
        intros ? ?. eapply H. 2: auto.
        eapply first_match_subst_size in e0 as ?.
        lia.
      + apply rename_closedn. rewrite map_length. subst.
        rewrite map_length in σl3. rewrite σl3.
        eapply All_nth_error in e4. 2: eassumption.
        destruct e4 as [? [? ?]].
        eapply closedn_subst with (k := 0).
        * unfold symbols_subst. generalize (#|rd.(symbols)| - 0).
          generalize 0 at 2.
          intros n m. induction m in n |- *. 1: reflexivity.
          cbn. auto.
        * cbn. rewrite symbols_subst_length.
          replace (#|symbols rd| - 0) with #|symbols rd| by lia.
          assumption.

    (* Evar *)
    - cbn. simp rho lhs_viewc. f_equal.
      rewrite !map_map_compose. solve_all.
      eapply All_size with (f := size).
      intros t ht. eapply H. all: eauto.
      cbn. lia.

    (* Prod *)
    - simpl. simp rho lhs_viewc. repeat fold_rho.
      erewrite H. 2: eauto.
      erewrite H0. 1: eauto.
      eapply (shift_renaming _ _ [_] [_]). 2: auto.
      repeat constructor.

    (* Lambda *)
    - simpl. simp rho lhs_viewc. repeat fold_rho. erewrite H; eauto.
      erewrite H0; eauto.
      simpl. eapply (shift_renaming _ _ [_] [_]).
      + repeat constructor.
      + auto.

    (* Let *)
    - simpl. simp rho lhs_viewc. repeat fold_rho.
      rewrite /subst1 subst_inst.
      specialize (H _ _ h). specialize (H0 _ _ h).
      autorewrite with sigma in H, H0.
      erewrite <- H1.
      2:{
        eapply (shift_renaming _ _ [_] [_]). 2: auto.
        repeat constructor. simpl.
        sigma. now rewrite -H shiftn0.
      }
      sigma. apply inst_ext. rewrite H.
      rewrite -ren_shiftn. sigma. unfold Up. now sigma.

    (* Symbol (not lhs) *)
    - cbn. simp rho. rewrite Heq. cbn. reflexivity.

    (* Fix *)
    - simpl. simp rho lhs_viewc. simpl. simp rho.
      apply (f_equal (fun m => tFix m idx)).
      rewrite /map_fix !map_length !map_map_compose.
      solve_all.
      eapply All_size with (f := def_size size).
      intros d sd.
      rewrite !map_def_map_def.
      eapply map_def_eq_spec.
      1:{
        eapply H. all: eauto.
        destruct d. cbn in sd. cbn. unfold mfixpoint_size.
        lia.
      }
      eapply H. 2: eauto.
      1:{
        destruct d. cbn in sd. cbn. unfold mfixpoint_size.
        lia.
      }
      assert (em : #|mfix| = #|fold_fix_context rho Γ [] mfix|).
      { rewrite fold_fix_context_length /= //. }
      rewrite {2}em.
      eapply shift_renaming; auto.
      clear. generalize #|mfix|. induction mfix using rev_ind.
      + simpl. constructor.
      + intros. rewrite map_app !fold_fix_context_app. simpl. constructor.
        * simpl. reflexivity.
        * apply IHmfix.

    (* CoFix *)
    - simpl. simp rho lhs_viewc. simpl. simp rho.
      apply (f_equal (fun m => tCoFix m idx0)).
      rewrite /map_fix !map_length !map_map_compose.
      solve_all.
      eapply All_size with (f := def_size size).
      intros [dna dty dtm dr] sd. cbn in sd.
      rewrite !map_def_map_def.
      eapply map_def_eq_spec.
      1:{ eapply H. all: eauto. cbn. unfold mfixpoint_size. lia. }
      eapply H. 2: eauto.
      1:{ cbn. unfold mfixpoint_size. lia. }
      assert (em : #|mfix0| = #|fold_fix_context rho Γ [] mfix0|).
      { rewrite fold_fix_context_length /= //. }
      rewrite {2}em.
      eapply shift_renaming; auto.
      clear. generalize #|mfix0|. induction mfix0 using rev_ind.
      + simpl. constructor.
      + intros. rewrite map_app !fold_fix_context_app. simpl. constructor.
        * simpl. reflexivity.
        * apply IHmfix0.

    (* Rel (with body) *)
    - red in h. simpl.
      specialize (h n).
      destruct (nth_error Γ n) as [c|] eqn:e.
      2:{ cbn in Heq. discriminate. }
      simp rho lhs_viewc.
      cbn in Heq. apply some_inj in Heq. rewrite Heq in h.
      rewrite lift0_inst.
      destruct h as [b' [-> Hb']] => /=.
      rewrite lift0_inst.
      sigma. autorewrite with sigma in *. rewrite Hb'.
      reflexivity.

    (* Rel without body *)
    - simpl. simp rho lhs_viewc.
      red in h. specialize (h n).
      destruct nth_error eqn:e.
      2:{ cbn in Heq. discriminate. }
      cbn in Heq. apply some_inj in Heq. rewrite Heq in h.
      rewrite h. cbn. reflexivity.

    (* Undeclared rel *)
    - red in h. specialize (h n).
      destruct nth_error eqn:e.
      1:{ cbn in Heq. discriminate. }
      simp rho lhs_viewc. rewrite h.
      cbn. reflexivity.

    (* Fixpoint application *)
    - simp rho.
      destruct (lhs_viewc (rename _ _)).
      1:{
        eapply first_match_lookup_sound in e0 as et. 2: auto.
        apply (f_equal elim_kn) in et.
        apply first_match_subst_length in e0 as σl.
        rewrite σl in et.
        eapply first_match_rule_list in e0 as hr. destruct hr as [m ?].
        erewrite elim_kn_lhs in et. 2-3: eauto.
        cbn in et. rewrite rename_mkApps in et. rewrite elim_kn_mkApps in et.
        discriminate.
      }
      cbn [rename]. rewrite rename_mkApps.
      simpl.
      assert (eqargs : map (rename r) (map (rho Γ) (l ++ [a])) =
              map (rho Δ) (map (rename r) (l ++ [a]))).
      { rewrite !map_map_compose !map_app.
        apply app_cong.
        (* f_equal => /= //. *)
        2:{
          cbn. (* clear - Heq0 H1.
          f_equal. *)
          erewrite H1. all: eauto.
          cbn. lia.
        }
        solve_all.
        eapply All_size with (f := size).
        intros t ht. eapply H1. 2: auto.
        cbn. rewrite size_mkApps. lia.
      }
      destruct (rho_fix_elim Γ mfix i (l ++ [a])).
      * simpl. simp rho.
        rewrite /unfold_fix /map_fix nth_error_map e /= i0.
        simp rho; rewrite /map_fix !nth_error_map /= e /=.
        move: i0; rewrite /is_constructor -(map_app (rename r) l [a]) nth_error_map.
        destruct (nth_error_spec (l ++ [a]) (rarg d)) => /= //.
        rewrite -isConstruct_app_rename => -> //.
        rewrite rename_mkApps. rewrite eqargs.
        apply (f_equal (fun x => mkApps x _)).
        (* f_equal; auto. *)
        assert (Hbod: ∀ (Γ Δ : list context_decl) (r : nat → nat),
                  renaming Γ Δ r → rename r (rho Γ (dbody d)) = rho Δ (rename r (dbody d))).
        { intros. eapply H. all: eauto.
          eapply mfixpoint_size_nth_error in e.
          assumption.
        }
        assert (Hren : renaming (Γ ,,, rho_fix_context Γ mfix)
                          (Δ ,,, rho_fix_context Δ (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix))
                          (shiftn #|mfix| r)).
        { now apply renaming_shift_rho_fix_context. }
        specialize (Hbod _ _ _ Hren).
        rewrite -Hbod.
        rewrite !subst_inst.
        { sigma. fold_rho. eapply inst_ext.
          rewrite -ren_shiftn. sigma.
          rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
          rewrite subst_consn_compose compose_ids_l. apply subst_consn_proper => //.
          rewrite map_fix_subst //.
          - intros m. simp rho lhs_viewc. simpl. simp rho.
            reflexivity.
          - clear - H1 h Hren.
            unfold fix_subst. autorewrite with len. generalize #|mfix| at 1 4.
            induction n; simpl; auto.
            rewrite IHn. clear IHn. f_equal; auto.
            specialize (H1 Γ (tFix mfix n)) as Hbod.
            forward Hbod.
            { simpl. rewrite size_mkApps. cbn. lia. }
            simp rho lhs_viewc. simpl. simp rho.
            specialize (Hbod _ _ h).
            simpl in Hbod. simp rho lhs_viewc in Hbod.
            simpl in Hbod; simp rho lhs_viewc in Hbod.
            rewrite -Hbod.
            rewrite map_length. f_equal.
            rewrite !map_map_compose. apply map_ext.
            intros []; unfold map_def; cbn.
            rewrite !rename_inst. f_equal. apply inst_ext.
            apply ren_shiftn.
        }

      * simp rho. simpl. simp rho.
        rewrite /unfold_fix /map_fix !nth_error_map.
        destruct (nth_error mfix i) eqn:hfix => /=.
        -- assert(is_constructor (rarg d) (l ++ [a]) = false).
            { red in i0; unfold negb in i0.
              destruct is_constructor; auto.
            }
          rewrite H2.
          rewrite -(map_app (rename r) l [a]) -is_constructor_rename H2 //.
          rewrite rename_mkApps. clear - h H1 eqargs.
          f_equal.
          ++ simpl. f_equal.
            autorewrite with len.
            eapply (map_fix_rho_rename mfix i l); eauto.
            intros. eapply H1. all: eauto.
            cbn. lia.
          ++ apply eqargs.
        -- rewrite rename_mkApps.
          clear - eqargs h H1.
          f_equal; auto.
          2:{ now rewrite -(map_app (rename r) _ [_]). }
          simpl. f_equal. autorewrite with len.
          apply (map_fix_rho_rename mfix i l); eauto.
          intros; eapply H1; simpl; try lia. auto.

    (* Lambda abstraction (empty list) *)
    - set (l' := []) in *.
      cbn - [l'].
      rewrite (rename_mkApps _ (tLambda _ _ _)). cbn - [l'].
      rewrite tApp_mkApps mkApps_nested.
      rewrite -(map_app (rename r) _ [_]).
      rewrite rho_app_lambda'.
      simpl.
      rewrite -H. 1: auto.
      rewrite -H0. 1: auto.
      rewrite -H1.
      { eapply shiftn1_renaming; auto. }
      rewrite rename_inst /subst1 subst_inst.
      sigma. apply inst_ext.
      rewrite -ren_shiftn. sigma.
      unfold Up. now sigma.

    (* Lambda abstraction (cons, the two proofs are the same, shame) *)
    - set (l' := t0 :: l) in *.
      cbn - [l'].
      rewrite (rename_mkApps _ (tLambda _ _ _)). cbn - [l'].
      rewrite tApp_mkApps mkApps_nested.
      rewrite -(map_app (rename r) _ [_]).
      rewrite rho_app_lambda'.
      simpl.
      rewrite rename_inst /subst1 subst_inst.
      rewrite inst_mkApps.
      specialize (H1 (shiftn 1 r) (vass na (rho Δ ty.[ren r]) :: Δ)).
      forward H1.
      { eapply shiftn1_renaming; auto. }
      sigma.
      specialize (H r Δ).
      forward H by assumption.
      autorewrite with sigma in H, H1.
      f_equal.
      + rewrite -H1. sigma. apply inst_ext.
        rewrite H.
        rewrite -ren_shiftn. sigma.
        unfold Up. now sigma.
      + rewrite !map_map_compose. solve_all.
        apply All_app_inv.
        * eapply All_size with (f := size).
          intros t ht. cbn in H2.
          specialize (H2 Γ t).
          forward H2.
          { rewrite size_mkApps. lia. }
          specialize H2 with (1 := eq_refl).
          specialize H2 with (1 := h).
          autorewrite with sigma in H2. auto.
        * constructor. 2: constructor.
          specialize (H2 Γ a0).
          forward H2.
          { cbn. lia. }
          specialize H2 with (1 := eq_refl).
          specialize H2 with (1 := h).
          autorewrite with sigma in H2. auto.

    (* Application *)
    - simp rho. eapply is_not_lhs_rename with (r := r) in Heq0 as e.
      rewrite e.
      simpl. repeat fold_rho.
      pose proof (isFixLambda_app_rename r _ i0) as H3.
      simpl in H3.
      rewrite (view_lambda_fix_app_other (rename r t0) (rename r a1) H3). simpl.
      erewrite H, H0. all: eauto.

    (* Ill-defined constant *)
    - simpl. simp rho lhs_viewc.
      rewrite Heq. cbn. reflexivity.

    (* Ill-defined constant *)
    - simpl. simp rho lhs_viewc.
      rewrite Heq. cbn. reflexivity.

    (* Undeclared constant *)
    - simpl. simp rho lhs_viewc.
      rewrite Heq. cbn. reflexivity.

    (* Constant unfolding *)
    - simpl. simp rho lhs_viewc.
      rewrite Heq0. cbn. rewrite Heq. cbn.
      rewrite rename_inst inst_closed0 //.
      apply declared_decl_closed in Heq0 => //.
      hnf in Heq0. rewrite Heq in Heq0.
      rewrite closedn_subst_instance_constr; auto.
      now move/andP: Heq0 => [-> _].

    (* Constant with no body *)
    - simpl. simp rho lhs_viewc.
      rewrite Heq0. cbn. rewrite Heq. cbn.
      reflexivity.

    (* Cofix iota reduction *)
    - simp rho.
      eapply is_not_lhs_rename with (r := r) in Heq as er.
      rewrite er.
      cbn [rename]. simp rho.
      repeat fold_rho.
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename (symmetry e)) as hd.
      rewrite <- decapp' in hd. noconf hd.
      assert (
        map (on_snd (rename r)) (map (λ x : nat × term, (fst x, rho Γ (snd x))) brs) =
        (map (λ x : nat × term, (fst x, rho Δ (snd x))) (map (on_snd (rename r)) brs))
      ).
      { rewrite !map_map_compose /on_snd. solve_all.
        eapply All_size with (f := (fun x => size (snd x))).
        intros [? ?]. cbn. intros ?.
        f_equal. eapply H1. 2: auto.
        cbn. lia.
      }
      (* The proof diverges here *)
      simpl. simp view_construct_cofix.
      simpl. simp rho. repeat fold_rho.
      rewrite /map_fix !map_map_compose.
      rewrite /unfold_cofix !nth_error_map. clear H5.
      apply symmetry, decompose_app_inv in e. subst c.
      specialize H4 with (1 := h).
      simp rho in H4.
      rewrite !rename_mkApps in H4.
      simpl in H4. rewrite <- !fold_rho in H4. simp rho in H4.
      apply mkApps_eq_inj in H4 as [Heqcof Heq0] => //.
      noconf Heqcof. simpl in H4. noconf H4.
      autorewrite with len in H4.
      rewrite /map_fix !map_map_compose in H4.
      case efix: (nth_error mfix idx) => [d|] /= //.
      + rewrite rename_mkApps !map_map_compose compose_map_def /on_snd.
        f_equal.
        * erewrite H; eauto.
        * {
          f_equal => //.
          - rewrite !subst_inst. sigma.
            apply map_eq_inj in H4.
            epose proof (nth_error_all efix H4) as hh.
            simpl in hh. apply (f_equal dbody) in hh.
            simpl in hh. autorewrite with sigma in hh.
            rewrite -hh. sigma.
            apply inst_ext.
            rewrite -ren_shiftn. sigma.
            rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
            + rewrite subst_consn_compose compose_ids_l.
              apply subst_consn_proper => //.
              rewrite map_cofix_subst' //.
              * intros ?. simp rho lhs_viewc. simpl; f_equal. now simp rho.
              * {
                rewrite map_cofix_subst' //.
                - simpl. move=> ? ; f_equal.
                  simp rho lhs_viewc. simpl. simp rho.
                  f_equal. rewrite /map_fix.
                  rewrite !map_map_compose !compose_map_def.
                  apply map_ext => x; apply map_def_eq_spec => //.
                - rewrite !map_map_compose.
                  unfold cofix_subst. generalize #|mfix|.
                  clear -H4.
                  induction n; simpl; auto. f_equal; auto.
                  simp rho lhs_viewc. simpl. simp rho. f_equal.
                  rewrite /map_fix !map_map_compose.
                  autorewrite with len.
                  solve_all.
                  rewrite -H.
                  apply map_def_eq_spec; simpl.
                  + now sigma.
                  + sigma.
                    rewrite -ren_shiftn. rewrite up_Upn. reflexivity.
              }
            + now autorewrite with len.
          - now rewrite !map_map_compose in Heq0.
        }
        * simpl. solve_all.
          eapply All_size with (f := (fun x => size (snd x))).
          intros [? ?]. cbn. intros ?.
          f_equal. eapply H1. 2: auto.
          cbn. lia.
      + rewrite map_map_compose /on_snd. f_equal; auto.
        * simp rho.
          rewrite !rename_mkApps /= !map_map_compose !compose_map_def /=.
          repeat fold_rho.
          simp rho.
          f_equal.
          -- f_equal.
             rewrite /map_fix map_map_compose. rewrite -H4.
             autorewrite with len. reflexivity.
          -- now rewrite -Heq0 !map_map_compose.
        * simpl. solve_all.
          eapply All_size with (f := (fun x => size (snd x))).
          intros [? ?]. cbn. intros ?.
          f_equal. eapply H1. 2: auto.
          cbn. lia.

    (* Pattern matching *)
    - simp rho.
      eapply is_not_lhs_rename with (r := r) in Heq0 as er.
      rewrite er.
      cbn [rename]. simp rho.
      repeat fold_rho.
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename (symmetry e)) as hd.
      rewrite <- decapp' in hd. noconf hd.
      assert (
        map (on_snd (rename r)) (map (λ x : nat × term, (fst x, rho Γ (snd x))) brs) =
        (map (λ x : nat × term, (fst x, rho Δ (snd x))) (map (on_snd (rename r)) brs))
      ).
      { rewrite !map_map_compose /on_snd. solve_all.
        eapply All_size with (f := (fun x => size (snd x))).
        intros [? ?]. cbn. intros ?.
        f_equal. eapply H1. 2: auto.
        cbn. lia.
      }
      (* The proof diverges here *)
      simpl.
      pose proof (construct_cofix_rename r t1 d) as H4.
      destruct (view_construct_cofix (rename r t1)); simpl in H4 => //.
      simp rho. simpl. rewrite -H3. repeat fold_rho. erewrite H, H0.
      all: eauto.

    (* Construct iota reduction *)
    - simp rho.
      eapply is_not_lhs_rename with (r := r) in Heq0 as er.
      rewrite er.
      cbn [rename]. simp rho.
      repeat fold_rho.
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename (symmetry e)) as hd.
      rewrite <- decapp' in hd. noconf hd.
      assert (
        map (on_snd (rename r)) (map (λ x : nat × term, (fst x, rho Γ (snd x))) brs) =
        (map (λ x : nat × term, (fst x, rho Δ (snd x))) (map (on_snd (rename r)) brs))
      ).
      { rewrite !map_map_compose /on_snd. solve_all.
        eapply All_size with (f := (fun x => size (snd x))).
        intros [? ?]. cbn. intros ?.
        f_equal. eapply H1. 2: auto.
        cbn. lia.
      }
      (* The proof diverges here *)
      simpl. simp view_construct_cofix.
      simpl. simp rho. repeat fold_rho.
      rewrite Heq. simpl.
      simp rho. rewrite -H3.
      (* Reduction *)
      rewrite /iota_red /= -map_skipn rename_mkApps !nth_map //.
      f_equal. rewrite !map_skipn.
      clear H2. apply symmetry, decompose_app_inv in e. subst c.
      specialize H0 with (2 := h).
      specialize (H0 (mkApps (tConstruct c0 u i0) l)).
      forward H0.
      { cbn. lia. }
      rewrite !rho_app_construct !rename_mkApps in H0.
      simpl in H0. rewrite rho_app_construct in H0.
      apply mkApps_eq_inj in H0 as [_ ?] => //. congruence.

    (* Construct without iota reduction *)
    - simp rho.
      eapply is_not_lhs_rename with (r := r) in Heq0 as er.
      rewrite er.
      cbn [rename]. simp rho.
      repeat fold_rho.
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename (symmetry e)) as hd.
      rewrite <- decapp' in hd. noconf hd.
      assert (
        map (on_snd (rename r)) (map (λ x : nat × term, (fst x, rho Γ (snd x))) brs) =
        (map (λ x : nat × term, (fst x, rho Δ (snd x))) (map (on_snd (rename r)) brs))
      ).
      { rewrite !map_map_compose /on_snd. solve_all.
        eapply All_size with (f := (fun x => size (snd x))).
        intros [? ?]. cbn. intros ?.
        f_equal. eapply H1. 2: auto.
        cbn. lia.
      }
      (* The proof diverges here *)
      simpl. simp view_construct_cofix.
      simpl. simp rho. repeat fold_rho.
      rewrite Heq. simpl.
      simp rho. rewrite -H3.
      repeat fold_rho.
      erewrite H, H0. all: auto.

    (* Proj construct/cofix reduction *)
    - simp rho.
      eapply is_not_lhs_rename with (r := r) in Heq as er.
      rewrite er.
      cbn [rename]. simp rho.
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename (symmetry e)) as e'.
      rewrite <- decapp' in e'.
      noconf e'. simpl.
      simp view_construct_cofix. simpl.
      simp rho.
      repeat fold_rho.
      clear H3. symmetry in e.
      apply decompose_app_inv in e. subst c0.
      specialize H2 with (1 := h).
      rewrite rename_mkApps in H2.
      (* Proof divergence *)
      rewrite !nth_error_map.
      destruct nth_error eqn:hnth.
      2:{
        cbn. rewrite H2. rewrite rename_mkApps. auto.
      }
      simpl. rewrite rename_mkApps.
      f_equal; auto.
      simpl in H2. simp rho in H2. rewrite rename_mkApps in H2.
      eapply mkApps_eq_inj in H2 as [Hcof Hargs] => //.
      f_equal; auto. simpl in Hcof. noconf Hcof. simpl in H2.
      noconf H2.
      rewrite /map_fix !map_map_compose in H2.
      apply map_eq_inj in H2.
      epose proof (nth_error_all hnth H2) as H3.
      simpl in H3. apply (f_equal dbody) in H3.
      simpl in H3. autorewrite with sigma in H3.
      sigma. autorewrite with len in H2, H3.
      rewrite -H3. sigma.
      apply inst_ext.
      rewrite -ren_shiftn. sigma.
      rewrite Upn_comp ?map_length ?fix_subst_length ?map_length //.
      2: now autorewrite with len.
      rewrite subst_consn_compose compose_ids_l.
      apply subst_consn_proper => //.
      rewrite map_cofix_subst' //.
      { intro. simp rho lhs_viewc. simpl. simp rho. reflexivity. }
      rewrite map_cofix_subst' //.
      { intro. simp rho lhs_viewc. simpl. simp rho. reflexivity. }
      rewrite map_cofix_subst' //.
      rewrite !map_map_compose.
      unfold cofix_subst. generalize #|mfix|.
      clear -H2.
      induction n; simpl; auto. f_equal; auto.
      simp rho lhs_viewc. simpl. simp rho. f_equal.
      rewrite /map_fix !map_map_compose.
      autorewrite with len.
      solve_all.
      rewrite -H.
      apply map_def_eq_spec; simpl. 1: now sigma.
      sigma.
      rewrite -ren_shiftn. rewrite up_Upn. reflexivity.

    (* Proj construct/cofix reduction *)
    - simp rho.
      eapply is_not_lhs_rename with (r := r) in Heq0 as er.
      rewrite er.
      cbn [rename]. simp rho.
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename (symmetry e)) as e'.
      rewrite <- decapp' in e'.
      noconf e'. simpl.
      (* Proof divergence *)
      pose proof (construct_cofix_rename r t1 d) as H4.
      destruct (view_construct_cofix (rename r t1)); simpl in H4 => //.
      simp rho. repeat fold_rho. erewrite H. all: auto.

    (* Proj construct/cofix reduction *)
    - simp rho.
      eapply is_not_lhs_rename with (r := r) in Heq as er.
      rewrite er.
      cbn [rename]. simp rho.
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename (symmetry e)) as e'.
      rewrite <- decapp' in e'.
      noconf e'. simpl.
      (* Proof divergence *)
      simp view_construct_cofix. simpl.
      simp rho.
      repeat fold_rho.
      clear H0. rewrite map_terms_map in e0.
      clear H1. symmetry in e.
      apply decompose_app_inv in e. subst c0.
      specialize H with (1 := h).
      rewrite rename_mkApps in H.
      rewrite !nth_error_map.
      rewrite nth_error_map in e0.
      destruct (nth_error l _) eqn:hnth. 2: discriminate.
      cbn in e0. apply some_inj in e0. subst.
      simpl.
      destruct eq_inductive eqn:eqi.
      2:{
        cbn. rewrite H. rewrite rename_mkApps. reflexivity.
      }
      simp rho in H. rewrite rename_mkApps in H.
      eapply mkApps_eq_inj in H as [_ Hargs] => //.
      rewrite !map_map_compose in Hargs.
      eapply map_eq_inj in Hargs.
      apply (nth_error_all hnth Hargs).

   (* Proj construct/cofix reduction *)
    - simp rho.
      eapply is_not_lhs_rename with (r := r) in Heq as er.
      rewrite er.
      cbn [rename]. simp rho.
      destruct inspect as [[f' a'] decapp'].
      epose proof (decompose_app_rename (symmetry e)) as e'.
      rewrite <- decapp' in e'.
      noconf e'. simpl.
      (* Proof divergence *)
      simp view_construct_cofix. simpl.
      simp rho.
      repeat fold_rho.
      clear H0. rewrite map_terms_map in e0.
      clear H1. symmetry in e.
      apply decompose_app_inv in e. subst c0.
      specialize H with (1 := h).
      rewrite rename_mkApps in H.
      rewrite !nth_error_map.
      rewrite nth_error_map in e0.
      destruct (nth_error l _) eqn:hnth. 1: discriminate.
      simpl.
      rewrite H. rewrite rename_mkApps. reflexivity.
  Qed.

  Lemma rho_lift0 Γ Δ t : lift0 #|Δ| (rho Γ t) = rho (Γ ,,, Δ) (lift0 #|Δ| t).
  Proof.
    rewrite !lift_rename. apply rho_rename.
    red. intros x. destruct nth_error eqn:Heq.
    - unfold lift_renaming. simpl. rewrite Nat.add_comm.
      rewrite nth_error_app_ge. 1: lia.
      rewrite Nat.add_sub Heq.
      destruct c as [na [b|] ty]; simpl in *; auto.
      exists b. split; eauto.
      rewrite -ren_shiftk. rewrite shiftk_compose. reflexivity.
    - unfold lift_renaming. simpl. rewrite Nat.add_comm.
      rewrite nth_error_app_ge. 1: lia.
      now rewrite Nat.add_sub Heq.
  Qed.

  Section rho_ctx.
    Context (Δ : context).
    Fixpoint rho_ctx_over Γ :=
      match Γ with
      | [] => []
      | {| decl_name := na; decl_body := None; decl_type := T |} :: Γ =>
        let Γ' := rho_ctx_over Γ in
        vass na (rho (Δ ,,, Γ') T) :: Γ'
      | {| decl_name := na; decl_body := Some b; decl_type := T |} :: Γ =>
        let Γ' := rho_ctx_over Γ in
        vdef na (rho (Δ ,,, Γ') b) (rho (Δ ,,, Γ') T) :: Γ'
      end.
  End rho_ctx.

  Definition rho_ctx Γ := (rho_ctx_over [] Γ).

  Lemma rho_ctx_over_length Δ Γ : #|rho_ctx_over Δ Γ| = #|Γ|.
  Proof.
    induction Γ; simpl; auto. destruct a. destruct decl_body; simpl; auto with arith.
  Qed.

  Lemma rho_ctx_over_app Γ' Γ Δ :
    rho_ctx_over Γ' (Γ ,,, Δ) =
    rho_ctx_over Γ' Γ ,,, rho_ctx_over (Γ' ,,, rho_ctx_over Γ' Γ) Δ.
  Proof.
    induction Δ; simpl; auto.
    destruct a as [na [b|] ty].
    - simpl. f_equal; auto.
      now rewrite IHΔ app_context_assoc.
    - now rewrite IHΔ app_context_assoc.
  Qed.

  Lemma rho_ctx_app Γ Δ : rho_ctx (Γ ,,, Δ) = rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) Δ.
  Proof.
    induction Δ; simpl; auto.
    destruct a as [na [b|] ty].
    - simpl. f_equal.
      + rewrite app_context_nil_l. now rewrite IHΔ.
      + auto.
    - rewrite app_context_nil_l. now rewrite IHΔ.
  Qed.

  Lemma fold_fix_context_over_acc Γ m acc :
    rho_ctx_over (rho_ctx Γ ,,, acc)
                 (List.rev (mapi_rec (λ (i : nat) (d : def term), vass (dname d) ((lift0 i) (dtype d))) m #|acc|))
                 ++ acc =
    fold_fix_context rho (rho_ctx Γ) acc m.
  Proof.
    induction m in Γ, acc |- *; simpl; auto.
    rewrite rho_ctx_over_app. simpl.
    unfold app_context. unfold app_context in IHm.
    erewrite <- IHm.
    rewrite - app_assoc. cbn. f_equal.
    - f_equal. f_equal. f_equal. rewrite rho_lift0. auto.
    - repeat f_equal. rewrite rho_lift0; auto.
  Qed.

  Lemma fold_fix_context_rho_ctx Γ m :
    rho_ctx_over (rho_ctx Γ) (fix_context m) =
    fold_fix_context rho (rho_ctx Γ) [] m.
  Proof.
    rewrite <- fold_fix_context_over_acc; now rewrite ?app_nil_r.
  Qed.

  Definition fold_fix_context_alt Γ m :=
    mapi (fun k def => vass def.(dname) (lift0 k (rho Γ def.(dtype)))) m.

  Lemma fix_context_fold Γ m :
    fix_context (map (map_def (rho (rho_ctx Γ))
                              (rho (rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) (fix_context m)))) m) =
    rho_ctx_over (rho_ctx Γ) (fix_context m).
  Proof.
    unfold fix_context. rewrite mapi_map. simpl.
    rewrite fold_fix_context_rho_ctx; auto.
    rewrite fold_fix_context_rev_mapi. simpl.
    now rewrite app_nil_r.
  Qed.

  Lemma fix_context_map_fix Γ mfix :
    fix_context (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix) =
    rho_ctx_over (rho_ctx Γ) (fix_context mfix).
  Proof.
    rewrite - fix_context_fold.
    unfold map_fix. f_equal.
    f_equal. f_equal. now rewrite fix_context_fold.
  Qed.

  Lemma rho_cofix_subst Γ mfix :
    cofix_subst (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix)
    = (map (rho (rho_ctx Γ)) (cofix_subst mfix)).
  Proof.
    unfold cofix_subst. unfold map_fix at 2. rewrite !map_length.
    induction #|mfix|. 1: reflexivity.
    simpl. simp rho lhs_viewc. simpl.
    simp rho.
    rewrite - fold_fix_context_rho_ctx. f_equal. apply IHn.
  Qed.

  Lemma rho_fix_subst Γ mfix :
    fix_subst (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix)
    = (map (rho (rho_ctx Γ)) (fix_subst mfix)).
  Proof.
    unfold fix_subst. unfold map_fix at 2. rewrite !map_length.
    induction #|mfix|. 1: reflexivity.
    simpl. simp rho lhs_viewc. simpl. simp rho.
    rewrite - fold_fix_context_rho_ctx. f_equal. apply IHn.
  Qed.

  Lemma nth_error_cofix_subst mfix n b :
    nth_error (cofix_subst mfix) n = Some b ->
    b = tCoFix mfix (#|mfix| - S n).
  Proof.
    unfold cofix_subst.
    generalize #|mfix|. induction n0 in n, b |- *.
    - simpl.
      destruct n; simpl; congruence.
    - destruct n; simpl.
      + intros [= <-]. f_equal.
        destruct n0; simpl; try reflexivity.
      + intros H. now specialize (IHn0 _ _ H).
  Qed.

  Lemma nth_error_fix_subst mfix n b :
    nth_error (fix_subst mfix) n = Some b ->
    b = tFix mfix (#|mfix| - S n).
  Proof.
    unfold fix_subst.
    generalize #|mfix|. induction n0 in n, b |- *.
    - simpl.
      destruct n; simpl; congruence.
    - destruct n; simpl.
      + intros [= <-]. f_equal.
        destruct n0; simpl; try reflexivity.
      + intros H. now specialize (IHn0 _ _ H).
  Qed.

  Lemma ctxmap_cofix_subst:
    ∀ (Γ' : context) (mfix1 : mfixpoint term),
      ctxmap (Γ' ,,, fix_context mfix1) Γ' (cofix_subst mfix1 ⋅n ids).
  Proof.
    intros Γ' mfix1.
    intros x d' Hnth.
    destruct (leb_spec_Set #|fix_context mfix1| x).
    - rewrite nth_error_app_ge // in Hnth.
      rewrite fix_context_length in l Hnth.
      destruct d' as [na [b'|] ty]; simpl; auto.
      rewrite subst_consn_ge cofix_subst_length //.
      unfold ids. eexists _, _; split; eauto.
      rewrite Hnth. split; simpl; eauto.
      apply inst_ext.
      rewrite /subst_compose. simpl. intros v.
      rewrite subst_consn_ge ?cofix_subst_length. 1: lia.
      unfold shiftk. f_equal. lia.
    - rewrite nth_error_app_lt in Hnth => //.
      pose proof (fix_context_assumption_context mfix1).
      destruct d' as [na [b'|] ty]; simpl; auto.
      elimtype False. eapply nth_error_assumption_context in H; eauto.
      simpl in H; discriminate.
  Qed.

  Lemma ctxmap_fix_subst:
    ∀ (Γ' : context) (mfix1 : mfixpoint term),
      ctxmap (Γ' ,,, fix_context mfix1) Γ' (fix_subst mfix1 ⋅n ids).
  Proof.
    intros Γ' mfix1.
    intros x d' Hnth.
    destruct (leb_spec_Set #|fix_context mfix1| x).
    - rewrite nth_error_app_ge // in Hnth.
      rewrite fix_context_length in l Hnth.
      destruct d' as [na [b'|] ty]; simpl; auto.
      rewrite subst_consn_ge fix_subst_length //.
      unfold ids. eexists _, _; split; eauto.
      rewrite Hnth. split; simpl; eauto.
      apply inst_ext.
      rewrite /subst_compose. simpl. intros v.
      rewrite subst_consn_ge ?fix_subst_length. 1: lia.
      unfold shiftk. f_equal. lia.
    - rewrite nth_error_app_lt in Hnth => //.
      pose proof (fix_context_assumption_context mfix1).
      destruct d' as [na [b'|] ty]; simpl; auto.
      elimtype False. eapply nth_error_assumption_context in H; eauto.
      simpl in H; discriminate.
  Qed.

  Lemma rho_triangle_All_All2_ind:
    ∀ (Γ : context) (brs : list (nat * term)),
    pred1_ctx Σ Γ (rho_ctx Γ) →
    All (λ x : nat * term, pred1_ctx Σ Γ (rho_ctx Γ) → pred1 Σ Γ (rho_ctx Γ) (snd x) (rho (rho_ctx Γ) (snd x)))
        brs →
    All2 (on_Trel_eq (pred1 Σ Γ (rho_ctx Γ)) snd fst) brs
         (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs).
  Proof.
    intros. rewrite - {1}(map_id brs). eapply All2_map, All_All2; eauto.
  Qed.

  Lemma rho_triangle_All_All2_ind_noeq:
    ∀ (Γ Γ' : context) (brs0 brs1 : list (nat * term)),
      pred1_ctx Σ Γ Γ' →
      All2 (on_Trel_eq (λ x y : term, (pred1 Σ Γ Γ' x y * pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type) snd
                       fst) brs0 brs1 ->
      All2 (on_Trel (pred1 Σ Γ' (rho_ctx Γ)) snd) brs1 (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs0).
  Proof.
    intros. rewrite - {1}(map_id brs1). eapply All2_map, All2_sym, All2_impl; pcuic.
  Qed.

  Lemma All2_local_env_pred_fix_ctx P (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) :
     All2_local_env
       (on_decl
          (on_decl_over (λ (Γ0 Γ'0 : context) (t t0 : term), P Γ'0 (rho_ctx Γ0) t0 (rho (rho_ctx Γ0) t)) Γ Γ'))
       (fix_context mfix0) (fix_context mfix1)
     → All2_local_env (on_decl (on_decl_over P Γ' (rho_ctx Γ))) (fix_context mfix1)
                      (fix_context (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix0)) mfix0)).
  Proof.
    intros.
    rewrite fix_context_map_fix.
    revert X. generalize (fix_context mfix0) (fix_context mfix1).
    induction 1; simpl; constructor; auto.
    - unfold on_decl, on_decl_over in p |- *.
      now rewrite rho_ctx_app in p.
    - unfold on_decl, on_decl_over in p |- *.
      now rewrite rho_ctx_app in p.
  Qed.

   Lemma All2_local_env_sym P Γ Γ' Δ Δ' :
    All2_local_env (on_decl (on_decl_over (fun Γ Γ' t t' => P Γ' Γ t' t) Γ' Γ)) Δ' Δ ->
    All2_local_env (on_decl (on_decl_over P Γ Γ')) Δ Δ'.
  Proof.
    induction 1; constructor; eauto.
  Qed.

  Lemma wf_rho_fix_subst Γ Γ' mfix0 mfix1 :
    #|mfix0| = #|mfix1| ->
    pred1_ctx Σ Γ' (rho_ctx Γ) ->
    All2_local_env
      (on_decl
         (on_decl_over
            (λ (Γ Γ' : context) (t t0 : term), pred1 Σ Γ' (rho_ctx Γ) t0 (rho (rho_ctx Γ) t)) Γ
            Γ')) (fix_context mfix0) (fix_context mfix1) ->
    All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                  (λ x : def term, (dname x, rarg x))
                  (λ (Γ Γ' : context) (x y : term), (pred1 Σ Γ Γ' x y *
                                                     pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type)
                  mfix0 mfix1 ->
    psubst Σ Γ' (rho_ctx Γ) (fix_subst mfix1) (map (rho (rho_ctx Γ)) (fix_subst mfix0))
           (fix_context mfix1) (rho_ctx_over (rho_ctx Γ) (fix_context mfix0)).
  Proof.
    intros Hlen Hred Hctxs a0. pose proof Hctxs as Hctxs'.
    pose proof a0 as a0'. apply All2_rev in a0'.
    revert Hctxs.
    unfold fix_subst, fix_context. simpl.
    revert a0'. rewrite -Hlen -(@List.rev_length _ mfix0).
    rewrite !rev_mapi. unfold mapi.
    assert (#|mfix0| >= #|List.rev mfix0|) by (rewrite List.rev_length; lia).
    assert (#|mfix1| >= #|List.rev mfix1|) by (rewrite List.rev_length; lia).
    assert (He :0 = #|mfix0| - #|List.rev mfix0|) by (rewrite List.rev_length; auto with arith).
    assert (He' :0 = #|mfix1| - #|List.rev mfix1|) by (rewrite List.rev_length; auto with arith).
    rewrite {2 6}He {3 6}He'. clear He He'. revert H H0.
    assert (#|List.rev mfix0| = #|List.rev mfix1|) by (rewrite !List.rev_length; lia).
    revert H.
    generalize (List.rev mfix0) (List.rev mfix1).
    intros l l' Heqlen Hlen' Hlen'' H. induction H. 1: constructor.
    simpl.
    simpl in *.
    replace (S (#|mfix0| - S #|l|)) with (#|mfix0| - #|l|) by lia.
    replace (S (#|mfix1| - S #|l'|)) with (#|mfix1| - #|l'|) by lia.
    rewrite -Hlen.
    assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l|)) = #|l|) by lia.
    assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l'|)) = #|l'|) by lia.
    rewrite H0 H1.
    intros. depelim Hctxs.
    - red in o. simpl in H2, H3. noconf H2; noconf H3.
      red in o. noconf Heqlen. simpl in H.
      rewrite -H.
      econstructor.
      + unfold mapi in IHAll2.
        forward IHAll2 by lia.
        forward IHAll2 by lia.
        forward IHAll2 by lia. rewrite -H in IHAll2.
        rewrite -Hlen in IHAll2.
        apply IHAll2; clear IHAll2.
        rewrite -H in Hctxs.
        apply Hctxs; clear Hctxs.
      + clear IHAll2 Hctxs. destruct r.
        destruct o0. destruct p. destruct p.
        simpl in *. simpl in H.
        rewrite H in o |- *.
        rewrite rho_ctx_app in o. apply o.
      + simp rho lhs_viewc. simpl. simp rho.
        econstructor.
        * eauto.
        * clear Hctxs o IHAll2.
          rewrite -fold_fix_context_rho_ctx.
          eapply All2_local_env_pred_fix_ctx. eapply Hctxs'.
        * eapply All2_mix.
          -- rewrite -fold_fix_context_rho_ctx.
             clear IHAll2 Hctxs H o r.
             eapply All2_mix_inv in a0. destruct a0.
             eapply All2_sym. unfold on_Trel.
             eapply All2_mix_inv in a. destruct a.
             eapply All2_map_left. simpl. auto.
          -- clear IHAll2 Hctxs H o r.
             eapply All2_mix_inv in a0. destruct a0.
             eapply All2_sym. unfold on_Trel.
             eapply All2_mix_inv in a0. destruct a0.
             eapply All2_mix_inv in a0. destruct a0.
             eapply All2_mix.
             ++ rewrite -fold_fix_context_rho_ctx.
                rewrite fix_context_map_fix. simpl.
                rewrite rho_ctx_app in a2. unfold on_Trel.
                eapply All2_map_left. simpl. eapply a2.
             ++ eapply All2_map_left. simpl. solve_all.
    - simpl in H2. noconf H2.
  Qed.

(* TODO generalize fix/cofix subst by tFix/tCofix constructor! *)

  Lemma wf_rho_cofix_subst Γ Γ' mfix0 mfix1 :
    #|mfix0| = #|mfix1| ->
    pred1_ctx Σ Γ' (rho_ctx Γ) ->
    All2_local_env
      (on_decl
         (on_decl_over
            (λ (Γ Γ' : context) (t t0 : term), pred1 Σ Γ' (rho_ctx Γ) t0 (rho (rho_ctx Γ) t)) Γ
            Γ')) (fix_context mfix0) (fix_context mfix1) ->
    All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                  (λ x : def term, (dname x, rarg x))
                  (λ (Γ Γ' : context) (x y : term), (pred1 Σ Γ Γ' x y *
                                                     pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type)
                  mfix0 mfix1 ->
    psubst Σ Γ' (rho_ctx Γ) (cofix_subst mfix1) (map (rho (rho_ctx Γ)) (cofix_subst mfix0))
           (fix_context mfix1) (rho_ctx_over (rho_ctx Γ) (fix_context mfix0)).
  Proof.
    intros Hlen Hred Hctxs a0. pose proof Hctxs as Hctxs'.
    pose proof a0 as a0'. apply All2_rev in a0'.
    revert Hctxs.
    unfold cofix_subst, fix_context. simpl.
    revert a0'. rewrite -Hlen -(@List.rev_length _ mfix0).
    rewrite !rev_mapi. unfold mapi.
    assert (#|mfix0| >= #|List.rev mfix0|) by (rewrite List.rev_length; lia).
    assert (#|mfix1| >= #|List.rev mfix1|) by (rewrite List.rev_length; lia).
    assert (He :0 = #|mfix0| - #|List.rev mfix0|) by (rewrite List.rev_length; auto with arith).
    assert (He' :0 = #|mfix1| - #|List.rev mfix1|) by (rewrite List.rev_length; auto with arith).
    rewrite {2 6}He {3 6}He'. clear He He'. revert H H0.
    assert (#|List.rev mfix0| = #|List.rev mfix1|) by (rewrite !List.rev_length; lia).
    revert H.
    generalize (List.rev mfix0) (List.rev mfix1).
    intros l l' Heqlen Hlen' Hlen'' H. induction H. 1: constructor.
    simpl.
    simpl in *.
    replace (S (#|mfix0| - S #|l|)) with (#|mfix0| - #|l|) by lia.
    replace (S (#|mfix1| - S #|l'|)) with (#|mfix1| - #|l'|) by lia.
    rewrite -Hlen.
    assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l|)) = #|l|) by lia.
    assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l'|)) = #|l'|) by lia.
    rewrite H0 H1.
    intros. depelim Hctxs.
    - red in o.
      simpl in H2. noconf H2.
      simpl in H3. noconf H3.
      constructor.
      + unfold mapi in IHAll2.
        forward IHAll2 by lia.
        forward IHAll2 by lia.
        forward IHAll2 by lia. rewrite -Hlen in IHAll2.
        apply IHAll2; clear IHAll2. apply Hctxs; clear Hctxs.
      + clear IHAll2 Hctxs. destruct r.
        destruct o0. destruct p. destruct p. red in o.
        simpl in *. noconf Heqlen. simpl in H.
        rewrite H in o |- *.
        rewrite rho_ctx_app in o. apply o.
      + simp rho lhs_viewc; simpl; simp rho.
        econstructor.
        * eauto.
        * clear Hctxs o IHAll2.
          rewrite -fold_fix_context_rho_ctx.
          eapply All2_local_env_pred_fix_ctx. eapply Hctxs'.
        * eapply All2_mix.
          -- rewrite -fold_fix_context_rho_ctx.
             clear IHAll2 Hctxs H o r.
             eapply All2_mix_inv in a0. destruct a0.
             eapply All2_sym. unfold on_Trel.
             eapply All2_mix_inv in a. destruct a.
             eapply All2_map_left. simpl. auto.
          -- clear IHAll2 Hctxs H o r.
             eapply All2_mix_inv in a0. destruct a0.
             eapply All2_sym. unfold on_Trel.
             eapply All2_mix_inv in a0. destruct a0.
             eapply All2_mix_inv in a0. destruct a0.
             eapply All2_mix.
             ++ rewrite -fold_fix_context_rho_ctx.
                rewrite fix_context_map_fix. simpl.
                rewrite rho_ctx_app in a2. unfold on_Trel.
                eapply All2_map_left. simpl. eapply a2.
             ++ eapply All2_map_left. simpl. solve_all.
    - hnf in H2. noconf H2.
  Qed.

  Definition pred1_subst Γ Δ Δ' σ τ :=
  forall x, pred1 Σ Δ Δ' (σ x) (τ x) *
            match option_map decl_body (nth_error Γ x) return Type with
            | Some (Some b) => σ x = τ x
            | _ => True
            end.

  Lemma pred_subst_rho_cofix (Γ Γ' : context) (mfix0 mfix1 : mfixpoint term) :
    pred1_ctx Σ Γ Γ' → pred1_ctx Σ Γ' (rho_ctx Γ)
    → All2_local_env
        (on_decl
           (on_decl_over
              (λ (Γ0 Γ'0 : context) (t t0 : term),
               pred1 Σ Γ'0 (rho_ctx Γ0) t0
                     (rho (rho_ctx Γ0) t)) Γ Γ'))
        (fix_context mfix0) (fix_context mfix1)
    → All2 (on_Trel eq (λ x : def term, (dname x, rarg x)))
           mfix0 mfix1
    → All2
        (on_Trel
           (λ x y : term, pred1 Σ Γ Γ' x y
                                × pred1 Σ Γ'
                                (rho_ctx Γ) y
                                (rho (rho_ctx Γ) x)) dtype)
        mfix0 mfix1
    → All2
        (on_Trel
           (λ x y : term, pred1 Σ
                                (Γ ,,, fix_context mfix0)
                                (Γ' ,,, fix_context mfix1) x
                                y
                                × pred1 Σ
                                (Γ' ,,, fix_context mfix1)
                                (rho_ctx
                                   (Γ ,,, fix_context mfix0)) y
                                (rho
                                   (rho_ctx
                                      (Γ ,,, fix_context mfix0)) x))
           dbody) mfix0 mfix1
    → pred1_subst  (Γ' ,,, fix_context mfix1) Γ'
                  (rho_ctx Γ) (cofix_subst mfix1 ⋅n ids)
                  (cofix_subst
                     (map_fix rho (rho_ctx Γ)
                              (rho_ctx_over
                                 (rho_ctx Γ)
                                 (fix_context mfix0)) mfix0) ⋅n ids).
  Proof.
    intros predΓ predΓ' fctx eqf redr redl.
    intros x.
    destruct (leb_spec_Set (S x) #|cofix_subst mfix1|).
    - destruct (subst_consn_lt l) as [? [Hb Hb']].
      rewrite Hb'.
      eapply nth_error_cofix_subst in Hb. subst.
      rewrite cofix_subst_length in l.
      rewrite -(All2_length _ _ eqf) in l.
      rewrite -(cofix_subst_length mfix0) in l.
      destruct (subst_consn_lt l) as [b' [Hb0 Hb0']].
      rewrite rho_cofix_subst.
      pose proof (nth_error_map (rho (rho_ctx Γ)) x (cofix_subst mfix0)).
      rewrite Hb0 in H. simpl in H.
      rewrite /subst_consn H.
      eapply nth_error_cofix_subst in Hb0. subst b'.
      cbn. rewrite (All2_length _ _ eqf). constructor; auto.
      + simp rho lhs_viewc; simpl; simp  rho.
        rewrite -fold_fix_context_rho_ctx. constructor; auto.
        * eapply All2_local_env_pred_fix_ctx. apply fctx.
        * red. clear - wfΣ on_extra eqf redr redl.
          eapply All2_sym. apply All2_map_left.
          pose proof (All2_mix eqf (All2_mix redr redl)) as X; clear eqf redr redl.
          eapply All2_impl; eauto. clear X.
          unfold on_Trel in *. simpl. intros x y.
          rewrite fix_context_map_fix rho_ctx_app. intuition auto.
      + pose proof (fix_context_assumption_context mfix1).
        rewrite cofix_subst_length (All2_length _ _ eqf) -(fix_context_length mfix1) in l.
        rewrite nth_error_app_lt //.
        destruct (nth_error (fix_context mfix1) x) eqn:Heq => // /=; auto.
        destruct c as [na [?|] ty] => //.
        move: (nth_error_assumption_context _ _ _ H0 Heq) => //.
    - rewrite cofix_subst_length in l.
      rewrite !subst_consn_ge; try rewrite ?cofix_subst_length ?map_length; try lia.
      + now rewrite (All2_length _ _ eqf).
      + split.
        * rewrite (All2_length _ _ eqf); pcuic.
        * rewrite nth_error_app_ge ?fix_context_length //; try lia.
          destruct option_map as [[o|]|]; auto.
          now rewrite (All2_length _ _ eqf).
  Qed.

  Lemma pred_subst_rho_fix (Γ Γ' : context) (mfix0 mfix1 : mfixpoint term) :
    pred1_ctx Σ Γ Γ' → pred1_ctx Σ Γ' (rho_ctx Γ)
    → All2_local_env
        (on_decl
           (on_decl_over
              (λ (Γ0 Γ'0 : context) (t t0 : term),
               pred1 Σ Γ'0 (rho_ctx Γ0) t0
                     (rho (rho_ctx Γ0) t)) Γ Γ'))
        (fix_context mfix0) (fix_context mfix1)
    → All2 (on_Trel eq (λ x : def term, (dname x, rarg x)))
           mfix0 mfix1
    → All2
        (on_Trel
           (λ x y : term, pred1 Σ Γ Γ' x y
                                × pred1 Σ Γ'
                                (rho_ctx Γ) y
                                (rho (rho_ctx Γ) x)) dtype)
        mfix0 mfix1
    → All2
        (on_Trel
           (λ x y : term, pred1 Σ
                                (Γ ,,, fix_context mfix0)
                                (Γ' ,,, fix_context mfix1) x
                                y
                                × pred1 Σ
                                (Γ' ,,, fix_context mfix1)
                                (rho_ctx
                                   (Γ ,,, fix_context mfix0)) y
                                (rho
                                   (rho_ctx
                                      (Γ ,,, fix_context mfix0)) x))
           dbody) mfix0 mfix1
    → pred1_subst (Γ' ,,, fix_context mfix1) Γ'
                  (rho_ctx Γ) (fix_subst mfix1 ⋅n ids)
                  (fix_subst
                     (map_fix rho (rho_ctx Γ)
                              (rho_ctx_over
                                 (rho_ctx Γ)
                                 (fix_context mfix0)) mfix0) ⋅n ids).
  Proof.
    intros predΓ predΓ' fctx eqf redr redl.
    intros x.
    destruct (leb_spec_Set (S x) #|fix_subst mfix1|).
    - destruct (subst_consn_lt l) as [? [Hb Hb']].
      rewrite Hb'.
      eapply nth_error_fix_subst in Hb. subst.
      rewrite fix_subst_length in l.
      rewrite -(All2_length _ _ eqf) in l.
      rewrite -(fix_subst_length mfix0) in l.
      destruct (subst_consn_lt l) as [b' [Hb0 Hb0']].
      rewrite rho_fix_subst.
      pose proof (nth_error_map (rho (rho_ctx Γ)) x (fix_subst mfix0)).
      rewrite Hb0 in H. simpl in H.
      rewrite /subst_consn H.
      eapply nth_error_fix_subst in Hb0. subst b'.
      cbn. rewrite (All2_length _ _ eqf). constructor; auto.
      + simp rho lhs_viewc; simpl; simp rho.
        rewrite -fold_fix_context_rho_ctx. constructor; auto.
        * eapply All2_local_env_pred_fix_ctx. apply fctx.
        * red. clear - wfΣ on_extra eqf redr redl.
          eapply All2_sym. apply All2_map_left.
          pose proof (All2_mix eqf (All2_mix redr redl)) as X; clear eqf redr redl.
          eapply All2_impl; eauto. clear X.
          unfold on_Trel in *. simpl. intros x y.
          rewrite fix_context_map_fix rho_ctx_app. intuition auto.
      + pose proof (fix_context_assumption_context mfix1).
        rewrite fix_subst_length (All2_length _ _ eqf) -(fix_context_length mfix1) in l.
        rewrite nth_error_app_lt //.
        destruct (nth_error (fix_context mfix1) x) eqn:Heq => // /=; auto.
        destruct c as [na [?|] ty] => //.
        move: (nth_error_assumption_context _ _ _ H0 Heq) => //.
    - rewrite fix_subst_length in l.
      rewrite !subst_consn_ge; try rewrite ?fix_subst_length ?map_length; try lia.
      + now rewrite (All2_length _ _ eqf).
      + split.
        * rewrite (All2_length _ _ eqf); pcuic.
        * rewrite nth_error_app_ge ?fix_context_length //; try lia.
          destruct option_map as [[o|]|]; auto.
          now rewrite (All2_length _ _ eqf).
  Qed.

  Section All2_telescope.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).

    Definition telescope := context.

    Inductive All2_telescope (Γ Γ' : context) : telescope -> telescope -> Type :=
    | telescope2_nil : All2_telescope Γ Γ' [] []
    | telescope2_cons_abs na t t' Δ Δ' :
        P Γ Γ' None t t' ->
        All2_telescope (Γ ,, vass na t) (Γ' ,, vass na t') Δ Δ' ->
        All2_telescope Γ Γ' (vass na t :: Δ) (vass na t' :: Δ')
    | telescope2_cons_def na b b' t t' Δ Δ' :
        P Γ Γ' (Some (b, b')) t t' ->
        All2_telescope (Γ ,, vdef na b t) (Γ' ,, vdef na b' t') Δ Δ' ->
        All2_telescope Γ Γ' (vdef na b t :: Δ) (vdef na b' t' :: Δ').
  End All2_telescope.

  Section All2_telescope_n.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).
    Context (f : nat -> term -> term).

    Inductive All2_telescope_n (Γ Γ' : context) (n : nat) : telescope -> telescope -> Type :=
    | telescope_n_nil : All2_telescope_n Γ Γ' n [] []
    | telescope_n_cons_abs na t t' Δ Δ' :
        P Γ Γ' None (f n t) (f n t') ->
        All2_telescope_n (Γ ,, vass na (f n t)) (Γ' ,, vass na (f n t')) (S n) Δ Δ' ->
        All2_telescope_n Γ Γ' n (vass na t :: Δ) (vass na t' :: Δ')
    | telescope_n_cons_def na b b' t t' Δ Δ' :
        P Γ Γ' (Some (f n b, f n b')) (f n t) (f n t') ->
        All2_telescope_n (Γ ,, vdef na (f n b) (f n t)) (Γ' ,, vdef na (f n b') (f n t'))
                         (S n) Δ Δ' ->
        All2_telescope_n Γ Γ' n (vdef na b t :: Δ) (vdef na b' t' :: Δ').

  End All2_telescope_n.

  Lemma All2_telescope_mapi {P} Γ Γ' Δ Δ' (f : nat -> term -> term) k :
    All2_telescope_n (on_decl P) f Γ Γ' k Δ Δ' ->
    All2_telescope (on_decl P) Γ Γ' (mapi_rec (fun n => map_decl (f n)) Δ k)
                   (mapi_rec (fun n => map_decl (f n)) Δ' k).
  Proof.
    induction 1; simpl; constructor; auto.
  Qed.

  Lemma local_env_telescope P Γ Γ' Δ Δ' :
    All2_telescope (on_decl P) Γ Γ' Δ Δ' ->
    All2_local_env_over P Γ Γ' (List.rev Δ) (List.rev Δ').
  Proof.
    induction 1.
    - simpl. constructor.
    - simpl. eapply All2_local_env_over_app.
      + constructor. 1: constructor.
        simpl. apply p.
      + revert IHX.
        generalize (List.rev Δ) (List.rev Δ'). induction 1.
        * constructor.
        * constructor. 1: auto.
          red in p0. red. red. red. red in p0.
          rewrite !app_context_assoc. cbn. apply p0.
        * constructor. 1: auto.
          destruct p0. unfold on_decl_over in *. simpl.
          rewrite !app_context_assoc. cbn. intuition.
    - simpl. eapply All2_local_env_over_app.
      + constructor. 1: constructor.
        simpl. unfold on_decl_over, on_decl in *.
        destruct p. split; intuition auto.
      + revert IHX.
        generalize (List.rev Δ) (List.rev Δ'). induction 1.
        * constructor.
        * constructor. 1: auto.
          red in p0. red. red. red. red in p0.
          rewrite !app_context_assoc. cbn. apply p0.
        * constructor. 1: auto.
          destruct p0. unfold on_decl_over in *. simpl.
          rewrite !app_context_assoc. cbn. intuition.
  Qed.


  Lemma All_All2_telescopei_gen (Γ Γ' Δ Δ' : context) (m m' : mfixpoint term) :
    #|Δ| = #|Δ'| ->
                 All2
                   (λ (x y : def term), (pred1 Σ Γ'
                                               (rho_ctx Γ)
                                               (dtype x)
                                               (rho (rho_ctx Γ) (dtype y))) * (dname x = dname y))%type m m' ->
                 All2_local_env_over (pred1 Σ) Γ' (rho_ctx Γ) Δ (rho_ctx_over (rho_ctx Γ) Δ') ->
                 All2_telescope_n (on_decl (pred1 Σ)) (λ n : nat, lift0 n)
                                  (Γ' ,,, Δ) (rho_ctx (Γ ,,, Δ'))
                                  #|Δ|
  (map (λ def : def term, vass (dname def) (dtype def)) m)
    (map (λ def : def term, vass (dname def) (rho (rho_ctx Γ) (dtype def))) m').
  Proof.
    intros Δlen.
    induction 1 in Δ, Δ', Δlen |- *; cbn. 1: constructor.
    intros. destruct r. rewrite e. constructor.
    - red. rewrite rho_ctx_app.
      assert (#|Δ| = #|rho_ctx_over (rho_ctx Γ) Δ'|) by now rewrite rho_ctx_over_length.
      rewrite {2}H. eapply weakening_pred1_pred1; eauto.
    - specialize (IHX (vass (dname y) (lift0 #|Δ| (dtype x)) :: Δ)
                    (vass (dname y) (lift0 #|Δ'| (dtype y)) :: Δ')%list).
      assert (#|Δ| = #|rho_ctx_over (rho_ctx Γ) Δ'|) by now rewrite rho_ctx_over_length.
      rewrite {2}H.
      rewrite rho_lift0.
      unfold snoc. forward IHX.
      { simpl. lia. }
      forward IHX.
      { cbn. constructor.
        - apply X0.
        - red. red.
        assert (#|Δ'| = #|rho_ctx_over (rho_ctx Γ) Δ'|) by now rewrite rho_ctx_over_length.
        rewrite H0.
        rewrite - (rho_lift0 (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) Δ')). simpl.
        eapply weakening_pred1_pred1; eauto.
      }
      rewrite rho_ctx_app in IHX.
      simpl in IHX. rewrite -H. rewrite {2}Δlen.
      rewrite rho_ctx_app. apply IHX.
  Qed.

  Lemma All_All2_telescopei (Γ Γ' : context) (m m' : mfixpoint term) :
    All2 (λ (x y : def term), (pred1 Σ Γ' (rho_ctx Γ) (dtype x) (rho (rho_ctx Γ) (dtype y))) *
                              (dname x = dname y))%type m m' ->
    All2_telescope_n (on_decl (pred1 Σ)) (λ n : nat, lift0 n)
                     Γ' (rho_ctx Γ)
                     0
                     (map (λ def : def term, vass (dname def) (dtype def)) m)
                     (map (λ def : def term, vass (dname def) (rho (rho_ctx Γ) (dtype def))) m').
  Proof.
    specialize (All_All2_telescopei_gen Γ Γ' [] [] m m'). simpl.
    intros. specialize (X eq_refl X0). forward X. 1: constructor.
    apply X.
  Qed.


  Lemma rho_All_All2_local_env_inv :
  ∀ Γ Γ' : context, pred1_ctx Σ Γ' (rho_ctx Γ) → ∀ Δ Δ' : context,
      All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ' (rho_ctx Γ))) Δ
                     (rho_ctx_over (rho_ctx Γ) Δ') ->
      All2_local_env
        (on_decl
           (λ (Δ Δ' : context) (t t' : term), pred1 Σ (Γ' ,,, Δ)
                                                    (rho_ctx (Γ ,,, Δ')) t
                                                    (rho (rho_ctx (Γ ,,, Δ')) t'))) Δ Δ'.

  Proof.
    intros. induction Δ in Δ', X0 |- *.
    - depelim X0. destruct Δ'; noconf H. 1: constructor.
      cbn in H. destruct c as [? [?|] ?]; noconf H.
    - depelim X0.
      + destruct Δ'. 1: noconf H.
        destruct c as [? [?|] ?]; noconf H.
        1:{ simpl in H. noconf H. }
        simpl in H. noconf H.
        constructor.
        * eapply IHΔ. auto.
        * red. red in o. intros.
          red in o. rewrite !rho_ctx_app. eapply o.
      + destruct Δ'. 1: noconf H.
        destruct c as [? [?|] ?]; noconf H.
        2:{ simpl in H. noconf H. }
        simpl in H. noconf H. red in o. destruct o.
        constructor.
        * eapply IHΔ. auto.
        * red. red in o, o0. intros.
          rewrite !rho_ctx_app. split; eauto.
  Qed.

  Lemma pred1_rho_fix_context_2 (Γ Γ' : context) (m m' : mfixpoint term) :
    pred1_ctx Σ Γ' (rho_ctx Γ) ->
    All2 (on_Trel_eq (pred1 Σ Γ' (rho_ctx Γ)) dtype dname) m
         (map_fix rho (rho_ctx Γ)
                  (fold_fix_context rho (rho_ctx Γ) [] m') m') ->
    All2_local_env
      (on_decl (on_decl_over (pred1 Σ) Γ' (rho_ctx Γ)))
      (fix_context m)
      (fix_context (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] m') m')).
  Proof.
    intros HΓ a.
    rewrite - fold_fix_context_rho_ctx in a.
    unfold map_fix in a.
    eapply All2_map_right' in a.
    rewrite - fold_fix_context_rho_ctx.
    unfold fix_context. unfold map_fix.
    eapply local_env_telescope.
    cbn.
    rewrite - (mapi_mapi
                 (fun n def => vass (dname def) (dtype def))
                 (fun n decl => lift_decl n 0 decl)).
    rewrite mapi_map. simpl.
    rewrite - (mapi_mapi
                 (fun n def => vass (dname def) (rho (rho_ctx Γ) (dtype def)))
                 (fun n decl => lift_decl n 0 decl)).
    eapply All2_telescope_mapi.
    rewrite !mapi_cst_map.
    eapply All_All2_telescopei; eauto.
  Qed.

  Lemma isConstruct_app_pred1 {Γ Δ a b} : pred1 Σ Γ Δ a b -> isConstruct_app a -> isConstruct_app b.
  Proof.
    move=> pr; rewrite /isConstruct_app.
    move e: (decompose_app a) => [hd args].
    apply decompose_app_inv in e. subst a. simpl.
    case: hd pr => // ind n ui.
    intros h _.
    apply pred1_mkApps_tConstruct in h as [args' [-> Hargs']]. 2: auto.
    rewrite decompose_app_mkApps //.
  Qed.

  Lemma is_constructor_pred1 Γ Γ' n l l' :
    All2 (pred1 Σ Γ Γ') l l' ->
    is_constructor n l -> is_constructor n l'.
  Proof.
    induction 1 in n |- *.
    - now rewrite /is_constructor nth_error_nil.
    - destruct n; rewrite /is_constructor /=.
      + now eapply isConstruct_app_pred1.
      + eapply IHX.
  Qed.

  Lemma pred1_subst_pred1_ctx {Γ Δ Δ' σ τ} :
    pred1_subst Γ Δ Δ' σ τ ->
    pred1_ctx Σ Δ Δ'.
  Proof. intros Hrel. destruct (Hrel 0). pcuic. Qed.

  Hint Extern 4 (pred1_ctx ?Σ ?Δ ?Δ') =>
  match goal with
    H : pred1_subst _ Δ Δ' _ _ |- _ =>
    apply (pred1_subst_pred1_ctx H)
  end : pcuic.

  Lemma pred1_subst_Up:
    ∀ (Γ : context) (na : name) (t0 t1 : term) (Δ Δ' : context) (σ τ : nat → term),
      pred1 Σ Δ Δ' t0.[σ] t1.[τ] →
      pred1_subst Γ Δ Δ' σ τ →
      pred1_subst (Γ,, vass na t0) (Δ,, vass na t0.[σ]) (Δ',, vass na t1.[τ]) (⇑ σ) (⇑ τ).
  Proof.
    intros Γ na t0 t1 Δ Δ' σ τ X2 Hrel.
    intros x. destruct x; simpl.
    - split; auto.
      eapply pred1_refl_gen. constructor; eauto with pcuic.
    - unfold subst_compose. rewrite - !(lift0_inst 1).
      split.
      + eapply (weakening_pred1_pred1 Σ _ _ [_] [_]); auto.
        * constructor. 1: constructor.
          red. red. eapply X2.
        * eapply Hrel.
      + destruct (Hrel x).
        destruct option_map as [[o|]|]; now rewrite ?y.
  Qed.

  Lemma pred1_subst_vdef_Up:
    ∀ (Γ : context) (na : name) (b0 b1 t0 t1 : term) (Δ Δ' : context) (σ τ : nat → term),
      pred1 Σ Δ Δ' t0.[σ] t1.[τ] →
      pred1 Σ Δ Δ' b0.[σ] b1.[τ] →
      pred1_subst Γ Δ Δ' σ τ →
      pred1_subst (Γ,, vdef na b0 t0) (Δ,, vdef na b0.[σ] t0.[σ]) (Δ',, vdef na b1.[τ] t1.[τ]) (⇑ σ) (⇑ τ).
  Proof.
    intros Γ na b0 b1 t0 t1 Δ Δ' σ τ Xt Xb Hrel.
    intros x. destruct x; simpl.
    - split; auto.
      eapply pred1_refl_gen.
      constructor; eauto with pcuic.
    - unfold subst_compose. rewrite - !(lift0_inst 1).
      split.
      + eapply (weakening_pred1_pred1 Σ _ _ [_] [_]); auto.
        * constructor. 1: constructor.
          red. split; red.
          -- eapply Xb.
          -- apply Xt.
        * eapply Hrel.
      + destruct (Hrel x). destruct option_map as [[o|]|]; now rewrite ?y.
  Qed.

  Lemma pred1_subst_Upn:
    ∀ (Γ : context) (Δ Δ' : context) (σ τ : nat → term) (Γ' Δ0 Δ1 : context) n,
      #|Γ'| = #|Δ0| -> #|Δ0| = #|Δ1| -> n = #|Δ0| ->
                                                  pred1_subst Γ Δ Δ' σ τ →
                                                  All2_local_env_over (pred1 Σ) Δ Δ' Δ0 Δ1 ->
                                                  pred1_subst (Γ ,,, Γ') (Δ ,,, Δ0) (Δ' ,,, Δ1) (⇑^n σ) (⇑^n τ).
  Proof.
    intros * len0 len1 -> Hrel.
    red. intros H x.
    destruct (leb_spec_Set (S x) #|idsn #|Δ0| |).
    - unfold Upn.
      specialize (subst_consn_lt l).
      intros [tx [Hdecl Heq]].
      rewrite !Heq. split.
      + eapply pred1_refl_gen. auto.
        eapply All2_local_env_over_app; auto. destruct (Hrel 0). pcuic.
      + destruct option_map as [[o|]|]; auto.
    - unfold Upn.
      rewrite !subst_consn_ge. 1-2: lia.
      rewrite idsn_length. specialize (Hrel (x - #|Δ0|)).
      destruct Hrel.
      split.
      + unfold subst_compose. rewrite - !(lift0_inst _).
        rewrite {3}len1.
        eapply weakening_pred1_pred1; auto.
      + rewrite nth_error_app_ge.
        * rewrite idsn_length in l. lia.
        * rewrite len0.
          destruct option_map as [[o|]|]; auto.
        unfold subst_compose. simpl. rewrite y. reflexivity.
  Qed.

  Lemma substitution_pred1 Γ Δ Γ' Δ' s s' N N' :
    psubst Σ Γ Γ' s s' Δ Δ' ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') N N' ->
    pred1 Σ Γ Γ' (subst s 0 N) (subst s' 0 N').
  Proof.
    intros redM redN.
    pose proof (substitution_let_pred1 Σ Γ Δ [] Γ' Δ' [] s s' N N' wfΣ) as H.
    assert (#|Γ| = #|Γ'|).
    { eapply psubst_length in redM. intuition auto.
      apply pred1_pred1_ctx in redN. eapply All2_local_env_length in redN.
      rewrite !app_context_length in redN. lia. }
    forward H by auto.
    forward H by pcuic.
    specialize (H eq_refl). forward H.
    - apply pred1_pred1_ctx in redN; pcuic.
      eapply All2_local_env_app in redN; auto.
      destruct redN. apply a0.
    - simpl in H. now apply H.
  Qed.

  Lemma inst_iota_red s pars c args brs :
    inst s (iota_red pars c args brs) =
    iota_red pars c (List.map (inst s) args) (List.map (on_snd (inst s)) brs).
  Proof.
    unfold iota_red. rewrite !inst_mkApps. f_equal; auto using map_skipn.
    rewrite nth_map; simpl; auto.
  Qed.

  Lemma All2_local_env_fold_context P f g Γ Δ :
    All2_local_env (fun Γ Δ p T U => P (fold_context f Γ) (fold_context g Δ)
                                        (option_map (fun '(b, b') => (f #|Γ| b, g #|Δ| b')) p)
                                        (f #|Γ| T) (g #|Δ| U)) Γ Δ ->
    All2_local_env P (fold_context f Γ) (fold_context g Δ).
  Proof.
    induction 1; rewrite ?fold_context_snoc0; constructor; auto.
  Qed.

  Lemma All2_local_env_fix_context P σ τ Γ Δ :
    All2_local_env (fun Γ Δ p T U => P (inst_context σ Γ) (inst_context τ Δ)
                                        (option_map (fun '(b, b') => (b.[⇑^#|Γ| σ], b'.[⇑^#|Δ| τ])) p)
                                        (T.[⇑^#|Γ| σ]) (U.[⇑^#|Δ| τ])) Γ Δ ->
    All2_local_env P (inst_context σ Γ) (inst_context τ Δ).
  Proof.
    eapply All2_local_env_fold_context.
  Qed.

  Lemma All2_local_env_impl P Q Γ Δ :
    All2_local_env P Γ Δ ->
    (forall Γ Δ t T U, #|Γ| = #|Δ| -> P Γ Δ t T U -> Q Γ Δ t T U) ->
    All2_local_env Q Γ Δ.
  Proof.
    intros H HP. pose proof (All2_local_env_length H).
    induction H; constructor; simpl; eauto.
  Qed.

  Lemma decompose_app_rec_inst s t l :
    let (f, a) := decompose_app_rec t l in
    inst s f = f ->
    decompose_app_rec (inst s t) (map (inst s) l)  = (f, map (inst s) a).
  Proof.
    induction t in s, l |- *; simpl; auto; try congruence.
    - intros ->. simpl. reflexivity.
    - specialize (IHt1 s (t2 :: l)).
      destruct decompose_app_rec. intros H. rewrite IHt1; auto.
  Qed.

  Lemma decompose_app_inst s t f a :
    decompose_app t = (f, a) -> inst s f = f ->
    decompose_app (inst s t) = (inst s f, map (inst s) a).
  Proof.
    generalize (decompose_app_rec_inst s t []).
    unfold decompose_app. destruct decompose_app_rec.
    move=> Heq [= <- <-] Heq'. now rewrite Heq' (Heq Heq').
  Qed.
  Hint Rewrite decompose_app_inst using auto : lift.

  Lemma inst_is_constructor:
    forall (args : list term) (narg : nat) s,
      is_constructor narg args = true -> is_constructor narg (map (inst s) args) = true.
  Proof.
    intros args narg.
    unfold is_constructor; intros.
    rewrite nth_error_map. destruct nth_error; try discriminate. simpl. intros.
    unfold isConstruct_app in *.
    destruct (decompose_app t) eqn:Heq. eapply decompose_app_inst in Heq as ->.
    - destruct t0; try discriminate || reflexivity.
    - destruct t0; try discriminate || reflexivity.
  Qed.
  Hint Resolve inst_is_constructor : core.

  Lemma closed_ctx_inst :
    forall σ Γ,
      closed_ctx Γ ->
      inst_context σ Γ = Γ.
  Proof.
    intros σ Γ h.
    induction Γ as [| [na [b|] A] Γ ih ] in σ, h |- *.
    - reflexivity.
    - rewrite inst_context_snoc. unfold map_decl. cbn.
      rewrite closedn_ctx_cons in h. apply MCProd.andP in h as [h1 h2].
      unfold closed_decl in h2. cbn in h2.
      apply MCProd.andP in h2 as [h2 h3].
      rewrite -> ih by assumption.
      rewrite -> inst_closed by assumption.
      rewrite -> inst_closed by assumption.
      reflexivity.
    - rewrite inst_context_snoc. unfold map_decl. cbn.
      rewrite closedn_ctx_cons in h. apply MCProd.andP in h as [h1 h2].
      unfold closed_decl in h2. cbn in h2.
      rewrite -> ih by assumption.
      rewrite -> inst_closed by assumption.
      reflexivity.
  Qed.

  Lemma strong_substitutivity Γ Γ' Δ Δ' s t σ τ :
    pred1 Σ Γ Γ' s t ->
    ctxmap Γ Δ σ ->
    ctxmap Γ' Δ' τ ->
    pred1_subst Γ Δ Δ' σ τ ->
    pred1 Σ Δ Δ' s.[σ] t.[τ].
  Proof using cf Σ wfΣ.
    intros redst.
    revert Δ Δ' σ τ.
    revert Γ Γ' s t redst.
    set (P' := fun Γ Γ' => pred1_ctx Σ Γ Γ').
    refine (pred1_ind_all_ctx Σ _ P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); subst P';
      try (intros until Δ; intros Δ' σ τ Hσ Hτ Hrel); trivial.

    (* induction redst using ; sigma; intros Δ Δ' σ τ Hσ Hτ Hrel. *)
    all:eauto 2 with pcuic.

    (** Beta case *)
    1:{ eapply simpl_pred; simpl; rewrite ?up_Upn; sigma; try reflexivity.
        specialize (X2 _ _ _ _ Hσ Hτ Hrel).
        specialize (X0 (Δ ,, vass na t0.[σ]) (Δ' ,, vass na t1.[τ]) (⇑ σ) (⇑ τ)).
        forward X0.
        { eapply Up_ctxmap; eauto. }
        forward X0.
        { eapply Up_ctxmap; eauto. }
        forward X0.
        { eapply pred1_subst_Up; auto. }
        specialize (X4 _ _ _ _ Hσ Hτ Hrel).
        eapply (pred_beta _ _ _ _ _ _ _ _ _ _ X2 X0 X4).
    }

    (** Let-in delta case *)
    2:{ rewrite lift_rename rename_inst.
        simpl. rewrite lift_renaming_0. clear X0.
        destruct (nth_error_pred1_ctx _ _ X H) as [bodyΓ [? ?]]; eauto.
        move e after H.
        pose proof (pred1_pred1_ctx _ (fst (Hrel i))).
        destruct (nth_error Γ' i) eqn:HΓ'i; noconf H. hnf in H.
        destruct (nth_error Γ i) eqn:HΓi; noconf e. hnf in H.
        pose proof (Hσ _ _ HΓi) as Hc. rewrite H in Hc.
        destruct Hc as [σi [b' [eqi' [Hnth Hb']]]].
        pose proof (Hτ _ _ HΓ'i) as Hc'. rewrite H0 in Hc'.
        destruct Hc' as [τi [b'' [eqi'' [Hnth' Hb'']]]].
        destruct (nth_error_pred1_ctx _ _ X0 Hnth') as [bodyΔ [? ?]].
        destruct (Hrel i) as [_ Hi]. rewrite HΓi in Hi. simpl in Hi. rewrite H in Hi.
        rewrite Hi in eqi'. rewrite eqi' in eqi''. noconf eqi''.
        simpl_pred.
        eapply refine_pred.
        - now rewrite -ren_shiftk -Hb''.
        - rewrite Hi eqi'. rewrite -lift0_inst. constructor. all: auto.
    }

    (** Let-in delta case (left) *)
    (* 2:{ rewrite lift_rename rename_inst.
        simpl. rewrite lift_renaming_0. clear X0.
        (* destruct (nth_error_pred1_ctx _ _ X H) as [bodyΓ [? ?]]; eauto.
        move e after H.
        pose proof (pred1_pred1_ctx _ (fst (Hrel i))).
        destruct (nth_error Γ' i) eqn:HΓ'i; noconf H. hnf in H.
        destruct (nth_error Γ i) eqn:HΓi; noconf e. hnf in H.
        pose proof (Hσ _ _ HΓi) as Hc. rewrite H in Hc.
        destruct Hc as [σi [b' [eqi' [Hnth Hb']]]].
        pose proof (Hτ _ _ HΓ'i) as Hc'. rewrite H0 in Hc'.
        destruct Hc' as [τi [b'' [eqi'' [Hnth' Hb'']]]].
        destruct (nth_error_pred1_ctx _ _ X0 Hnth') as [bodyΔ [? ?]].
        destruct (Hrel i) as [_ Hi]. rewrite HΓi in Hi. simpl in Hi. rewrite H in Hi.
        rewrite Hi in eqi'. rewrite eqi' in eqi''. noconf eqi''.
        simpl_pred.
        eapply refine_pred.
        - now rewrite -ren_shiftk -Hb''.
        - rewrite Hi eqi'. rewrite -lift0_inst. constructor. all: auto. *)
      admit.
    } *)

    (** Zeta *)
    1:{ sigma.
        econstructor; eauto.
        eapply X4; try apply Up_ctxmap; auto.
        apply pred1_subst_vdef_Up; auto. }

    - simpl. eapply Hrel.

    - simpl. rewrite inst_iota_red.
      sigma. econstructor.
      + now eapply pred1_subst_pred1_ctx.
      + solve_all.
      + solve_all. red in X2. solve_all.

    - sigma.
      unfold unfold_fix in *.
      destruct nth_error eqn:Heq; noconf H.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { clear -wfΣ Hσ Hτ Hrel X2.
        induction X2.
        + constructor.
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
          apply (All2_local_env_length X2).
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. split; eapply p; auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic.
      }
      econstructor; eauto with pcuic.
      + instantiate (1 := (map (map_def (inst τ) (inst (⇑^#|mfix1| τ))) mfix1)).
        rewrite !inst_fix_context; auto.
      + rewrite !inst_fix_context; auto.
        clear -X5 wfΣ X3 Hσ Hτ Hrel. red. eapply All2_map.
        red in X3. pose proof (All2_length _ _ X3).
        solve_all; unfold on_Trel in *; simpl in *;
        intuition eauto.
        eapply b.
        * rewrite -(fix_context_length mfix0); auto with pcuic.
        * rewrite -(fix_context_length mfix1); auto with pcuic.
        * rewrite -H; eapply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length;
          auto with pcuic.
      + unfold unfold_fix. rewrite nth_error_map Heq. simpl.
        rewrite !subst_inst. do 2 apply f_equal. sigma. apply inst_ext.
        rewrite map_fix_subst.
        * simpl. intros. f_equal. apply map_ext. intros.
          apply map_def_eq_spec; auto. now sigma.
        * rewrite Upn_comp ?map_length ?fix_subst_length //.
          rewrite subst_consn_compose. now sigma.
      + solve_all.

    - (* CoFix Case *)
      simpl. sigma.
      unfold unfold_cofix in H |- *. destruct nth_error eqn:Heq; noconf H.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { clear -wfΣ Hσ Hτ Hrel X2.
        induction X2.
        + constructor.
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
          apply (All2_local_env_length X2).
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. split; eapply p; auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic.
      }
      econstructor.
      + eapply pred1_subst_pred1_ctx; eauto.
      + instantiate (1 := (map (map_def (inst τ) (inst (⇑^#|mfix1| τ))) mfix1)).
        rewrite !inst_fix_context; auto.
      + rewrite !inst_fix_context; auto.
        clear -X8 wfΣ X3 Hσ Hτ Hrel. red. eapply All2_map.
        red in X3. pose proof (All2_length _ _ X3).
        solve_all; unfold on_Trel in *; simpl in *;
        intuition eauto.
        eapply b.
        * rewrite -(fix_context_length mfix0); auto with pcuic.
        * rewrite -(fix_context_length mfix1); auto with pcuic.
        * rewrite -H; eapply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length;
          auto with pcuic.
      + unfold unfold_cofix. rewrite nth_error_map Heq. simpl.
        rewrite !subst_inst. do 2 apply f_equal. sigma. apply inst_ext.
        rewrite map_cofix_subst'.
        * simpl. intros. f_equal. apply map_ext. intros.
          apply map_def_eq_spec; auto. now sigma.
        * rewrite Upn_comp ?map_length ?cofix_subst_length //.
          rewrite subst_consn_compose. now sigma.
      + solve_all. (* args *)
      + eauto.
      + red in X7. solve_all.

    - (* Proj Cofix *)
      simpl. sigma.
      unfold unfold_cofix in H |- *. destruct nth_error eqn:Heq; noconf H.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { clear -wfΣ Hσ Hτ Hrel X2.
        induction X2.
        + constructor.
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
          apply (All2_local_env_length X2).
        + rewrite !inst_context_snoc. constructor; auto.
          hnf in p |- *. simpl. split; eapply p; auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto with pcuic.
      }
      econstructor.
      + eapply pred1_subst_pred1_ctx; eauto.
      + instantiate (1 := (map (map_def (inst τ) (inst (⇑^#|mfix1| τ))) mfix1)).
        rewrite !inst_fix_context; auto.
      + rewrite !inst_fix_context; auto.
        clear -X5 wfΣ X3 Hσ Hτ Hrel. red. eapply All2_map.
        red in X3. pose proof (All2_length _ _ X3).
        solve_all; unfold on_Trel in *; simpl in *;
        intuition eauto.
        eapply b.
        * rewrite -(fix_context_length mfix0); auto with pcuic.
        * rewrite -(fix_context_length mfix1); auto with pcuic.
        * rewrite -H; eapply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length;
          auto with pcuic.
      + unfold unfold_cofix. rewrite nth_error_map Heq. simpl.
        rewrite !subst_inst. do 2 apply f_equal. sigma. apply inst_ext.
        rewrite map_cofix_subst'.
        * simpl. intros. f_equal. apply map_ext. intros.
          apply map_def_eq_spec; auto. now sigma.
        * rewrite Upn_comp ?map_length ?cofix_subst_length //.
          rewrite subst_consn_compose. now sigma.
      + solve_all. (* args *)

    - (* Rewrite rules *)
      subst lhs rhs.
      rewrite 2!inst_subst0.
      rewrite inst_closed.
      1:{
        change #|s| with (0 + #|s|). eapply closedn_subst.
        - subst ss. unfold symbols_subst.
          generalize (#|symbols decl| - 0). clear.
          generalize 0 at 2.
          intros m n. induction n in m |- *. 1: reflexivity.
          cbn. rewrite IHn. reflexivity.
        - cbn. apply untyped_subslet_length in X2.
          rewrite X2. subst ss. rewrite symbols_subst_length.
          replace (#|symbols decl| - 0) with #|symbols decl| by lia.
          rewrite subst_context_length.
          eapply closed_rule_lhs. all: eauto.
      }
      rewrite inst_closed.
      1:{
        apply All2_length in X1. rewrite <- X1.
        change #|s| with (0 + #|s|). eapply closedn_subst.
        - subst ss. unfold symbols_subst.
          generalize (#|symbols decl| - 0). clear.
          generalize 0 at 2.
          intros m n. induction n in m |- *. 1: reflexivity.
          cbn. rewrite IHn. reflexivity.
        - cbn. apply untyped_subslet_length in X2.
          rewrite X2. subst ss. rewrite symbols_subst_length.
          replace (#|symbols decl| - 0) with #|symbols decl| by lia.
          rewrite subst_context_length.
          eapply closed_rule_rhs. all: eauto.
      }
      erewrite <- map_length.
      eapply pred_rewrite_rule.
      all: try eassumption.
      + auto with pcuic.
      + apply All2_map. eapply All2_impl. 1: eassumption.
        cbn. intros x y [? ih]. eapply ih. all: auto.
      + eapply untyped_subslet_inst with (σ := σ) in X2 as h. 2: eassumption.
        eapply closed_declared_symbol_pat_context in H as hcl. 2-3: eassumption.
        rewrite -> closed_ctx_inst in h.
        1: assumption.
        eapply PCUICWeakening.closedn_ctx_subst_context0.
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

    - (* Parallel rewrite rules *)
      subst lhs rhs.
      rewrite 2!inst_subst0.
      rewrite inst_closed.
      1:{
        change #|s| with (0 + #|s|). eapply closedn_subst.
        - subst ss. unfold symbols_subst.
          generalize (#|symbols decl| - 0). clear.
          generalize 0 at 2.
          intros m n. induction n in m |- *. 1: reflexivity.
          cbn. rewrite IHn. reflexivity.
        - cbn. apply untyped_subslet_length in X2. rewrite X2.
          subst ss. rewrite symbols_subst_length.
          replace (#|symbols decl| - 0) with #|symbols decl| by lia.
          rewrite subst_context_length.
          eapply closed_prule_lhs. all: eauto.
      }
      rewrite inst_closed.
      1:{
        apply All2_length in X1. rewrite <- X1.
        change #|s| with (0 + #|s|). eapply closedn_subst.
        - subst ss. unfold symbols_subst.
          generalize (#|symbols decl| - 0). clear.
          generalize 0 at 2.
          intros m n. induction n in m |- *. 1: reflexivity.
          cbn. rewrite IHn. reflexivity.
        - cbn. apply untyped_subslet_length in X2. rewrite X2.
          subst ss. rewrite symbols_subst_length.
          replace (#|symbols decl| - 0) with #|symbols decl| by lia.
          rewrite subst_context_length.
          eapply closed_prule_rhs. all: eauto.
      }
      erewrite <- map_length.
      eapply pred_par_rewrite_rule.
      all: try eassumption.
      + auto with pcuic.
      + apply All2_map. eapply All2_impl. 1: eassumption.
        cbn. intros x y [? ih]. eapply ih. all: auto.
      + eapply untyped_subslet_inst with (σ := σ) in X2 as h. 2: eassumption.
        eapply closed_declared_symbol_par_pat_context in H as hcl. 2-3: eassumption.
        rewrite -> closed_ctx_inst in h.
        1: assumption.
        eapply PCUICWeakening.closedn_ctx_subst_context0.
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

    - simpl. rewrite inst_closed0.
      + rewrite closedn_subst_instance_constr; auto.
        eapply declared_decl_closed in H; auto. hnf in H. rewrite H0 in H.
        rtoProp; auto.
      + econstructor; eauto with pcuic.

    - (* Proj-Construct *)
      simpl. sigma. econstructor.
      + pcuic.
      + eapply All2_map. solve_all.
      + rewrite nth_error_map. now rewrite H.

    - (* Lambda congruence *)
      sigma. econstructor.
      + pcuic.
      + eapply X2.
        * eapply Up_ctxmap; pcuic.
        * eapply Up_ctxmap; pcuic.
        * now eapply pred1_subst_Up.

    - (* App congruence *)
      sigma; auto with pcuic.

    - (* Let congruence *)
      sigma. econstructor; eauto. eapply X4; try apply Up_ctxmap; auto.
      eapply pred1_subst_vdef_Up; eauto.

    - (* Case congruence *)
      simpl. econstructor; eauto. red in X3. solve_all.

    - (* Proj congruence *)
      sigma; pcuic.

    - (* Fix congruence *)
      sigma.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { eapply All2_local_env_fix_context.
        pose proof (pred1_subst_pred1_ctx Hrel). apply All2_local_env_length in X4.
        clear -wfΣ X4 X2 Hσ Hτ Hrel.
        induction X2; constructor; simpl in *; auto.
        + hnf in p |- *. simpl. eapply p; auto with pcuic.
           rewrite -(All2_local_env_length X2).
           eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
           1: apply (All2_local_env_length X2).
           apply All2_local_env_app.
           * apply All2_local_env_app_inv. 1: pcuic.
             now eapply All2_local_env_fold_context.
           * destruct (Hrel 0); auto with pcuic.
        + hnf in p |- *. simpl. split; eapply p; auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
            1: apply (All2_local_env_length X2).
            apply All2_local_env_app.
            -- apply All2_local_env_app_inv. 1: pcuic.
               now eapply All2_local_env_fold_context.
            -- destruct (Hrel 0); auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
            1: auto with pcuic.
            apply All2_local_env_app.
            -- apply All2_local_env_app_inv. 1: pcuic.
               now eapply All2_local_env_fold_context.
            -- destruct (Hrel 0); auto with pcuic.
      }

      constructor; auto with pcuic.
      { now rewrite !inst_fix_context. }
      rewrite !inst_fix_context. apply All2_map. red in X3.
      pose proof (All2_length _ _ X3).
      solve_all.
      + unfold on_Trel in *. simpl. intuition auto.
      + unfold on_Trel in *. simpl. intuition auto.
        eapply b; auto with pcuic.
        * rewrite -{1}(fix_context_length mfix0). auto with pcuic.
        * rewrite -{1}(fix_context_length mfix1). auto with pcuic.
        * rewrite -H.
          apply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length //.

    - (* CoFix congruence *)
      sigma.
      assert (All2_local_env (on_decl (on_decl_over (pred1 Σ) Δ Δ')) (inst_context σ (fix_context mfix0))
                             (inst_context τ (fix_context mfix1))).
      { eapply All2_local_env_fix_context.
        pose proof (pred1_subst_pred1_ctx Hrel). apply All2_local_env_length in X4.
        clear -wfΣ X4 X2 Hσ Hτ Hrel.
        induction X2; constructor; simpl in *; auto.
        + hnf in p |- *. simpl. eapply p; auto with pcuic.
          rewrite -(All2_local_env_length X2).
          eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
          1: apply (All2_local_env_length X2).
          apply All2_local_env_app.
          * apply All2_local_env_app_inv. 1: pcuic.
            now eapply All2_local_env_fold_context.
          * destruct (Hrel 0); auto with pcuic.
        + hnf in p |- *. simpl. split; eapply p; auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
            1: apply (All2_local_env_length X2).
            apply All2_local_env_app.
            -- apply All2_local_env_app_inv. 1: pcuic.
               now eapply All2_local_env_fold_context.
            -- destruct (Hrel 0); auto with pcuic.
          * rewrite -(All2_local_env_length X2).
            eapply pred1_subst_Upn; rewrite ?inst_context_length; auto.
            1: auto with pcuic.
            apply All2_local_env_app.
            -- apply All2_local_env_app_inv. 1: pcuic.
               now eapply All2_local_env_fold_context.
            -- destruct (Hrel 0); auto with pcuic.
      }

      constructor; auto with pcuic.
      { now rewrite !inst_fix_context. }
      rewrite !inst_fix_context. apply All2_map. red in X3.
      pose proof (All2_length _ _ X3).
      solve_all.
      + unfold on_Trel in *. simpl. intuition auto.
      + unfold on_Trel in *. simpl. intuition auto.
        eapply b; auto with pcuic.
        * rewrite -{1}(fix_context_length mfix0). auto with pcuic.
        * rewrite -{1}(fix_context_length mfix1). auto with pcuic.
        * rewrite -H. apply pred1_subst_Upn; rewrite ?inst_context_length ?fix_context_length //.

    - (* Prod Congruence *)
      sigma. constructor; auto with pcuic;
      eapply X2; auto with pcuic; try eapply Up_ctxmap; auto with pcuic.
      apply pred1_subst_Up; auto.

    - sigma. simpl. constructor; auto with pcuic. solve_all.

    - rewrite !pred_atom_inst; auto. eapply pred1_refl_gen; auto with pcuic.
  Qed.

End Rho.

Section Confluenv.

  (* Constraints on the global environment that would ensure confluence. *)

  Context {cf : checker_flags}.

  Fixpoint match_prelhs_prefix npat k n l t :=
    match match_prelhs npat k n l t with
    | Some (ui, σ) => Some (ui, σ)
    | None =>
      match l with
      | [] => None
      | r :: l => match_prelhs_prefix npat k n l t
      end
    end.

  Definition match_lhs_prefix npat k n l t :=
    match_prelhs_prefix npat k n (List.rev l) t.

  Fixpoint first_match_prefix k (l : list rewrite_rule) (t : term) :=
    match l with
    | [] => None
    | r :: l =>
      match match_lhs_prefix #|r.(pat_context)| k r.(head) r.(elims) t with
      | Some (ui, σ) => Some (ui, σ, r)
      | None => first_match_prefix k l t
      end
    end.

  (* TODO Am I assuming rhs are normal? *)
  Definition triangle_rules Σ e kn nsymb l :=
    ∀ r n npat' Γ σ ui θ r',
      nth_error l n = Some r →
      All (pattern npat') σ →
      untyped_subslet Γ σ r.(pat_context) →
      let ss := symbols_subst kn 0 ui nsymb in
      let tl := subst0 σ (subst ss #|σ| (lhs r)) in
      let tr := subst0 σ (subst ss #|σ| (rhs r)) in
      let tr' := subst0 θ (subst ss #|θ| (rhs r')) in
      first_match kn l tl = Some (ui, θ, r') →
      (* Contexts should be irrelevant here because we're dealing with
        patterns that do not involve lets or any binder.
      *)
      pred1_extra Σ e Γ tr tr'.

  Definition prefix {A} (l l' : list A) :=
    ∑ l'', l' = l ++ l''.

  Definition strict_prefix {A} (l l' : list A) :=
    prefix l l' × #|l| < #|l'|.

  (* Local version of not_lhs *)
  Definition loc_not_lhs k rd t :=
    first_match k (all_rewrite_rules rd) t = None.

  Lemma loc_not_lhs_not_lhs :
    ∀ Σ extra k rd t,
      wf Σ →
      on_option (fun '(_, d) => onrd d) extra →
      lookup_rewrite_decl Σ extra k = Some rd →
      elim_kn t = Some k →
      loc_not_lhs k rd t →
      not_lhs Σ extra t.
  Proof.
    intros Σ extra k rd t hΣ hex hrd hk h.
    intros [k' [rd' [[[ui' σ'] r'] [hrd' e]]]].
    unfold loc_not_lhs in h.
    cbn in e. eapply first_match_lookup_sound in e as ?. all: eauto.
    subst.
    apply first_match_subst_length in e as σl.
    rewrite σl in hk.
    eapply first_match_rule_list in e as hr. destruct hr as [n ?].
    subst. erewrite elim_kn_lhs in hk. 2-5: eauto.
    apply some_inj in hk. subst.
    rewrite hrd' in hrd. apply some_inj in hrd. subst.
    rewrite h in e. discriminate.
  Qed.

  (* Criterion that essentially enforces rules on the same symbol
    to have the same arity.
    Prefixes of lhs are no longer lhs.
  *)
  Definition nosubmatch kn rd l :=
    ∀ n r σ el ui,
      nth_error l n = Some r →
      let ss := symbols_subst kn 0 ui #|symbols rd| in
      strict_prefix el (map (subst_elim σ 0) (map (subst_elim ss #|σ|) r.(elims))) →
      loc_not_lhs
        kn rd (mkElims (tSymb kn r.(head) ui) el).

  (* Inductive triangle_rules Σ e kn nsymb : list rewrite_rule → Type :=
  | triangle_rules_nil : triangle_rules Σ e kn nsymb []
  | triangle_rules_cons :
      ∀ r rl,
        (∀ npat' Γ σ ui θ r',
          All (pattern npat') σ →
          untyped_subslet Γ σ r.(pat_context) →
          let ss := symbols_subst kn 0 ui nsymb in
          let tl := subst0 σ (subst ss #|σ| (lhs r)) in
          let tr := subst0 σ (subst ss #|σ| (rhs r)) in
          let tr' := subst0 θ (subst ss #|θ| (rhs r')) in
          first_match kn rl tl = Some (ui, θ, r') →
          (* Contexts should be irrelevant here because we're dealing with
            patterns that do not involve lets or any binder.
          *)
          pred1_extra Σ e Γ Γ tr tr'
        ) →
        triangle_rules Σ e kn nsymb rl →
        triangle_rules Σ e kn nsymb (rl ++ [r]). *)

  Definition confl_rew_decl Σ kn d :=
    let l := d.(prules) ++ d.(rules) in
    let extra := Some (kn, d) in
    triangle_rules Σ extra kn #|d.(symbols)| l ×
    nosubmatch kn d l.

  Definition confl_decl Σ kn decl : Type :=
    match decl with
    | RewriteDecl rew => confl_rew_decl Σ kn rew
    | _ => True
    end.

  Inductive confluenv : global_env → Type :=
  | confluenv_nil : confluenv []
  | confluenv_decl Σ kn d :
      confluenv Σ →
      confl_decl Σ kn d →
      confluenv (Σ ,, (kn, d)).

  Lemma triangle_rules_weakening :
    ∀ Σ Σ' k nsymb r e,
      wf Σ' →
      PCUICWeakeningEnv.extends Σ Σ' →
      triangle_rules Σ e k nsymb r →
      triangle_rules Σ' e k nsymb r.
  Proof.
    intros Σ Σ' k nsymb r e hΣ hx hr.
    unfold triangle_rules.
    intros rr n npat' Γ σ ui θ r' hrr pσ uσ fm.
    eapply weakening_env_pred1_extra. 1,2: eauto.
    eapply hr. all: eauto.
  Qed.

  Lemma confl_decl_weakening :
    ∀ Σ Σ' k d,
      wf Σ' →
      PCUICWeakeningEnv.extends Σ Σ' →
      confl_decl Σ k d →
      confl_decl Σ' k d.
  Proof.
    intros Σ Σ' k d hΣ e hd.
    destruct d. 1,2: constructor.
    cbn in *. unfold confl_rew_decl in *.
    intuition auto.
    eapply triangle_rules_weakening. all: eauto.
  Qed.

  Lemma lookup_env_confl_decl :
    ∀ Σ k d,
      wf Σ →
      confluenv Σ →
      lookup_env Σ k = Some d →
      confl_decl Σ k d.
  Proof.
    intros Σ k d hΣ h e.
    induction h. 1: discriminate.
    cbn in e. change (eq_kername k kn) with (eqb k kn) in e.
    destruct (eqb_spec k kn).
    - apply some_inj in e. subst.
      eapply confl_decl_weakening. 1,3: eauto.
      eexists [ _ ]. reflexivity.
    - eapply confl_decl_weakening.
      + eauto.
      + eexists [ _ ]. reflexivity.
      + eapply IHh. 2: auto.
        inversion hΣ. assumption.
  Qed.

  Lemma lookup_env_confl_rew_decl :
    ∀ Σ k rd,
      wf Σ →
      confluenv Σ →
      lookup_env Σ k = Some (RewriteDecl rd) →
      confl_rew_decl Σ k rd.
  Proof.
    intros Σ k rd hΣ h e.
    eapply lookup_env_confl_decl in e. 2,3: auto.
    assumption.
  Qed.

  Definition triangle_rules' Σ kn nsymb l :=
    ∀ r n npat' Γ Γ' σ ui θ r',
      nth_error l n = Some r →
      All (pattern npat') σ →
      untyped_subslet Γ σ r.(pat_context) →
      let ss := symbols_subst kn 0 ui nsymb in
      let tl := subst0 σ (subst ss #|σ| (lhs r)) in
      let tr := subst0 σ (subst ss #|σ| (rhs r)) in
      let tr' := subst0 θ (subst ss #|θ| (rhs r')) in
      first_match kn l tl = Some (ui, θ, r') →
      pred1_ctx Σ Γ Γ' →
      pred1 Σ Γ Γ' tr tr'.

  (* Inductive triangle_rules'  Σ kn nsymb : list rewrite_rule → Type :=
  | triangle_rules_nil' : triangle_rules' Σ kn nsymb []
  | triangle_rules_cons' :
      ∀ r rl,
        (∀ npat' Γ σ ui θ r',
          All (pattern npat') σ →
          untyped_subslet Γ σ r.(pat_context) →
          let ss := symbols_subst kn 0 ui nsymb in
          let tl := subst0 σ (subst ss #|σ| (lhs r)) in
          let tr := subst0 σ (subst ss #|σ| (rhs r)) in
          let tr' := subst0 θ (subst ss #|θ| (rhs r')) in
          first_match kn rl tl = Some (ui, θ, r') →
          pred1 Σ Γ Γ tr tr'
        ) →
        triangle_rules' Σ kn nsymb rl →
        triangle_rules' Σ kn nsymb (rl ++ [r]). *)

  Definition nosubmatch' Σ kn nsymb l :=
    ∀ n r σ el ui,
      nth_error l n = Some r →
      let ss := symbols_subst kn 0 ui nsymb in
      strict_prefix el (map (subst_elim σ 0) (map (subst_elim ss #|σ|) r.(elims))) →
      not_lhs Σ None (mkElims (tSymb kn r.(head) ui) el).

  Lemma lookup_env_triangle :
    ∀ Σ k rd,
      wf Σ →
      confluenv Σ →
      lookup_env Σ k = Some (RewriteDecl rd) →
      triangle_rules' Σ k #|rd.(symbols)| (all_rewrite_rules rd).
  Proof.
    intros Σ k rd hΣ cΣ e.
    eapply lookup_env_confl_rew_decl in e as h. 2,3: auto.
    unfold confl_rew_decl in h.
    fold (all_rewrite_rules rd) in h.
    set (l := all_rewrite_rules rd) in *. clearbody l.
    intros n rr npat' Γ Γ' σ ui θ r' hrr pσ uσ ss tl tr tr' fm hctx.
    eapply pred1_extra_pred1. 1: auto. 2: eapply h ; eauto. 2: auto.
    cbn. assumption.
  Qed.

  Lemma lookup_env_nosubmatch :
    ∀ Σ k rd,
      wf Σ →
      confluenv Σ →
      lookup_env Σ k = Some (RewriteDecl rd) →
      nosubmatch' Σ k #|rd.(symbols)| (all_rewrite_rules rd).
  Proof.
    intros Σ k rd hΣ cΣ e.
    eapply lookup_env_confl_rew_decl in e as h. 2,3: auto.
    unfold confl_rew_decl in h. destruct h as [_ h].
    intros n r σ el ui hr ss hpx. eapply loc_not_lhs_not_lhs. all: eauto.
    - exact I.
    - cbn. unfold lookup_rd. rewrite e. reflexivity.
    - rewrite elim_kn_mkElims. reflexivity.
  Qed.

  Lemma first_match_app_dec :
    ∀ k l1 l2 t ui θ r,
      first_match k (l1 ++ l2) t = Some (ui, θ, r) →
      (first_match k l1 t = Some (ui, θ, r)) +
      (first_match k l2 t = Some (ui, θ, r)).
  Proof.
    intros k l1 l2 t ui θ r h.
    induction l1 in ui, θ, r, h |- *.
    - right. assumption.
    - cbn - [match_lhs] in h. destruct match_lhs as [[]|] eqn:e.
      + inversion h. subst. clear h.
        left. cbn - [match_lhs]. rewrite e. reflexivity.
      + cbn - [match_lhs]. rewrite e. eapply IHl1. assumption.
  Qed.

  (* Lemma lookup_env_triangle :
    ∀ Σ k rd,
      wf Σ →
      confluenv Σ →
      lookup_env Σ k = Some (RewriteDecl rd) →
      let nsymb := #|rd.(symbols)| in
      ∀ n r npat' Γ σ ui θ r',
        nth_error (all_rewrite_rules rd) n = Some r →
        All (pattern npat') σ →
        untyped_subslet Γ σ r.(pat_context) →
        let ss := symbols_subst k 0 ui nsymb in
        let tl := subst0 σ (subst ss #|σ| (lhs r)) in
        let tr := subst0 σ (subst ss #|σ| (rhs r)) in
        let tr' := subst0 θ (subst ss #|θ| (rhs r')) in
        first_match k (all_rewrite_rules rd) tl = Some (ui, θ, r') →
        pred1 Σ Γ Γ tr tr'.
  Proof.
    intros Σ k rd hΣ cΣ e.
    eapply lookup_env_triangle' in e as h. 2,3: auto.
    set (l := all_rewrite_rules rd) in *. clearbody l.
    induction h.
    - intros ? []. all: discriminate.
    - intros nsymb n rr npat' Γ σ ui θ r' hrr hσ uσ ss tl tr tr' fm.
      apply first_match_app_dec in fm as [fm|fm].
      + apply nth_error_app_dec in hrr as [[? hrr] | [? hrr]].
        * eapply IHh. all: eauto.
        *
        (* Perhaps just assume this directly as a criterion? *)
  Admitted. *)

End Confluenv.

Section Triangle.

  Context {cf : checker_flags}.
  Context (Σ : global_env).
  Context (wfΣ : wf Σ).

  Lemma on_extra_None :
    @on_option (kername × rewrite_decl) (fun '(k,rd) => onrd rd) None.
  Proof.
    exact I.
  Defined.

  Existing Class wf.
  Existing Instance wfΣ.

  Hint Resolve on_extra_None : rho.
  Hint Rewrite map_terms_map : rho.
  Hint Rewrite map_brs_map : rho.
  Hint Rewrite map_fix_rho_map fold_fix_context_wf_fold : rho.
  Hint Rewrite rho_app_construct : rho.
  Hint Rewrite rho_app_cofix : rho.
  Hint Constructors All2i : core pcuic.
  Hint Constructors All2i_ctx : core pcuic.
  Hint Resolve pres_bodies_inst_context : pcuic.
  Hint Resolve Upn_ctxmap : pcuic.
  Hint Extern 4 (pred1_ctx ?Σ ?Δ ?Δ') =>
    match goal with
      H : pred1_subst _ Δ Δ' _ _ |- _ =>
      apply (pred1_subst_pred1_ctx H)
    end : pcuic.
  Hint Rewrite decompose_app_inst using auto : lift.
  Hint Resolve inst_is_constructor : core.

  (* Corollay of match_lhs_complete *)
  Lemma match_lhs_rule :
    forall n r ui σ k rd,
      lookup_env Σ k = Some (RewriteDecl rd) ->
      nth_error (all_rewrite_rules rd) n = Some r ->
      #|σ| = #|r.(pat_context)| ->
      let ss := symbols_subst k 0 ui #|symbols rd| in
      match_lhs #|r.(pat_context)| k r.(head) r.(elims)
        (subst0 σ (subst ss #|σ| (lhs r)))
      = Some (ui, σ).
  Proof.
    intros n r ui σ k rd hrd hn σl ss.
    unfold lhs. rewrite mkElims_subst. cbn - [match_lhs].
    destruct (Nat.leb_spec #|σ| (#|pat_context r| + head r)). 2: lia.
    eapply lookup_on_global_env in wfΣ as h. 2: eauto.
    destruct h as [Σ' [? hd]].
    destruct hd as [? [hr [hpr ?]]].
    assert (h :
      All (on_rewrite_rule (map (vass nAnon) rd.(symbols)))
        (all_rewrite_rules rd)
    ).
    { unfold all_rewrite_rules. apply All_app_inv. all: auto. }
    eapply All_nth_error in h. 2: eauto.
    destruct h as [? ? ? hh hl pl ?].
    rewrite map_length in hh.
    destruct (nth_error ss _) eqn:e1.
    2:{
      eapply nth_error_None in e1. rewrite symbols_subst_length in e1. lia.
    }
    apply list_make_nth_error in e1. subst.
    cbn - [match_lhs].
    rewrite subst_elims_symbols_subst.
    { rewrite σl. auto. }
    replace (#|pat_context r| + head r - #|σ| + 0) with r.(head) by lia.
    eapply match_lhs_complete. all: auto.
  Qed.

  Lemma match_lhs_first_match :
    forall k l n r t x,
      nth_error l n = Some r ->
      match_lhs #|pat_context r| k (head r) (elims r) t = Some x ->
      ∑ y, first_match k l t = Some y.
  Proof.
    intros k l n r t [? ?] h e.
    induction l in n, r, h, e |- *.
    - destruct n. all: discriminate.
    - destruct n.
      + cbn in h. apply some_inj in h. subst.
        cbn - [ match_lhs ].
        rewrite e. eexists. reflexivity.
      + cbn in h. cbn - [ match_lhs ].
        destruct (match_lhs _ _ (head a) _) as [[]|] eqn:e1.
        * eexists. reflexivity.
        * eapply IHl. all: eassumption.
  Qed.

  Lemma subst_subst_compose :
    ∀ σ θ t,
      closedn #|θ| t →
      subst0 σ (subst0 θ t) = subst0 (map (subst0 σ) θ) t.
  Proof.
    intros σ θ t h.
    rewrite distr_subst.
    rewrite (subst_closedn σ).
    { replace (#|θ| + 0) with #|θ| by lia. assumption. }
    reflexivity.
  Qed.

  (* TODO MOVE *)
  Lemma elim_pattern_closedn :
    ∀ npat e,
      elim_pattern npat e →
      on_elim (closedn npat) e.
  Proof.
    intros npat e h.
    destruct h.
    - cbn. apply pattern_closedn. assumption.
    - cbn. split.
      + apply pattern_closedn. assumption.
      + eapply All_impl. 1: eauto.
        intros [? ?] ?. apply pattern_closedn. assumption.
    - cbn. constructor.
  Qed.

  Lemma subst_elim_subst_elim_compose :
    ∀ σ θ e,
      on_elim (closedn #|θ|) e →
      subst_elim σ 0 (subst_elim θ 0 e) = subst_elim (map (subst0 σ) θ) 0 e.
  Proof.
    intros σ θ e h.
    destruct e.
    - cbn in *. rewrite subst_subst_compose. 1: auto.
      reflexivity.
    - cbn in *. destruct h as [? h].
      rewrite subst_subst_compose. 1: auto.
      f_equal. rewrite map_map_compose.
      apply All_map_eq. eapply All_impl. 1: eauto.
      intros [? ?]. unfold on_snd. cbn. intros ?.
      f_equal. apply subst_subst_compose. assumption.
    - cbn in *. reflexivity.
  Qed.

  Lemma all_rewrite_rules_on_rewrite_rule :
    ∀ k rd,
      lookup_env Σ k = Some (RewriteDecl rd) →
      let Δ := map (vass nAnon) rd.(symbols) in
      All (on_rewrite_rule Δ) (all_rewrite_rules rd).
  Proof.
    intros k rd h Δ.
    eapply lookup_on_global_env in wfΣ as h'. 2: eauto.
    destruct h' as [Σ' [_ hd]].
    red in hd. red in hd.
    destruct hd as [? [? [? ?]]].
    unfold all_rewrite_rules. apply All_app_inv. all: auto.
  Qed.

  (* Lemma all_rewrite_rules_on_rewrite_rule' :
    ∀ k rd,
      lookup_env Σ k = Some (RewriteDecl rd) →
      let Δ := map (vass nAnon) rd.(symbols) in
      ∑ Σ',
        wf Σ'.1 ×
        All (on_rewrite_rule Δ) (all_rewrite_rules rd).
  Proof.
    intros k rd h Δ.
    eapply lookup_on_global_env in wfΣ as h'. 2: eauto.
    destruct h' as [Σ' [? hd]].
    red in hd. red in hd.
    destruct hd as [? [? [? ?]]].
    exists Σ'. intuition auto.
    unfold all_rewrite_rules. apply All_app_inv. all: auto.
  Qed. *)

  Lemma lhs_footprint_first_match :
    ∀ k r t ui σ rd,
      lookup_env Σ k = Some (RewriteDecl rd) →
      let l := all_rewrite_rules rd in
      first_match k l t = Some (ui, σ, r) →
      ∑ n l' τ θ,
        lhs_footprint t = Some (k, n, ui, l', τ) ×
        first_match k l (mkElims (tSymb k n ui) l') = Some (ui, θ, r) ×
        map (subst0 τ) θ = σ.
  Proof.
    intros k r t ui σ rd hrd l e.
    apply all_rewrite_rules_on_rewrite_rule in hrd. subst l.
    set (l := all_rewrite_rules rd) in *. clearbody l.
    induction l in ui, σ, r, e, hrd |- *. 1: discriminate.
    cbn - [ match_lhs ] in e. destruct match_lhs as [[]|] eqn:e1.
    - inversion e. subst. clear e.
      inversion hrd. subst.
      match goal with
      | h : on_rewrite_rule _ _ |- _ =>
        destruct h as [_ _ _ _ _ he _]
      end.
      eapply lhs_footprint_match_lhs in e1. 2: auto.
      destruct e1 as [l' [τ [θ [e1 [e2 ?]]]]].
      eexists _,_,_,_. intuition eauto.
      cbn - [ match_lhs ]. rewrite e2. reflexivity.
    - inversion hrd. subst.
      match goal with
      | h : on_rewrite_rule _ _ |- _ =>
        destruct h as [_ _ _ _ hl he _]
      end.
      eapply IHl in e. 2: auto.
      destruct e as [n [l' [τ [θ [? [? ?]]]]]].
      eexists _,_,_,_. intuition eauto.
      cbn - [ match_lhs ].
      destruct (match_lhs _ _ _ _ (mkElims _ _)) as [[]|] eqn:e3.
      1:{
        exfalso. clear IHl.
        eapply lhs_footprint_eq in e as ?.
        eapply lhs_footprint_closedn in e as hc.
        eapply match_lhs_sound in e3 as e4. 2: auto.
        subst.
        rewrite mkElims_subst in e4. cbn in e4.
        apply (f_equal (decompose_elims)) in e4.
        rewrite !mkElims_decompose_elims in e4. cbn in e4.
        inversion e4. subst. clear e4.
        rewrite mkElims_subst in e1. cbn - [ match_lhs ] in e1.
        rewrite map_map_compose in e1.
        eapply match_lhs_subst_length in e3 as e4.
        eapply All_impl in he as hr.
        2: eapply elim_pattern_closedn.
        erewrite All_map_eq in e1.
        2:{
          eapply All_impl. 1: eauto.
          intros x h. eapply subst_elim_subst_elim_compose.
          rewrite e4. assumption.
        }
        match type of e1 with
        | match_lhs ?npat ?k ?n ?l (mkElims (tSymb _ _ ?ui) _) = _ =>
          pose proof (match_lhs_complete npat k n ui l) as h
        end.
        match type of e1 with
        | context [ subst_elim ?σ ] =>
          specialize (h σ)
        end.
        forward h by auto.
        forward h by auto.
        forward h.
        { rewrite map_length. auto. }
        rewrite mkElims_subst in h. cbn - [ match_lhs ] in h.
        rewrite h in e1. discriminate.
      }
      auto.
  Qed.

  Lemma first_match_match_rule :
    forall k l t ui σ r,
      first_match k l t = Some (ui, σ, r) ->
      ∑ n,
        nth_error l n = Some r ×
        match_lhs #|pat_context r| k r.(head) r.(elims) t = Some (ui, σ).
  Proof.
    intros k l t ui σ r h.
    induction l in ui, σ, r, h |- *.
    - cbn in h. discriminate.
    - cbn - [ match_lhs ] in h.
      lazymatch type of h with
      | context [ match ?t with _ => _ end ] =>
        destruct t as [[ui' σ']|] eqn:e
      end.
      + noconf h. exists 0. intuition eauto.
      + apply IHl in h as [n [? ?]]. exists (S n). auto.
  Qed.

  Lemma lookup_rewrite_decl_lookup_env :
    ∀ k rd,
      lookup_rewrite_decl Σ None k = Some rd →
      lookup_env Σ k = Some (RewriteDecl rd).
  Proof.
    intros k rd e.
    unfold lookup_rewrite_decl in e. unfold lookup_rd in e.
    destruct lookup_env as [[]|] eqn:e1. all: try discriminate.
    apply some_inj in e. subst. reflexivity.
  Qed.

  Lemma rule_assumption_context :
    ∀ k rd n r,
      lookup_env Σ k = Some (RewriteDecl rd) →
      nth_error (all_rewrite_rules rd) n = Some r →
      assumption_context r.(pat_context).
  Proof.
    intros k rd n r h hr.
    eapply all_rewrite_rules_on_rewrite_rule in h.
    eapply All_nth_error in h. 2: eauto.
    destruct h as [].
    assumption.
  Qed.

  Lemma rule_closed_rhs :
    ∀ k rd n r,
      lookup_env Σ k = Some (RewriteDecl rd) →
      nth_error (all_rewrite_rules rd) n = Some r →
      closedn (#|r.(pat_context)| + #|rd.(symbols)|) (rhs r).
  Proof.
    intros k rd n r h hr.
    eapply all_rewrite_rules_on_rewrite_rule in h.
    eapply All_nth_error in h. 2: eauto.
    destruct h as [? ? h].
    rewrite map_length in h.
    replace (#|pat_context r| + #|symbols rd|)
    with (#|symbols rd| + #|pat_context r|)
    by lia.
    assumption.
  Qed.

  Lemma rule_linear :
    ∀ k rd n r,
      lookup_env Σ k = Some (RewriteDecl rd) →
      nth_error (all_rewrite_rules rd) n = Some r →
      linear #|r.(pat_context)| r.(elims).
  Proof.
    intros k rd n r h hr.
    eapply all_rewrite_rules_on_rewrite_rule in h.
    eapply All_nth_error in h. 2: eauto.
    destruct h as [].
    assumption.
  Qed.

  Lemma rule_head :
    ∀ k rd n r,
      lookup_env Σ k = Some (RewriteDecl rd) →
      nth_error (all_rewrite_rules rd) n = Some r →
      r.(head) < #|rd.(symbols)|.
  Proof.
    intros k rd n r h hr.
    eapply all_rewrite_rules_on_rewrite_rule in h.
    eapply All_nth_error in h. 2: eauto.
    destruct h as [? ? ? h].
    rewrite map_length in h.
    assumption.
  Qed.

  Lemma rule_elim_pattern :
    ∀ k rd n r,
      lookup_env Σ k = Some (RewriteDecl rd) →
      nth_error (all_rewrite_rules rd) n = Some r →
      All (elim_pattern #|pat_context r|) r.(elims).
  Proof.
    intros k rd n r h hr.
    eapply all_rewrite_rules_on_rewrite_rule in h.
    eapply All_nth_error in h. 2: eauto.
    destruct h as [].
    assumption.
  Qed.

  Lemma rule_is_rewrite_rule :
    ∀ k rd n r,
      lookup_env Σ k = Some (RewriteDecl rd) →
      nth_error (all_rewrite_rules rd) n = Some r →
      is_rewrite_rule Σ k rd r.
  Proof.
    intros k rd n r h hr.
    unfold is_rewrite_rule. intuition eauto.
    unfold all_rewrite_rules in hr.
    apply nth_error_app_dec in hr as [[]|[]].
    - right. eexists. eauto.
    - left. eexists. eauto.
  Qed.

  Lemma rule_symbols_subst :
    ∀ k ui rd r n m,
      lookup_env Σ k = Some (RewriteDecl rd) →
      nth_error (all_rewrite_rules rd) n = Some r →
      #|pat_context r| = m →
      subst
        (symbols_subst k 0 ui #|symbols rd|) m
        (tRel (#|pat_context r| + head r))
      = tSymb k r.(head) ui.
  Proof.
    intros k ui rd r n ? hrd hr [].
    cbn.
    destruct (Nat.leb_spec0 #|pat_context r| (#|pat_context r| + head r)).
    2: lia.
    replace (#|pat_context r| + head r - #|pat_context r|)
    with r.(head) by lia.
    destruct (nth_error _ r.(head)) eqn:e1.
    2:{
      apply nth_error_None in e1. rewrite symbols_subst_length in e1.
      eapply rule_head in hr. 2: eauto.
      lia.
    }
    unfold symbols_subst in e1.
    eapply list_make_nth_error in e1. subst.
    cbn. f_equal. lia.
  Qed.

  Definition rho_elimi Γ e :=
    match e with
    | eApp p => eApp (rho Σ None Γ p)
    | eCase ind p brs =>
      eCase ind (rho Σ None Γ p) (map (on_snd (rho Σ None Γ)) brs)
    | eProj p => eProj p
    end.

  Lemma rho_subst_pattern :
    ∀ Γ p τ,
      pattern #|τ| p →
      rho Σ None Γ (subst0 τ p) = subst0 (map (rho Σ None Γ) τ) p.
  Proof.
    intros Γ p τ hp.
    induction hp
    as [n hn | ind n ui args ha ih]
    in Γ |- *
    using pattern_all_rect.
    - cbn. rewrite nth_error_map.
      destruct nth_error eqn:e.
      2:{
        eapply nth_error_None in e. lia.
      }
      cbn. rewrite !lift0_id. reflexivity.
    - rewrite !subst_mkApps. cbn. simp rho. f_equal.
      rewrite !map_map_compose. apply All_map_eq.
      eapply All_impl. 1: eauto.
      cbn. intros. auto.
  Qed.

  Lemma map_rho_subst_pattern :
    ∀ Γ τ θ,
      All (pattern #|τ|) θ →
      map (rho Σ None Γ) (map (subst0 τ) θ) =
      map (subst0 (map (rho Σ None Γ) τ)) θ.
  Proof.
    intros Γ τ θ hθ.
    rewrite map_map_compose. apply All_map_eq.
    eapply All_impl. 1: eauto.
    intros p hp. eapply rho_subst_pattern. assumption.
  Qed.

  Lemma map_rho_subst_elim :
    ∀ Γ τ l,
      All (elim_pattern #|τ|) l →
      map (rho_elimi Γ) (map (subst_elim τ 0) l) =
      map (subst_elim (map (rho Σ None Γ) τ) 0) l.
  Proof.
    intros Γ τ l hl.
    rewrite map_map_compose. eapply All_map_eq.
    eapply All_impl. 1: eauto.
    intros ? [].
    - cbn. f_equal. apply rho_subst_pattern. assumption.
    - cbn. f_equal.
      + apply rho_subst_pattern. assumption.
      + rewrite map_map_compose. eapply All_map_eq.
        eapply All_impl. 1: eauto.
        intros [? ?]. unfold on_snd. cbn. intro.
        f_equal. apply rho_subst_pattern. assumption.
    - cbn. reflexivity.
  Qed.

  Lemma mkElims_subst_isnotFixLambda :
    ∀ k n ui l,
      ~~ isFixLambda (mkElims (tSymb k n ui) l).
  Proof.
    intros k n ui l.
    induction l as [| [] l ih] in k, n, ui |- * using list_rect_rev.
    - cbn. reflexivity.
    - rewrite mkElims_app. cbn. reflexivity.
    - rewrite mkElims_app. cbn. reflexivity.
    - rewrite mkElims_app. cbn. reflexivity.
  Qed.

  Lemma mkElims_subst_isnotFixLambda_app :
    ∀ k n ui l,
      ~~ isFixLambda_app (mkElims (tSymb k n ui) l).
  Proof.
    intros k n ui l.
    induction l as [| [] l ih] in k, n, ui |- * using list_rect_rev.
    - cbn. reflexivity.
    - rewrite mkElims_app. cbn.
      destruct mkElims eqn:e. all: try reflexivity.
      + apply (f_equal isFixLambda) in e. cbn in e.
        rewrite <- e. apply mkElims_subst_isnotFixLambda.
      + rewrite <- e. apply ih.
      + apply (f_equal isFixLambda) in e. cbn in e.
        rewrite <- e. apply mkElims_subst_isnotFixLambda.
    - rewrite mkElims_app. cbn. reflexivity.
    - rewrite mkElims_app. cbn. reflexivity.
  Qed.

  Lemma prefix_app :
    ∀ {A} (a b c : list A),
      prefix a b →
      prefix a (b ++ c).
  Proof.
    intros A a b c [d e]. subst.
    exists (d ++ c). rewrite app_assoc. reflexivity.
  Qed.

  Lemma prefix_length :
    ∀ {A} (a b : list A),
      prefix a b →
      #|a| ≤ #|b|.
  Proof.
    intros A a b [c e]. subst.
    rewrite app_length. lia.
  Qed.

  Lemma prefix_strict_prefix_app :
    ∀ {A} (a b c : list A),
      prefix a b →
      #|c| > 0 →
      strict_prefix a (b ++ c).
  Proof.
    intros A a b c p h.
    split.
    - apply prefix_app. assumption.
    - apply prefix_length in p. rewrite app_length. lia.
  Qed.

  Lemma prefix_strict_prefix_append :
    ∀ {A} (a b : list A) x,
      prefix a b →
      strict_prefix a (b ++ [x]).
  Proof.
    intros A a b x h.
    apply prefix_strict_prefix_app. all: auto.
  Qed.

  Lemma rho_mkElims_not_lhs :
    ∀ Γ k n ui el,
      (∀ el', prefix el' el → not_lhs Σ None (mkElims (tSymb k n ui) el')) →
      rho Σ None Γ (mkElims (tSymb k n ui) el) =
      mkElims (tSymb k n ui) (map (rho_elimi Γ) el).
  Proof.
    intros Γ k n ui el h.
    induction el in Γ, k, n, ui, h |- * using list_rect_rev.
    - cbn. simp rho.
      destruct lhs_viewc as [? ? ? ? ? hk fme |].
      1:{
        specialize (h []).
        forward h.
        { exists []. auto. }
        cbn in h.
        exfalso. apply h.
        eexists _,_,_. intuition eauto.
      }
      cbn. reflexivity.
    - simp rho.
      destruct lhs_viewc as [? ? ? ? ? hk fme |].
      1:{
        eapply first_match_lookup_sound in fme as et. 2-4: eauto.
        2: exact I.
        unfold lhs in et. rewrite !mkElims_subst in et.
        eapply lookup_rewrite_decl_lookup_env in hk as hk'.
        eapply first_match_rule_list in fme as hr'. destruct hr' as [? hr'].
        eapply first_match_subst_length in fme as hl.
        erewrite rule_symbols_subst in et. 2-4: eauto.
        cbn in et. apply (f_equal decompose_elims) in et.
        rewrite !mkElims_decompose_elims in et. cbn in et.
        symmetry in et. inversion et. subst.
        exfalso. eapply h.
        2:{
          eexists k, rd, _. intuition eauto.
        }
        exists []. rewrite app_nil_r. reflexivity.
      }
      rewrite map_app. rewrite !mkElims_app. cbn.
      destruct a as [| []| [[] ?]].
      + cbn. rewrite view_lambda_fix_app_other.
        2:{
          replace (tApp (mkElims (tSymb k n ui) el) p)
          with (mkElims (tSymb k n ui) (el ++ [eApp p])).
          2:{
            rewrite mkElims_app. reflexivity.
          }
          apply mkElims_subst_isnotFixLambda_app.
        }
        intro. cbn. f_equal.
        eapply IHel.
        intros el' hx. eapply h.
        apply prefix_app. auto.
      + simp rho.
        set (app := inspect _).
        destruct app as [[f l] eqapp].
        autorewrite with rho.
        assert (h' : ∑ h, view_construct_cofix f = construct_cofix_other f h).
        { clear - eqapp. unfold decompose_app in eqapp.
          revert eqapp. generalize (@nil term).
          intros l' e.
          induction el as [| [] el ih] in f, l, l', e |- * using list_rect_rev.
          - cbn in e. inversion e. cbn.
            simp view_construct_cofix. eexists. reflexivity.
          - rewrite mkElims_app in e. cbn in e.
            eapply ih in e. auto.
          - rewrite mkElims_app in e. cbn in e.
            inversion e. cbn.
            simp view_construct_cofix. eexists. reflexivity.
          - rewrite mkElims_app in e. cbn in e.
            inversion e. cbn.
            simp view_construct_cofix. eexists. reflexivity.
        }
        destruct h' as [? e].
        rewrite e. simp rho.
        cbn. rewrite <- !fold_rho. f_equal.
        eapply IHel.
        intros el' hx. eapply h.
        apply prefix_app. auto.
      + simp rho.
        set (app := inspect _).
        destruct app as [[f l] eqapp].
        autorewrite with rho.
        assert (h' : ∑ h, view_construct_cofix f = construct_cofix_other f h).
        { clear - eqapp. unfold decompose_app in eqapp.
          revert eqapp. generalize (@nil term).
          intros l' e.
          induction el as [| [] el ih] in f, l, l', e |- * using list_rect_rev.
          - cbn in e. inversion e. cbn.
            simp view_construct_cofix. eexists. reflexivity.
          - rewrite mkElims_app in e. cbn in e.
            eapply ih in e. auto.
          - rewrite mkElims_app in e. cbn in e.
            inversion e. cbn.
            simp view_construct_cofix. eexists. reflexivity.
          - rewrite mkElims_app in e. cbn in e.
            inversion e. cbn.
            simp view_construct_cofix. eexists. reflexivity.
        }
        destruct h' as [? e].
        rewrite e. simp rho.
        cbn. rewrite <- !fold_rho. f_equal.
        eapply IHel.
        intros el' hx. eapply h.
        apply prefix_app. auto.
  Qed.

  Lemma linear_mask_app_inv :
    ∀ n l1 l2 m,
      linear_mask n (l1 ++ l2) = Some m →
      ∑ m1 m2,
        linear_mask n l1 = Some m1 ×
        linear_mask n l2 = Some m2 ×
        lin_merge m1 m2 = Some m.
  Admitted.

  (* Already proven as pattern_reduct *)
  (* Lemma pred1_pattern_mask :
    ∀ npat p m Γ Γ' t σ,
      pattern npat p →
      pattern_mask npat p = Some m →
      pred1 Σ Γ Γ' (subst0 σ p) t →
      ∑ σ',
        ∀ σ'',
          subs_complete σ' σ'' →
          t = subst0 σ'' p ×
          All2_mask_subst (pred1 Σ Γ Γ') m σ σ'.
  Admitted. *)

  Lemma All_cons_inv :
    ∀ A P x l,
      @All A P (x :: l) →
      P x × All P l.
  Proof.
    intros A P x l h. inversion h.
    intuition auto.
  Qed.

  Lemma pred_atom_mkElims :
    ∀ t l,
      pred_atom (mkElims t l) →
      pred_atom t ∧ l = [].
  Proof.
    intros t l h.
    destruct l as [| [] l] using list_rect_rev.
    - intuition eauto.
    - rewrite mkElims_app in h. cbn in h. discriminate.
    - rewrite mkElims_app in h. cbn in h. discriminate.
    - rewrite mkElims_app in h. cbn in h. discriminate.
  Qed.

  Lemma pred1_elim_not_lhs_inv :
    ∀ Γ Γ' k n ui el t,
      (∀ el', prefix el' el → not_lhs Σ None (mkElims (tSymb k n ui) el')) →
      pred1 Σ Γ Γ' (mkElims (tSymb k n ui) el) t →
      ∑ el',
        All2 (pred1_elim Σ Γ Γ') el el' ×
        t = mkElims (tSymb k n ui) el'.
  Proof.
    intros Γ Γ' k n ui el t notlhs h.
    remember (mkElims (tSymb k n ui) el) as u eqn:e.
    revert Γ Γ' u t h k n ui el notlhs e.
    pose (Pctx := fun (Γ Δ : context) => True).
    refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: subst Pctx.
    all: intros.
    all: try solve [
      apply (f_equal elim_kn) in e ; rewrite elim_kn_mkElims in e ;
      cbn in e ; discriminate
    ].
    all: try solve [
      apply (f_equal elim_kn) in e ; rewrite elim_kn_mkElims in e ;
      cbn in e ; rewrite elim_kn_mkApps in e ; cbn in e ; discriminate
    ].
    - cbn. auto.
    - apply (f_equal decompose_elims) in e.
      rewrite mkElims_decompose_elims in e. cbn in e.
      inversion e. subst.
      exists []. intuition auto.
    - specialize (notlhs el).
      forward notlhs.
      { exists []. rewrite app_nil_r. auto. }
      rewrite <- e in notlhs.
      exfalso. apply notlhs.
      pose proof (match_lhs_complete #|r.(pat_context)| k0 r.(head) ui0 r.(elims) s) as h.
      forward h.
      { eapply declared_symbol_pattern. all: eauto. }
      forward h.
      { eapply declared_symbol_linear. all: eauto. }
      apply untyped_subslet_length in X1. rewrite subst_context_length in X1.
      forward h by auto.
      eapply match_lhs_first_match with (l := all_rewrite_rules decl) (n := #|decl.(prules)| + n) in h.
      2:{
        rewrite nth_error_app_ge. 1: lia.
        rewrite <- H1. f_equal. lia.
      }
      destruct h as [? h].
      subst lhs. unfold lhs in e.
      rewrite !mkElims_subst in e. erewrite rule_symbols_subst with (n := #|decl.(prules)| + n) in e. all: eauto.
      2:{
        rewrite nth_error_app_ge. 1: lia.
        rewrite <- H1. f_equal. lia.
      }
      cbn in e. apply (f_equal decompose_elims) in e.
      rewrite !mkElims_decompose_elims in e. cbn in e. inversion e. subst.
      unfold declared_symbol in H0.
      unfold lookup_rewrite_decl. unfold lookup_rd.
      rewrite mkElims_subst in h. cbn in h.
      eexists _,_,_. split.
      + erewrite H0. reflexivity.
      + unfold lhs.
        rewrite !mkElims_subst. erewrite rule_symbols_subst with (n := #|decl.(prules)| + n).
        all: eauto.
        2:{
          rewrite nth_error_app_ge. 1: lia.
          rewrite <- H1. f_equal. lia.
        }
        cbn. rewrite subst_elims_symbols_subst.
        { rewrite X1. eapply declared_symbol_pattern. all: eauto. }
        eauto.
    - specialize (notlhs el).
      forward notlhs.
      { exists []. rewrite app_nil_r. auto. }
      rewrite <- e in notlhs.
      exfalso. apply notlhs.
      pose proof (match_lhs_complete #|r.(pat_context)| k0 r.(head) ui0 r.(elims) s) as h.
      forward h.
      { eapply declared_symbol_par_pattern. all: eauto. }
      forward h.
      { eapply declared_symbol_par_linear. all: eauto. }
      apply untyped_subslet_length in X1. rewrite subst_context_length in X1.
      forward h by auto.
      eapply match_lhs_first_match with (l := all_rewrite_rules decl) (n := n) in h.
      2:{ apply nth_error_app_left. auto. }
      destruct h as [? h].
      subst lhs. unfold lhs in e.
      rewrite !mkElims_subst in e. erewrite rule_symbols_subst with (n := n) in e. all: eauto.
      2:{ apply nth_error_app_left. auto. }
      cbn in e. apply (f_equal decompose_elims) in e.
      rewrite !mkElims_decompose_elims in e. cbn in e. inversion e. subst.
      unfold declared_symbol in H0.
      unfold lookup_rewrite_decl. unfold lookup_rd.
      rewrite mkElims_subst in h. cbn in h.
      eexists _,_,_. split.
      + erewrite H0. reflexivity.
      + unfold lhs.
        rewrite !mkElims_subst. erewrite rule_symbols_subst with (n := n).
        all: eauto.
        2:{ apply nth_error_app_left. auto. }
        cbn. rewrite subst_elims_symbols_subst.
        { rewrite X1. eapply declared_symbol_par_pattern. all: eauto. }
        eauto.
    - destruct el as [| [] el] using list_rect_rev.
      1: discriminate.
      2:{ rewrite mkElims_app in e. cbn in e. discriminate. }
      2:{ rewrite mkElims_app in e. cbn in e. discriminate. }
      rewrite mkElims_app in e. cbn in e. inversion e. subst. clear e.
      clear IHel.
      specialize X0 with (2 := eq_refl).
      forward X0.
      { intros el' hx. apply notlhs.
        eapply prefix_app. auto.
      }
      destruct X0 as [el' [he ?]]. subst.
      eexists (el' ++ [ eApp _ ]).
      split.
      + apply All2_app. 1: auto.
        constructor. 2: constructor.
        constructor. eauto.
      + rewrite mkElims_app. cbn. reflexivity.
    - destruct el as [| [] el] using list_rect_rev.
      1: discriminate.
      1:{ rewrite mkElims_app in e. cbn in e. discriminate. }
      2:{ rewrite mkElims_app in e. cbn in e. discriminate. }
      rewrite mkElims_app in e. cbn in e. inversion e. subst. clear e.
      clear IHel.
      specialize X2 with (2 := eq_refl).
      forward X2.
      { intros el' hx. apply notlhs.
        eapply prefix_app. auto.
      }
      destruct X2 as [el' [he ?]]. subst.
      eexists (el' ++ [ eCase _ _ _ ]).
      split.
      + apply All2_app. 1: auto.
        constructor. 2: constructor.
        constructor. 1: eauto.
        eapply All2_impl. 1: eauto.
        intros [] []. cbn. intros. intuition eauto.
      + rewrite mkElims_app. cbn. reflexivity.
    - destruct el as [| [] el] using list_rect_rev.
      1: discriminate.
      1:{ rewrite mkElims_app in e. cbn in e. discriminate. }
      1:{ rewrite mkElims_app in e. cbn in e. discriminate. }
      rewrite mkElims_app in e. cbn in e. inversion e. subst. clear e.
      clear IHel.
      specialize X0 with (2 := eq_refl).
      forward X0.
      { intros el' hx. apply notlhs.
        eapply prefix_app. auto.
      }
      destruct X0 as [el' [he ?]]. subst.
      eexists (el' ++ [ eProj _ ]).
      split.
      + apply All2_app. 1: auto.
        constructor. 2: constructor.
        constructor.
      + rewrite mkElims_app. cbn. reflexivity.
    - subst. apply pred_atom_mkElims in H0 as [e ?].
      cbn in e. discriminate.
  Qed.

  Lemma cons_inv :
    ∀ {A} (x y : A) l l',
      x :: l = y :: l' →
      x = y × l = l'.
  Proof.
    intros A x y l l' e.
    inversion e. intuition eauto.
  Qed.

  Inductive All2_mask (P : term -> term -> Type) :
    list bool -> list term -> list term -> Type :=
  | All2_mask_nil : All2_mask P [] [] []
  | All2_mask_true :
      forall t u m l s,
        P t u ->
        All2_mask P m l s ->
        All2_mask P (true :: m) (t :: l) (u :: s)
  | All2_mask_psubst_false :
      forall t u m l s,
        All2_mask P m l s ->
        All2_mask P (false :: m) (t :: l) (u :: s).

  Lemma All2_mask_linear_mask_init :
    ∀ P n σ ρ,
      #|σ| = n →
      #|ρ| = n →
      All2_mask P (linear_mask_init n) σ ρ.
  Proof.
    intros P n σ ρ e1 e2.
    induction n in σ, ρ, e1, e2 |- *.
    - cbn.
      destruct σ. 2: discriminate.
      destruct ρ. 2: discriminate.
      constructor.
    - destruct σ. 1: discriminate.
      destruct ρ. 1: discriminate.
      cbn. constructor.
      cbn in e1. cbn in e2.
      eapply IHn. all: lia.
  Qed.

  Lemma All2_mask_lin_set :
    ∀ P n m m' σ x θ y,
      lin_set n m = Some m' →
      nth_error σ n = Some x →
      nth_error θ n = Some y →
      P x y →
      All2_mask P m σ θ →
      All2_mask P m' σ θ.
  Proof.
    intros P n m m' σ x θ y hm hσ hθ h1 h2.
    induction h2 in n, m', hm, x, hσ, y, hθ, h1 |- *.
    - destruct n. all: discriminate.
    - destruct n. 1: discriminate.
      cbn in hm. destruct lin_set eqn:hm'. 2: discriminate.
      apply some_inj in hm. subst.
      cbn in hσ. cbn in hθ.
      constructor. 1: auto.
      eapply IHh2. all: eauto.
    - destruct n.
      + cbn in hm. apply some_inj in hm. subst.
        cbn in hσ. cbn in hθ.
        apply some_inj in hσ. apply some_inj in hθ. subst.
        constructor. all: auto.
      + cbn in hm. destruct lin_set eqn:hm'. 2: discriminate.
        apply some_inj in hm. subst.
        cbn in hσ. cbn in hθ.
        constructor.
        eapply IHh2. all: eauto.
  Qed.

  Lemma All2_mask_lin_merge :
    ∀ P m1 m2 m σ θ,
      lin_merge m1 m2 = Some m →
      All2_mask P m1 σ θ →
      All2_mask P m2 σ θ →
      All2_mask P m σ θ.
  Proof.
    intros P m1 m2 m σ θ hm h1 h2.
    induction h1 in m2, h2, m, hm |- *.
    - destruct m2. 2: discriminate.
      cbn in hm. apply some_inj in hm. subst.
      constructor.
    - destruct m2 as [| []]. 1,2: discriminate.
      cbn in hm. destruct lin_merge eqn:e1. 2: discriminate.
      apply some_inj in hm. subst.
      inversion h2. subst.
      constructor. 1: auto.
      eapply IHh1. all: eauto.
    - destruct m2. 1: discriminate.
      cbn in hm. destruct lin_merge eqn:e1. 2: discriminate.
      apply some_inj in hm. subst.
      destruct b.
      + inversion h2. subst.
        constructor. 1: auto.
        eapply IHh1. all: eauto.
      + inversion h2. subst.
        constructor.
        eapply IHh1. all: eauto.
  Qed.

  Lemma pattern_mask_subst_inj :
    ∀ σ θ p npat m,
      pattern npat p →
      pattern_mask npat p = Some m →
      #|σ| = npat →
      #|θ| = npat →
      subst0 σ p = subst0 θ p →
      All2_mask eq m σ θ.
  Proof.
    intros σ θ p npat m hp hm eσ eθ e.
    induction hp
    as [n hn | ind n ui args ha ih]
    in σ, θ, m, hm, eσ, eθ, e |- *
    using pattern_all_rect.
    - cbn in hm. cbn in e.
      destruct (nth_error σ) eqn:e1.
      2:{ apply nth_error_None in e1. lia. }
      destruct (nth_error θ) eqn:e2.
      2:{ apply nth_error_None in e2. lia. }
      rewrite !lift0_id in e.
      replace (n - 0) with n in e1 by lia.
      replace (n - 0) with n in e2 by lia.
      eapply All2_mask_lin_set. all: eauto.
      apply All2_mask_linear_mask_init. all: auto.
    - rewrite !subst_mkApps in e. cbn in e.
      apply (f_equal decompose_app) in e.
      rewrite !decompose_app_mkApps in e. 1,2: auto.
      apply (f_equal snd) in e. cbn in e.
      eapply All_prod in ih. 2: exact ha.
      clear ha.
      induction ih
      as [| p args [hp ihp] _ ih]
      in σ, θ, m, hm, eσ, eθ, e |- *
      using All_rev_rect.
      + cbn in hm. apply some_inj in hm. subst.
        apply All2_mask_linear_mask_init. all: auto.
      + rewrite <- mkApps_nested in hm. cbn in hm.
        destruct pattern_mask eqn:e1. 2: discriminate.
        move hm at top.
        destruct pattern_mask eqn:e2. 2: discriminate.
        rewrite !map_app in e. cbn in e.
        apply (f_equal rev) in e. rewrite !rev_app in e.
        cbn in e. apply cons_inv in e as [e3 e4].
        apply (f_equal rev) in e4. rewrite !rev_invol in e4.
        eapply All2_mask_lin_merge. all: eauto.
  Qed.

  Lemma map_subst_elim_inj_mask :
    ∀ σ θ npat l m,
      All (elim_pattern npat) l →
      linear_mask npat l = Some m →
      #|σ| = npat →
      #|θ| = npat →
      map (subst_elim σ 0) l = map (subst_elim θ 0) l →
      All2_mask eq m σ θ.
  Proof.
    intros σ θ npat l m hl hm e1 e2 e.
    induction hl as [| ? l [] hl ih ] in σ, θ, m, hm, e1, e2, e |- *.
    - cbn in hm. apply some_inj in hm. subst.
      apply All2_mask_linear_mask_init. all: auto.
    - cbn in hm. destruct pattern_mask eqn:e3. 2: discriminate.
      destruct monad_map eqn:e4. 2: discriminate.
      cbn in hm. destruct PCUICPattern.monad_fold_right eqn:e5. 2: discriminate.
      cbn in e. apply cons_inv in e as [e6 e7].
      inversion e6.
      eapply pattern_mask_subst_inj in e3. 5: eassumption. 2-4: eauto.
      eapply All2_mask_lin_merge. all: eauto.
      eapply ih. all: eauto.
      unfold linear_mask. rewrite e4. cbn. auto.
    - cbn in hm. destruct pattern_mask eqn:e3. 2: discriminate.
      destruct monad_map eqn:e4. 2: discriminate.
      destruct PCUICPattern.monad_fold_right eqn:e5. 2: discriminate.
      destruct lin_merge eqn:e6. 2: discriminate.
      move hm at top.
      destruct monad_map eqn:e7. 2: discriminate.
      cbn in hm.
      destruct PCUICPattern.monad_fold_right eqn:e8. 2: discriminate.
      cbn in e. apply cons_inv in e as [e9 e10].
      inversion e9.
      eapply pattern_mask_subst_inj in e3. 5: eassumption. 2-4: eauto.
      eapply ih in e10. 3-4: auto.
      2:{ unfold linear_mask. rewrite e7. cbn. eauto. }
      eapply All2_mask_lin_merge. all: eauto.
      eapply All2_mask_lin_merge. all: eauto.
      clear - a l1 e4 l2 e5 e1 e2 H1.
      induction a in l1, e4, l2, e5, H1 |- *.
      + cbn in e4. apply some_inj in e4. subst.
        cbn in e5. apply some_inj in e5. subst.
        apply All2_mask_linear_mask_init. all: auto.
      + cbn in e4. destruct pattern_mask eqn:e3. 2: discriminate.
        destruct monad_map eqn:e6. 2: discriminate.
        apply some_inj in e4. subst.
        cbn in e5.
        destruct PCUICPattern.monad_fold_right eqn:e7. 2: discriminate.
        cbn in H1. destruct x. cbn in *.
        inversion H1.
        eapply pattern_mask_subst_inj in e3. 5: eassumption. 2-4: eauto.
        eapply All2_mask_lin_merge. all: eauto.
    - cbn in hm. destruct monad_map eqn:e3. 2: discriminate.
      cbn in hm. destruct PCUICPattern.monad_fold_right eqn:e4. 2: discriminate.
      cbn in e. inversion e.
      eapply ih. all: auto.
      unfold linear_mask. rewrite e3. cbn.
      eapply lin_merge_sym in hm.
      eapply lin_merge_linear_mask_init_eq in hm. subst.
      auto.
  Qed.

  Lemma All2_mask_all :
    ∀ P σ θ m,
      forallb (fun x => x) m →
      All2_mask P m σ θ →
      All2 P σ θ.
  Proof.
    intros P σ θ m hm h.
    induction h in hm |- *.
    - constructor.
    - cbn in hm. constructor. all: auto.
    - cbn in hm. discriminate.
  Qed.

  Lemma map_subst_elim_inj :
    ∀ σ θ npat l,
      All (elim_pattern npat) l →
      linear npat l →
      #|σ| = npat →
      #|θ| = npat →
      map (subst_elim σ 0) l = map (subst_elim θ 0) l →
      σ = θ.
  Proof.
    intros σ θ npat l hl ll eσ eθ e.
    unfold linear in ll. destruct linear_mask as [m|] eqn:hm. 2: discriminate.
    eapply All2_eq. eapply All2_mask_all. 1: eauto.
    eapply map_subst_elim_inj_mask. all: eauto.
  Qed.

  Definition pattern_list_mask npat l :=
    m <- monad_map (pattern_mask npat) l ;;
    PCUICPattern.monad_fold_right lin_merge m (linear_mask_init npat).

  Definition pattern_list_linear npat l :=
    match pattern_list_mask npat l with
    | Some m => forallb (λ x, x) m
    | None => false
    end.

  Lemma pattern_list_mask_cons :
    ∀ npat x l,
      pattern_list_mask npat (x :: l) = (
        m1 <- pattern_mask npat x ;;
        m2 <- pattern_list_mask npat l ;;
        lin_merge m2 m1
      ).
  Proof.
    intros npat x l.
    cbn. destruct pattern_mask eqn:e1. 2: auto.
    destruct monad_map eqn:e2. 2: auto.
    cbn. reflexivity.
  Qed.

  Inductive All_mask (P : term → Type) : list bool → list term → Type :=
  | All_mask_nil : All_mask P [] []
  | All_mask_true :
      ∀ t m l,
        P t →
        All_mask P m l →
        All_mask P (true :: m) (t :: l)
  | All_mask_false :
      ∀ t m l,
        All_mask P m l →
        All_mask P (false :: m) (t :: l).

  Lemma All_mask_linear_mask_init :
    ∀ P n σ,
      #|σ| = n →
      All_mask P (linear_mask_init n) σ.
  Proof.
    intros P n σ e.
    induction n in σ, e |- *.
    - cbn.
      destruct σ. 2: discriminate.
      constructor.
    - destruct σ. 1: discriminate.
      cbn. constructor.
      cbn in e.
      eapply IHn. lia.
  Qed.

  Lemma All_mask_lin_set :
    ∀ P n m m' σ x,
      lin_set n m = Some m' →
      nth_error σ n = Some x →
      P x →
      All_mask P m σ →
      All_mask P m' σ.
  Proof.
    intros P n m m' σ x hm hσ h1 h2.
    induction h2 in n, m', hm, x, hσ, h1 |- *.
    - destruct n. all: discriminate.
    - destruct n. 1: discriminate.
      cbn in hm. destruct lin_set eqn:hm'. 2: discriminate.
      apply some_inj in hm. subst.
      cbn in hσ.
      constructor. 1: auto.
      eapply IHh2. all: eauto.
    - destruct n.
      + cbn in hm. apply some_inj in hm. subst.
        cbn in hσ.
        apply some_inj in hσ. subst.
        constructor. all: auto.
      + cbn in hm. destruct lin_set eqn:hm'. 2: discriminate.
        apply some_inj in hm. subst.
        cbn in hσ.
        constructor.
        eapply IHh2. all: eauto.
  Qed.

  Lemma All_mask_lin_merge :
    ∀ P m1 m2 m σ,
      lin_merge m1 m2 = Some m →
      All_mask P m1 σ →
      All_mask P m2 σ →
      All_mask P m σ.
  Proof.
    intros P m1 m2 m σ hm h1 h2.
    induction h1 in m2, h2, m, hm |- *.
    - destruct m2. 2: discriminate.
      cbn in hm. apply some_inj in hm. subst.
      constructor.
    - destruct m2 as [| []]. 1,2: discriminate.
      cbn in hm. destruct lin_merge eqn:e1. 2: discriminate.
      apply some_inj in hm. subst.
      inversion h2. subst.
      constructor. 1: auto.
      eapply IHh1. all: eauto.
    - destruct m2. 1: discriminate.
      cbn in hm. destruct lin_merge eqn:e1. 2: discriminate.
      apply some_inj in hm. subst.
      destruct b.
      + inversion h2. subst.
        constructor. 1: auto.
        eapply IHh1. all: eauto.
      + inversion h2. subst.
        constructor.
        eapply IHh1. all: eauto.
  Qed.

  Lemma All_mask_true_All :
    ∀ P m σ,
      All_mask P m σ →
      forallb (λ x, x) m →
      All P σ.
  Proof.
    intros P m σ h1 h2.
    induction h1.
    - constructor.
    - cbn in h2. constructor. all: auto.
    - cbn in h2. discriminate.
  Qed.

  Fixpoint mask_filter {A} (m : list bool) (l : list A) :=
    match m, l with
    | true :: m, x :: l => x :: mask_filter m l
    | false :: m, x :: l => mask_filter m l
    | _, _ => []
    end.

  Lemma mask_filter_linear_mask_init :
    ∀ {A} n (l : list A),
      mask_filter (linear_mask_init n) l = [].
  Proof.
    intros A n l.
    induction n in l |- *.
    - cbn. reflexivity.
    - cbn. destruct l.
      + reflexivity.
      + apply IHn.
  Qed.

  Lemma mask_filter_all_true :
    ∀ {A} (l : list A) m,
      forallb (λ x, x) m →
      #|l| = #|m| →
      mask_filter m l = l.
  Proof.
    intros A l m h e.
    induction m as [| [] m ih] in l, h, e |- *.
    - cbn. destruct l. 2: discriminate.
      reflexivity.
    - cbn in *. destruct l. 1: discriminate.
      cbn in e. f_equal. eapply ih.
      + auto.
      + lia.
    - cbn in h. discriminate.
  Qed.

  Lemma option_map_mask_filter_lin_merge :
    ∀ {A B} m1 m2 m (f : A → option B) l1 l2 l,
      lin_merge m1 m2 = Some m →
      monad_map f (mask_filter m1 l) = Some l1 →
      monad_map f (mask_filter m2 l) = Some l2 →
      ∑ l',
        Permutation (l1 ++ l2) l' ×
        monad_map f (mask_filter m l) = Some l'.
  Proof.
    intros A B m1 m2 m f l1 l2 l hm h1 h2.
    induction m1 as [| [] m1 ih] in m2, m, hm, l, l1, h1, l2, h2 |- *.
    - destruct m2. 2: discriminate.
      cbn in hm. apply some_inj in hm. subst.
      cbn in h1. apply some_inj in h1. subst.
      cbn in h2. apply some_inj in h2. subst.
      cbn. exists []. intuition auto.
    - destruct m2 as [| [] m2]. 1,2: discriminate.
      cbn in hm. destruct lin_merge eqn:hm'. 2: discriminate.
      apply some_inj in hm. subst.
      cbn in h1. cbn in h2.
      destruct l.
      + cbn in h1. apply some_inj in h1. subst.
        cbn in h2. apply some_inj in h2. subst.
        cbn. exists []. intuition auto.
      + cbn in h1. destruct f eqn:e1. 2: discriminate.
        destruct monad_map eqn:e2. 2: discriminate.
        apply some_inj in h1. subst.
        cbn. rewrite e1.
        specialize ih with (1 := hm').
        specialize ih with (1 := e2) (2 := h2).
        destruct ih as [l' [hp e]].
        rewrite e.
        eexists. split. 2: reflexivity.
        constructor. assumption.
    - destruct m2 as [| b m2]. 1: discriminate.
      cbn in hm. destruct lin_merge eqn:hm'. 2: discriminate.
      apply some_inj in hm. subst.
      cbn in h1. cbn in h2.
      destruct l.
      + cbn in h1. apply some_inj in h1. subst.
        rewrite if_same in h2.
        cbn in h2. apply some_inj in h2. subst.
        cbn. rewrite if_same. exists []. intuition auto.
      + destruct b.
        * cbn in h2. destruct f eqn:e1. 2: discriminate.
          destruct (monad_map _ (mask_filter m2 _)) eqn:e2. 2: discriminate.
          apply some_inj in h2. subst.
          cbn. rewrite e1.
          specialize ih with (1 := hm').
          specialize ih with (1 := h1) (2 := e2).
          destruct ih as [l' [hp e]].
          rewrite e.
          eexists. split. 2: reflexivity.
          etransitivity.
          1: symmetry.
          1: eapply Permutation_middle.
          constructor. assumption.
        * cbn.
          specialize ih with (1 := hm').
          specialize ih with (1 := h1) (2 := h2).
          destruct ih as [l' [hp e]].
          rewrite e.
          eexists. split. 2: reflexivity.
          assumption.
  Qed.

  Lemma lin_merge_permutation :
    ∀ n l l' m,
      PCUICPattern.monad_fold_right lin_merge l (linear_mask_init n) = Some m →
      Permutation l l' →
      PCUICPattern.monad_fold_right lin_merge l' (linear_mask_init n) = Some m.
  Proof.
    intros n l l' m hm hp.
    induction hp in m, hm |- *.
    - assumption.
    - cbn in hm. destruct PCUICPattern.monad_fold_right eqn:e1. 2: discriminate.
      specialize IHhp with (1 := eq_refl).
      cbn. rewrite IHhp. assumption.
    - cbn in hm. destruct PCUICPattern.monad_fold_right eqn:e1. 2: discriminate.
      destruct lin_merge eqn:e2. 2: discriminate.
      cbn. rewrite e1.
      pose proof (lin_merge_assoc _ _ _ _ _ e2 hm) as h.
      destruct h as [m' [e3 e4]]. rewrite e3. assumption.
    - eapply IHhp2. eapply IHhp1. assumption.
  Qed.

  Lemma pattern_list_mask_filter_lin_merge :
    ∀ n m1 m2 m m1' m2' m' σ,
      lin_merge m1 m2 = Some m →
      lin_merge m1' m2' = Some m' →
      pattern_list_mask n (mask_filter m1 σ) = Some m1' →
      pattern_list_mask n (mask_filter m2 σ) = Some m2' →
      pattern_list_mask n (mask_filter m σ) = Some m'.
  Proof.
    intros n m1 m2 m m1' m2' m' σ hm hm' h1 h2.
    unfold pattern_list_mask in *.
    destruct monad_map eqn:e1. 2: discriminate.
    destruct (monad_map _ (mask_filter m2 _)) eqn:e2. 2: discriminate.
    cbn in h1. cbn in h2.
    eapply option_map_mask_filter_lin_merge in hm as h. 2,3: eauto.
    destruct h as [l' [pm e]].
    rewrite e. cbn.
    eapply lin_merge_permutation. 2: eauto.
    eapply lin_merge_app. all: eauto.
  Qed.

  Lemma pattern_list_mask_lin_set :
    ∀ x m1 m2 σ t m3 m4 n m',
      lin_set x m1 = Some m2 →
      nth_error σ x = Some t →
      pattern_mask n t = Some m3 →
      pattern_list_mask n (mask_filter m1 σ) = Some m4 →
      lin_merge m4 m3 = Some m' →
      pattern_list_mask n (mask_filter m2 σ) = Some m'.
  Proof.
    intros x m1 m2 σ t m3 m4 n m' h1 h2 h3 h4 h5.
    induction m1 as [| b m1 ih]
    in x, m2, h1, σ, t, h2, n, m3, h3, m4, h4, m', h5 |- *.
    - destruct x. all: discriminate.
    - destruct x.
      + cbn in h1. destruct b. 1: discriminate.
        apply some_inj in h1. subst.
        destruct σ. 1: discriminate.
        cbn in h2. apply some_inj in h2. subst.
        cbn [ mask_filter ] in h4.
        cbn [ mask_filter ]. rewrite pattern_list_mask_cons.
        rewrite h3. rewrite h4. cbn. assumption.
      + cbn in h1. destruct lin_set eqn:e1. 2: discriminate.
        apply some_inj in h1. subst.
        destruct σ. 1: discriminate.
        cbn in h2.
        destruct b.
        * cbn [ mask_filter ] in h4. rewrite pattern_list_mask_cons in h4.
          move h4 at top. destruct pattern_mask eqn:e2. 2: discriminate.
          destruct pattern_list_mask eqn:e3. 2: discriminate.
          cbn in h4.
          cbn [ mask_filter ]. rewrite pattern_list_mask_cons.
          rewrite e2.
          eapply lin_merge_assoc in h5 as h. 2: eauto.
          destruct h as [m5 [h6 h7]].
          erewrite ih. 2-6: eauto.
          cbn. assumption.
        * cbn [ mask_filter ] in h4. cbn [ mask_filter ].
          eapply ih. all: eauto.
  Qed.

  (* This gives something much weaker but sometimes sufficient *)
  Lemma pattern_app_inv :
    ∀ n u v,
      pattern n (tApp u v) →
      pattern n u ×
      pattern n v.
  Proof.
    intros n u v h.
    inversion h.
    destruct args as [| x args _] using list_rect_rev. 1: discriminate.
    rewrite <- mkApps_nested in H0. cbn in H0. inversion H0. subst.
    apply All_app in X as [? hv]. inversion hv. subst.
    intuition auto.
    constructor. auto.
  Qed.

  Lemma linear_pattern_mask :
    ∀ σ p m m' n,
      pattern #|σ| p →
      pattern n (subst0 σ p) →
      pattern_mask #|σ| p = Some m →
      pattern_mask n (subst0 σ p) = Some m' →
      All_mask (pattern n) m σ ×
      pattern_list_mask n (mask_filter m σ) = Some m'.
  Proof.
    intros σ p m m' n hp1 hp2 hm1 hm2.
    induction p in σ, n, hp1, hp2, m, hm1, m', hm2 |- *.
    all: try discriminate.
    - inversion hp1. 2: solve_discr.
      subst.
      cbn in hm1.
      cbn in hp2, hm2. destruct nth_error eqn:e1.
      2:{ apply nth_error_None in e1. lia. }
      rewrite lift0_id in hp2. rewrite lift0_id in hm2.
      replace (n0 - 0) with n0 in e1 by lia.
      split.
      + eapply All_mask_lin_set. all: eauto.
        apply All_mask_linear_mask_init. reflexivity.
      + eapply pattern_list_mask_lin_set. all: eauto.
        2: eapply lin_merge_linear_mask_init.
        rewrite mask_filter_linear_mask_init.
        cbn. f_equal. f_equal. apply pattern_mask_length in hm2. auto.
    - cbn in hm1. destruct pattern_mask eqn:e1. 2: discriminate.
      move hm1 at top.
      destruct pattern_mask eqn:e2. 2: discriminate.
      cbn in hm2. move hm2 at top.
      destruct pattern_mask eqn:e3. 2: discriminate.
      move hm2 at top.
      destruct pattern_mask eqn:e4. 2: discriminate.
      cbn in hp2. apply pattern_app_inv in hp1 as hp1'.
      destruct hp1' as [].
      apply pattern_app_inv in hp2 as hp2'. destruct hp2' as [].
      specialize IHp1 with (3 := e1) (4 := e3).
      repeat forward IHp1 by auto. destruct IHp1.
      specialize IHp2 with (3 := e2) (4 := e4).
      repeat forward IHp2 by auto. destruct IHp2.
      split.
      + eapply All_mask_lin_merge. all: eauto.
      + eapply pattern_list_mask_filter_lin_merge. all: eauto.
    - cbn in hm1. apply some_inj in hm1. subst.
      cbn in hm2. apply some_inj in hm2. subst.
      split.
      + apply All_mask_linear_mask_init. reflexivity.
      + rewrite mask_filter_linear_mask_init. cbn. reflexivity.
  Qed.

  Lemma linear_elim_mask :
    ∀ σ e n m m',
      elim_pattern #|σ| e →
      elim_pattern n (subst_elim σ 0 e) →
      elim_mask #|σ| e = Some m →
      elim_mask n (subst_elim σ 0 e) = Some m' →
      All_mask (pattern n) m σ ×
      pattern_list_mask n (mask_filter m σ) = Some m'.
  Proof.
    intros σ e n m m' hp1 hp2 hm1 hm2.
    induction hp1 as [| indn p brs hp hbrs |] in n, hp2, m, hm1, m', hm2 |- *.
    - cbn in hp2, hm1, hm2. inversion hp2. subst.
      eapply linear_pattern_mask. all: eauto.
    - cbn in hm1, hp2, hm2.
      destruct pattern_mask eqn:e1. 2: discriminate.
      destruct monad_map as [l2|] eqn:e2. 2: discriminate.
      destruct PCUICPattern.monad_fold_right as [l3|] eqn:e3. 2: discriminate.
      move hm2 at top.
      destruct pattern_mask eqn:e4. 2: discriminate.
      destruct monad_map as [l5|] eqn:e5. 2: discriminate.
      destruct PCUICPattern.monad_fold_right as [l6|] eqn:e6. 2: discriminate.
      inversion hp2. subst.
      eapply linear_pattern_mask in e1 as h1. 2-4: eauto.
      destruct h1.
      cut (
        All_mask (pattern n) l3 σ ×
        pattern_list_mask n (mask_filter l3 σ) = Some l6
      ).
      { intros []. split.
        - eapply All_mask_lin_merge. all: eauto.
        - eapply pattern_list_mask_filter_lin_merge. all: eauto.
      }
      match goal with
      | h : All _ (map _ _) |- _ =>
        rename h into hbrs'
      end.
      clear - e2 e3 e5 e6 hbrs hbrs'.
      apply All_map_inv in hbrs'.
      eapply All_prod in hbrs. 2: eauto.
      cbn in hbrs. clear hbrs'.
      induction hbrs as [| [] brs [] hbrs ih]
      in l5, e5, l6, e6, l2, e2, l3, e3 |- *.
      + cbn in e2. apply some_inj in e2. subst.
        cbn in e5. apply some_inj in e5. subst.
        cbn in e3. apply some_inj in e3. subst.
        cbn in e6. apply some_inj in e6. subst.
        split.
        * apply All_mask_linear_mask_init. reflexivity.
        * rewrite mask_filter_linear_mask_init. cbn. reflexivity.
      + cbn - [pattern_list_mask] in *.
        destruct pattern_mask eqn:e1. 2: discriminate.
        destruct monad_map eqn:e4. 2: discriminate.
        apply some_inj in e5. subst.
        move e2 at top.
        destruct pattern_mask eqn:e5. 2: discriminate.
        destruct monad_map eqn:e7. 2: discriminate.
        apply some_inj in e2. subst.
        cbn in e3. cbn in e6.
        destruct PCUICPattern.monad_fold_right eqn:e2. 2: discriminate.
        move e3 at top.
        destruct PCUICPattern.monad_fold_right eqn:e8. 2: discriminate.
        specialize ih with (1 := eq_refl) (2 := e2) (3 := eq_refl) (4 := e8).
        destruct ih.
        eapply linear_pattern_mask in e1 as h. 2-4: eauto.
        destruct h.
        split.
        * eapply All_mask_lin_merge. all: eauto.
        * eapply pattern_list_mask_filter_lin_merge. all: eauto.
    - cbn in hm1, hp2, hm2.
      apply some_inj in hm1. apply some_inj in hm2. subst.
      split.
      + apply All_mask_linear_mask_init. reflexivity.
      + rewrite mask_filter_linear_mask_init. cbn. reflexivity.
  Qed.

  Lemma linear_linear_mask_pattern :
    ∀ l σ n m1 m2,
      All (elim_pattern #|σ|) l →
      linear_mask #|σ| l = Some m1 →
      All (elim_pattern n) (map (subst_elim σ 0) l) →
      linear_mask n (map (subst_elim σ 0) l) = Some m2 →
      All_mask (pattern n) m1 σ ×
      pattern_list_mask n (mask_filter m1 σ) = Some m2.
  Proof.
    intros l σ n m1 m2 p1 hm1 p2 hm2.
    induction p1 in m1, hm1, p2, m2, hm2 |- *.
    - cbn in hm1. apply some_inj in hm1. subst.
      cbn in hm2. rewrite mask_filter_linear_mask_init.
      cbn. intuition auto.
      apply All_mask_linear_mask_init. reflexivity.
    - rewrite linear_mask_cons in hm1.
      cbn - [linear_mask] in hm2. rewrite linear_mask_cons in hm2.
      destruct elim_mask eqn:em1. 2: discriminate.
      destruct (elim_mask _ (subst_elim _ _ _)) eqn:em2. 2: discriminate.
      destruct linear_mask eqn:lm1. 2: discriminate.
      destruct (linear_mask _ (map _ _)) eqn:lm2. 2: discriminate.
      cbn in hm1. cbn in hm2.
      cbn in p2. apply All_cons_inv in p2 as [ph p2].
      specialize IHp1 with (1 := eq_refl) (3 := eq_refl).
      forward IHp1 by auto.
      destruct IHp1 as [hp hm].
      eapply linear_elim_mask in em2 as h. 2-4: eauto.
      destruct h.
      split.
      + eapply All_mask_lin_merge. all: eauto.
      + eapply pattern_list_mask_filter_lin_merge. all: eauto.
  Qed.

  Lemma linear_linear_pattern :
    ∀ l σ n,
      All (elim_pattern #|σ|) l →
      linear #|σ| l →
      All (elim_pattern n) (map (subst_elim σ 0) l) →
      linear n (map (subst_elim σ 0) l) →
      All (pattern n) σ × pattern_list_linear n σ.
  Proof.
    intros l σ n pl ll pm lm.
    unfold linear in *.
    destruct linear_mask eqn:e1. 2: discriminate.
    destruct (linear_mask _ (map _ _)) eqn:e2. 2: discriminate.
    eapply linear_linear_mask_pattern in e2 as h. 2-4: eauto.
    destruct h. split.
    - eapply All_mask_true_All. all: eauto.
    - unfold pattern_list_linear.
      erewrite mask_filter_all_true in e.
      2: auto.
      2:{ eapply linear_mask_length. eauto. }
      rewrite e. auto.
  Qed.

  Lemma match_lhs_pattern_subst :
    ∀ npat npat' k n l l' ui α,
      All (elim_pattern npat) l →
      linear npat l →
      All (elim_pattern npat') l' →
      linear npat' l' →
      match_lhs npat k n l (mkElims (tSymb k n ui) l') = Some (ui, α) →
      All (pattern npat') α × pattern_list_linear npat' α.
  Proof.
    intros npat npat' k n l l' ui α hel hll hel' hll' e.
    eapply match_lhs_sound in e as et. 2: auto.
    rewrite mkElims_subst in et. cbn in et.
    apply (f_equal decompose_elims) in et.
    rewrite !mkElims_decompose_elims in et. cbn in et.
    apply (f_equal snd) in et. cbn in et. subst.
    eapply match_lhs_subst_length in e as αl. subst.
    eapply linear_linear_pattern. all: eauto.
  Qed.

  Lemma first_match_pattern_subst :
    ∀ k r k' n' ui' el ui σ rd npat,
      All (elim_pattern npat) el →
      linear npat el →
      lookup_env Σ k = Some (RewriteDecl rd) →
      let l := all_rewrite_rules rd in
      first_match k l (mkElims (tSymb k' n' ui') el) = Some (ui, σ, r) →
      All (pattern npat) σ × pattern_list_linear npat σ.
  Proof.
    intros k r k' n' ui' el ui σ rd npat hel hll hk l e.
    apply all_rewrite_rules_on_rewrite_rule in hk as hrd.
    eapply first_match_rule_list in e as hr. destruct hr as [n hr].
    eapply All_nth_error in hr. 2: eauto. clear n.
    destruct hr as [T lT rT hh ll he hΔ].
    rewrite map_length in hh.
    eapply first_match_lookup_sound with (extra := None) in e as h. 2: eauto.
    2: exact I.
    2:{ unfold lookup_rewrite_decl. unfold lookup_rd. rewrite hk. reflexivity. }
    unfold lhs in h. rewrite !mkElims_subst in h. cbn in h.
    eapply first_match_subst_length in e as σl.
    destruct (Nat.leb_spec0 #|σ| (#|pat_context r| + head r)). 2: lia.
    replace (#|pat_context r| + head r - #|σ|) with r.(head) in h by lia.
    unfold symbols_subst at 1 in h.
    destruct nth_error eqn:e1.
    2:{
      apply nth_error_None in e1. rewrite list_make_length in e1. lia.
    }
    eapply list_make_nth_error in e1. subst.
    cbn in h.
    apply (f_equal decompose_elims) in h.
    rewrite !mkElims_decompose_elims in h. cbn in h.
    inversion h. subst. clear h.
    (* eapply All_impl in he as hc.
    2: eapply elim_pattern_closedn. *)
    apply All_map_inv in hel. apply All_map_inv in hel.
    assert (hel' :
      All (fun e =>
        elim_pattern npat (subst_elim σ 0 e)
      ) r.(elims)
    ).
    { eapply All_prod in hel. 2: exact he.
      eapply All_impl. 1: exact hel.
      cbn. intros x [? e0].
      rewrite subst_elim_symbols_subst in e0.
      1:{ rewrite σl. assumption. }
      assumption.
    }
    clear hel. rename hel' into hel.
    rewrite subst_elims_symbols_subst in hll.
    { rewrite σl. auto. }
    rewrite <- σl in ll.
    eapply first_match_subst_length in e. rewrite <- e in he.
    clear - cf wfΣ ll hel he hll.
    eapply linear_linear_pattern. all: eauto.
    apply All_map. auto.
  Qed.

  (* Lemma pattern_subst_pred1 :
    ∀ τ p Γ Δ t,
      pattern #|τ| p →
      pred1 Σ Γ Δ (subst0 τ p) t →
      ∑ τ',
        t = subst0 τ' p ×
        All2 (fun x y => pred1 Σ Γ Δ x y) τ τ'.
  Admitted. *)

  (* Another version of pattern_reduct *)
  Lemma pattern_reduct_alt :
    ∀ Γ Γ' τ p t m,
      pred1 Σ Γ Γ' (subst0 τ p) t →
      pattern #|τ| p →
      pattern_mask #|τ| p = Some m →
      ∑ τ',
        All2_mask_subst (pred1 Σ Γ Γ') m τ τ' ×
        (∀ τ'',
          subs_complete τ' τ'' →
          t = subst0 τ'' p).
  Proof.
    intros Γ Γ' τ p t m h hp hm.
    induction p in t, τ, h, hp, m, hm |- *.
    all: try solve [ discriminate ].
    - inversion hp. 2:solve_discr.
      subst.
      cbn in h. replace (n - 0) with n in h by lia.
      destruct nth_error eqn:e1.
      2:{ apply nth_error_None in e1. lia. }
      rewrite lift0_id in h.
      cbn in hm.
      eexists. split.
      + eapply All2_mask_subst_lin_set. all: eauto.
        * apply subs_add_empty. eassumption.
        * eapply All2_mask_subst_linear_mask_init. reflexivity.
      + intros θ hθ. cbn.
        replace (n - 0) with n by lia.
        apply subs_complete_spec in hθ as hh. destruct hh as [? hθ'].
        erewrite hθ'.
        * rewrite lift0_id. reflexivity.
        * rewrite nth_error_app_ge.
          { rewrite list_init_length. auto. }
          rewrite list_init_length.
          replace (n - n) with 0 by lia.
          cbn. reflexivity.
    - match type of h with
      | pred1 _ _ _ ?x _ =>
        remember x as u eqn:e
      end.
      cbn in e.
      destruct h.
      all: try discriminate.
      + inversion e. subst.
        inversion hp.
        destruct args as [| ? ? _] using list_rect_rev. 1: discriminate.
        rewrite <- mkApps_nested in H1. cbn in H1. inversion H1.
        subst. rewrite subst_mkApps in e. cbn in e.
        inversion e.
        solve_discr.
      + inversion e.
        inversion hp.
        destruct args as [| ? ? _] using list_rect_rev. 1: discriminate.
        rewrite <- mkApps_nested in H1. cbn in H1. inversion H1.
        subst. rewrite subst_mkApps in e. cbn in e.
        destruct args0 as [| ? ? _] using list_rect_rev. 1: discriminate.
        rewrite <- mkApps_nested in e. cbn in e. inversion e.
        solve_discr.
      + match type of e with
        | ?l = tApp (subst0 ?τ ?p1) (subst0 _ ?p2) =>
          change (l = subst0 τ (tApp p1 p2)) in e
        end.
        apply (f_equal isElimSymb) in e.
        inversion hp. rewrite <- H0 in e.
        rewrite subst_mkApps in e. cbn in e.
        rewrite isElimSymb_mkApps in e. cbn in e.
        rewrite isElimSymb_subst in e.
        { apply untyped_subslet_length in u.
          rewrite subst_context_length in u. rewrite u.
          eapply isElimSymb_lhs.
          eapply declared_symbol_head in d. all: eauto.
        }
        discriminate.
      + match type of e with
        | ?l = tApp (subst0 ?τ ?p1) (subst0 _ ?p2) =>
          change (l = subst0 τ (tApp p1 p2)) in e
        end.
        apply (f_equal isElimSymb) in e.
        inversion hp. rewrite <- H0 in e.
        rewrite subst_mkApps in e. cbn in e.
        rewrite isElimSymb_mkApps in e. cbn in e.
        rewrite isElimSymb_subst in e.
        { apply untyped_subslet_length in u.
          rewrite subst_context_length in u. rewrite u.
          eapply isElimSymb_lhs.
          eapply declared_symbol_par_head in d. all: eauto.
        }
        discriminate.
      + inversion e. subst. clear e.
        match goal with
        | h : pred1 _ _ _ (subst0 _ p1) ?x |- _ =>
          rename x into u ;
          rename h into hu
        end.
        match goal with
        | h : pred1 _ _ _ (subst0 _ p2) ?x |- _ =>
          rename x into v ;
          rename h into hv
        end.
        cbn in hm.
        destruct pattern_mask eqn:e1. 2: discriminate.
        destruct (pattern_mask _ p2) eqn:e2. 2: discriminate.
        apply pattern_app_inv in hp as [hp1 hp2].
        specialize IHp1 with (2 := hp1) (3 := e1).
        specialize IHp2 with (2 := hp2) (3 := e2).
        specialize IHp1 with (1 := hu).
        specialize IHp2 with (1 := hv).
        destruct IHp1 as [τ1 [? h1]].
        destruct IHp2 as [τ2 [? h2]].
        eapply All2_mask_subst_lin_merge in hm as h. 2-3: eauto.
        destruct h as [τ' []].
        eexists. split.
        * eassumption.
        * intros τ'' hc.
          eapply subs_merge_complete in hc as h'. 2: eauto.
          destruct h'.
          cbn. erewrite h1. 2: eauto.
          erewrite h2. 2: eauto.
          reflexivity.
      + subst. discriminate.
    - cbn in h.
      match type of h with
      | pred1 _ _ _ ?x _ =>
        remember x as u eqn:e
      end.
      destruct h.
      all: try discriminate.
      all: try solve [ solve_discr ].
      + apply (f_equal isElimSymb) in e. cbn in e.
        rewrite isElimSymb_subst in e.
        { apply untyped_subslet_length in u.
          rewrite subst_context_length in u. rewrite u.
          eapply isElimSymb_lhs.
          eapply declared_symbol_head in d. all: eauto.
        }
        discriminate.
      + apply (f_equal isElimSymb) in e. cbn in e.
        rewrite isElimSymb_subst in e.
        { apply untyped_subslet_length in u.
          rewrite subst_context_length in u. rewrite u.
          eapply isElimSymb_lhs.
          eapply declared_symbol_par_head in d. all: eauto.
        }
        discriminate.
      + subst. cbn in *. apply some_inj in hm. subst.
        eexists. split.
        * eapply All2_mask_subst_linear_mask_init. reflexivity.
        * intros θ' hθ'. reflexivity.
  Qed.

  Lemma All2_mask_subst_length :
    ∀ P m σ θ,
      All2_mask_subst P m σ θ →
      #|m| = #|σ| ∧ #|σ| = #|θ|.
  Proof.
    intros P m σ θ h.
    induction h. all: cbn in *. all: intuition auto.
  Qed.

  Lemma subs_complete_mask_eq :
    ∀ m σ θ,
      masks m σ →
      subs_complete σ θ →
      All2_mask_subst eq m θ σ.
  Proof.
    intros m σ θ hm hc.
    induction hm in θ, hc |- *.
    - assert (θ = []).
      { inversion hc. reflexivity. }
      subst.
      constructor.
    - destruct θ. 1: exfalso ; inversion hc.
      constructor.
      + inversion hc. auto.
      + eapply IHhm. inversion hc. auto.
    - destruct θ. 1: exfalso ; inversion hc.
      constructor.
      eapply IHhm. inversion hc. auto.
  Qed.

  Lemma All2_mask_subst_masks :
    ∀ P m σ θ,
      All2_mask_subst P m σ θ →
      masks m θ.
  Proof.
    intros P m σ θ h.
    induction h.
    - constructor.
    - constructor. assumption.
    - constructor. assumption.
  Qed.

  Lemma All2_mask_subst_eq_replace_left :
    ∀ P m σ τ θ,
      All2_mask_subst P m σ τ →
      All2_mask eq m θ σ →
      All2_mask_subst P m θ τ.
  Proof.
    intros P m σ τ θ h e.
    induction h in θ, e |- *.
    - inversion e. constructor.
    - inversion e. subst. constructor.
      + auto.
      + eapply IHh. assumption.
    - inversion e. subst. constructor.
      eapply IHh. assumption.
  Qed.

  Lemma All2_mask_subst_sym_eq :
    ∀ P m σ τ σ' τ',
      All2_mask_subst P m σ τ →
      All2_mask_subst eq m σ σ' →
      All2_mask_subst eq m τ' τ →
      All2_mask_subst (fun x y => P y x) m τ' σ'.
  Proof.
    intros P m σ τ σ' τ' h e1 e2.
    induction h in σ', τ', e1, e2 |- *.
    - inversion e1. inversion e2. constructor.
    - inversion e1. inversion e2. subst. constructor.
      + auto.
      + eapply IHh. all: auto.
    - inversion e1. inversion e2. subst. constructor.
      eapply IHh. all: auto.
  Qed.

  Lemma All2_mask_subst_left_map_inv :
    ∀ P m σ θ f,
      All2_mask_subst P m (map f σ) θ →
      All2_mask_subst (fun x y => P (f x) y) m σ θ.
  Proof.
    intros P m σ θ f h.
    remember (map f σ) as τ eqn:e.
    induction h in σ, e |- *.
    - destruct σ. 2: discriminate.
      constructor.
    - destruct σ. 1: discriminate.
      inversion e.
      constructor.
      + subst. auto.
      + eapply IHh. auto.
    - destruct σ. 1: discriminate.
      inversion e.
      constructor.
      eapply IHh. auto.
  Qed.

  Lemma All2_mask_subst_prod :
    ∀ P Q m σ θ,
      All2_mask_subst P m σ θ →
      All2_mask_subst Q m σ θ →
      All2_mask_subst (fun x y => P x y × Q x y) m σ θ.
  Proof.
    intros P Q m σ θ h1 h2.
    induction h1 in h2 |- *.
    - constructor.
    - inversion h2. constructor.
      + split. all: auto.
      + eapply IHh1. auto.
    - inversion h2. constructor.
      eapply IHh1. auto.
  Qed.

  Lemma subst_pattern_factorisation_mask :
    ∀ Γ Γ' τ p t m,
      pred1 Σ Γ Γ' (subst0 τ p) t →
      pred1 Σ Γ' (rho_ctx Σ None Γ)
        t (rho Σ None (rho_ctx Σ None Γ) (subst0 τ p)) →
      pattern #|τ| p →
      pattern_mask #|τ| p = Some m →
      ∑ τ',
        (∀ τ'',
          subs_complete τ' τ'' →
          t = subst0 τ'' p) ×
        All2_mask_subst (λ x y,
          pred1 Σ Γ Γ' x y ×
          pred1 Σ Γ' (rho_ctx Σ None Γ) y (rho Σ None (rho_ctx Σ None Γ) x)
        ) m τ τ'.
  Proof.
    intros Γ Γ' τ p t m h1 h2 hp hm.
    rewrite rho_subst_pattern in h2. 1: auto.
    eapply pattern_reduct_alt in h1 as h1'. 2,3: eauto.
    destruct h1' as [τ1 [e1 c1]].
    exists τ1. split. 1: auto.
    pose proof (subs_flatten_default_complete τ1) as hc.
    specialize c1 with (1 := hc) as e.
    rewrite e in h2.
    eapply subs_complete_length in hc as hcl.
    eapply All2_mask_subst_length in e1 as l.
    destruct l as [l1 l2].
    eapply pattern_reduct_alt in h2 as h2'.
    2,3: rewrite <- hcl.
    2,3: rewrite <- l2.
    2,3: eauto.
    destruct h2' as [τ2 [e2 c2]].
    pose proof (subs_flatten_default_complete τ2) as hc2.
    specialize c2 with (1 := hc2) as e'.
    eapply pattern_mask_subst_inj in e'. 2-5: eauto.
    2:{ rewrite map_length. reflexivity. }
    2:{
      apply subs_complete_length in hc2.
      apply All2_mask_subst_length in e2. destruct e2 as [el1 el2].
      lia.
    }
    eapply All2_mask_subst_masks in e2 as hm2.
    eapply subs_complete_mask_eq in hc2 as e3. 2: eauto.
    eapply All2_mask_subst_eq_replace_left in e3. 2: eauto.
    eapply All2_mask_subst_masks in e1 as hm1.
    eapply subs_complete_mask_eq in hc as e4. 2: eauto.
    eapply All2_mask_subst_sym_eq in e2. 2,3: eauto.
    apply All2_mask_subst_left_map_inv in e2.
    eapply All2_mask_subst_prod. all: eauto.
  Qed.

  Lemma subst_factorisation_mask :
    ∀ Γ Γ' τ α σ m,
      All2 (λ x y,
        pred1 Σ Γ Γ' x y ×
        pred1 Σ Γ' (rho_ctx Σ None Γ) y (rho Σ None (rho_ctx Σ None Γ) x)
      ) (map (subst0 τ) α) σ →
      All (pattern #|τ|) α →
      pattern_list_mask #|τ| α = Some m →
      ∑ τ',
        (∀ τ'',
          subs_complete τ' τ'' →
          σ = map (subst0 τ'') α) ×
        All2_mask_subst (λ x y,
          pred1 Σ Γ Γ' x y ×
          pred1 Σ Γ' (rho_ctx Σ None Γ) y (rho Σ None (rho_ctx Σ None Γ) x)
        ) m τ τ'.
  Proof.
    intros Γ Γ' τ α σ m h pα lα.
    apply All2_map_inv_left in h.
    eapply All2_All_mix_left in h. 2: eauto.
    clear pα.
    induction h as [| u v α σ [? [? ?]] h ih ] in m, lα |- *.
    - cbn in lα. apply some_inj in lα. subst.
      cbn.
      eexists. split.
      + intros. reflexivity.
      + eapply All2_mask_subst_linear_mask_init. reflexivity.
    - rewrite pattern_list_mask_cons in lα.
      destruct pattern_mask eqn:e1. 2: discriminate.
      destruct pattern_list_mask eqn:e2. 2: discriminate.
      cbn in lα.
      specialize ih with (1 := eq_refl).
      destruct ih as [τ1 [h1 h2]].
      cbn.
      eapply subst_pattern_factorisation_mask in e1 as h3. 2-4: eauto.
      destruct h3 as [τ2 [h3 h4]].
      eapply All2_mask_subst_lin_merge in lα as h'. 2-3: eauto.
      destruct h' as [τ' [? ?]].
      exists τ'. split.
      + intros τ'' hc.
        eapply subs_merge_complete in hc as h'. 2: eauto.
        destruct h'.
        f_equal.
        * eapply h3. assumption.
        * eapply h1. assumption.
      + assumption.
  Qed.

  Lemma subst_factorisation :
    ∀ Γ Γ' τ α σ,
      All2 (λ x y,
        pred1 Σ Γ Γ' x y ×
        pred1 Σ Γ' (rho_ctx Σ None Γ) y (rho Σ None (rho_ctx Σ None Γ) x)
      ) (map (subst0 τ) α) σ →
      All (pattern #|τ|) α →
      pattern_list_linear #|τ| α →
      ∑ τ',
        σ = map (subst0 τ') α ×
        All2 (λ x y,
          pred1 Σ Γ Γ' x y ×
          pred1 Σ Γ' (rho_ctx Σ None Γ) y (rho Σ None (rho_ctx Σ None Γ) x)
        ) τ τ'.
  Proof.
    intros Γ Γ' τ α σ h pα lα.
    unfold pattern_list_linear in lα.
    destruct pattern_list_mask as [m|] eqn:e. 2: discriminate.
    eapply subst_factorisation_mask in e as h'. 2-3: eauto.
    destruct h' as [τ' [h1 h2]].
    eapply All2_mask_subst_all in h2. 2: auto.
    destruct h2 as [τ'' [e2 h2]].
    exists τ''. split.
    - eapply h1. apply map_option_out_subs_complete. assumption.
    - assumption.
  Qed.

  Context (cΣ : confluenv Σ).

  Lemma triangle Γ Δ t u :
    let Pctx := fun (Γ Δ : context) => pred1_ctx Σ Δ (rho_ctx Σ None Γ) in
    pred1 Σ Γ Δ t u ->
    pred1 Σ Δ (rho_ctx Σ None Γ) u (rho Σ None (rho_ctx Σ None Γ) t).
  Proof with solve_discr.
    intros Pctx H. revert Γ Δ t u H.
    refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      subst Pctx; intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [simpl; econstructor; simpl; eauto].

    - simpl. induction X0; simpl; depelim predΓ'; constructor; rewrite ?app_context_nil_l; eauto.
      all:simpl NoConfusion in *; noconf H; noconf H0; auto.

    - simpl.
      rewrite (rho_app_lambda _ _ _ _ _ _ _ _ _ []). 1,2: cbn ; eauto.
      eapply (substitution0_pred1); simpl in *. 1-2: eauto.
      rewrite app_context_nil_l in X0.
      eapply X0.

    - simp rho lhs_viewc. rewrite <- !fold_rho.
      eapply (substitution0_let_pred1); simpl in *. 1-2: eauto.
      rewrite app_context_nil_l in X4.
      eapply X4.

    - simp rho lhs_viewc.
      destruct nth_error eqn:Heq.
      + simpl in X0.
        pose proof Heq. apply nth_error_Some_length in Heq.
        destruct c as [na [?|] ?]; noconf heq_option_map.
        simpl in X0.
        eapply (f_equal (option_map decl_body)) in H.
        eapply nth_error_pred1_ctx_l in H; eauto.
        destruct H. intuition. rewrite a. simp rho.
        rewrite -{1}(firstn_skipn (S i) Γ').
        rewrite -{1}(firstn_skipn (S i) (rho_ctx _ _ Γ)).
        pose proof (All2_local_env_length X0).
        assert (S i = #|firstn (S i) Γ'|).
        { rewrite !firstn_length_le; try lia. }
        assert (S i = #|firstn (S i) (rho_ctx Σ None Γ)|).
        { rewrite !firstn_length_le; try lia. }
        rewrite {5}H0 {6}H1.
        eapply weakening_pred1_pred1; eauto.
        eapply All2_local_env_over_firstn_skipn. auto.
      + noconf heq_option_map.

    (* - simp rho lhs_viewc.
      destruct nth_error eqn:Heq. 2: discriminate.
      destruct c as [na [?|] ?]. all: noconf heq_option_map.
      simpl in X0.
      (* I see no way out here.
        Γ ⇒ Γ' ⇒ rho Γ
        but here I would need Γ ⇒ rho Γ I think...
      *)
      admit. *)

    - simp rho lhs_viewc. simpl in *.
      destruct option_map eqn:Heq.
      + destruct o.
        * constructor; auto.
        * constructor. auto.
      + constructor. auto.

    - simpl in X0. cbn.
      rewrite rho_app_case.
      { intros [k [rd [[[? ?] ?] [? e]]]].
        cbn in e. eapply first_match_lookup_sound in e as et. 4: eauto.
        2: auto. 2: exact I.
        apply (f_equal elim_kn) in et. cbn in et.
        rewrite elim_kn_mkApps in et. cbn in et.
        apply first_match_subst_length in e as σl.
        rewrite σl in et.
        eapply first_match_rule_list in e as hr. destruct hr as [n ?].
        erewrite elim_kn_lhs in et. 2-5: eauto. 2: exact I.
        discriminate.
      }
      rewrite decompose_app_mkApps; auto.
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec ind ind); try discriminate.
      2:{ congruence. }
      unfold iota_red. eapply pred_mkApps; eauto.
      + eapply pred_snd_nth.
        * red in X2.
          now eapply rho_triangle_All_All2_ind_noeq.
        * auto.
      + eapply All2_skipn. eapply All2_sym.
        rewrite - {1} (map_id args1). eapply All2_map, All2_impl; eauto.
        simpl. intuition.

    - (* Fix reduction *)
      unfold PCUICTyping.unfold_fix in heq_unfold_fix |- *.
      rewrite rho_app_fix. 1,2: cbn ; eauto.
      destruct nth_error eqn:Heq; noconf heq_unfold_fix.
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Hnth Hrel]].
      destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
      rewrite Hnth. simpl.
      destruct args0.
      + depelim X4. unfold is_constructor in heq_is_constructor.
        rewrite nth_error_nil in heq_is_constructor => //.
      + pose proof Hnth.
        eapply All2_nth_error_Some in H; eauto.
        destruct H as [fn' [Hnth' [? ?]]].
        destruct t', d.
        simpl in * |-. noconf Heq. destruct o, p as [[ol ol'] or].
        simpl in * |-. noconf or.
        move: heq_is_constructor.
        revert X4. generalize (t :: args0). simpl.
        clear t args0. intros args0 Hargs isc.
        simpl. rewrite isc.
        eapply pred_mkApps.
        * rewrite rho_ctx_app in Hreleq1.
          rewrite !subst_inst. simpl_pred.
          rewrite /rho_fix_context -fold_fix_context_rho_ctx. 1,2: cbn ; eauto.
          eapply strong_substitutivity; eauto.
          -- apply ctxmap_fix_subst.
          -- rewrite -rho_fix_subst. 1,2: cbn ; eauto.
             rewrite -{1}fix_context_map_fix. 1,2: cbn ; eauto.
             apply ctxmap_fix_subst.
          -- rewrite -rho_fix_subst. 1,2: cbn ; eauto.
             eapply All2_prop2_eq_split in X3.
             apply pred_subst_rho_fix; intuition auto. cbn. auto.
        * eapply All2_sym, All2_map_left, All2_impl; eauto.
          simpl. unfold on_Trel in *.
          intuition eauto.

    - (* Case-CoFix reduction *)
      destruct ip.
      rewrite rho_app_case.
      { intros [k [rd [[[? ?] ?] [? e]]]].
        cbn in e. eapply first_match_lookup_sound in e as et. 2-4: eauto.
        2: exact I.
        apply (f_equal elim_kn) in et. cbn in et.
        rewrite elim_kn_mkApps in et. cbn in et.
        apply first_match_subst_length in e as σl.
        rewrite σl in et.
        eapply first_match_rule_list in e as hr. destruct hr as [? ?].
        erewrite elim_kn_lhs in et. 2-5: eauto. 2: exact I.
        discriminate.
      }
      rewrite decompose_app_mkApps; auto.
      unfold unfold_cofix in heq_unfold_cofix |- *.
      destruct nth_error eqn:Heq; noconf heq_unfold_cofix. simpl.
      eapply All2_prop2_eq_split in X3. intuition.
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Ht' Hrel]]. rewrite Ht'. simpl.
      eapply pred_case.
      + eauto.
      + eapply pred_mkApps.
        * red in Hrel. destruct Hrel.
          rewrite rho_ctx_app in p2.
          rewrite - fold_fix_context_rho_ctx. 1,2: cbn ; eauto.
          set (rhoΓ := rho_ctx _ _ Γ ,,, rho_ctx_over _ _ (rho_ctx _ _ Γ) (fix_context mfix0)) in *.
          rewrite !subst_inst. eapply simpl_pred; try now sigma.
          eapply strong_substitutivity; eauto.
          -- apply ctxmap_cofix_subst.
          -- unfold rhoΓ.
             rewrite -{1}fix_context_map_fix. 1,2: cbn ; eauto.
             rewrite -rho_cofix_subst. 1,2 : cbn ; eauto.
             now eapply ctxmap_cofix_subst.
          -- rewrite -rho_cofix_subst. 1,2: cbn ; eauto.
             now eapply pred_subst_rho_cofix; auto.
        * eapply All2_sym, All2_map_left, All2_impl; eauto.
          simpl. intuition eauto.
      + eapply All2_sym, All2_map_left, All2_impl; eauto.
        simpl. unfold on_Trel in *.
        intuition eauto.

    - (* Proj-Cofix reduction *)
      simpl.
      destruct p as [[ind pars] arg].
      rewrite rho_app_proj.
      { intros [k [rd [[[? ?] ?] [? e]]]].
        cbn in e. eapply first_match_lookup_sound in e as et. 2-4: eauto.
        2: exact I.
        apply (f_equal elim_kn) in et. cbn in et.
        rewrite elim_kn_mkApps in et. cbn in et.
        apply first_match_subst_length in e as σl.
        rewrite σl in et.
        eapply first_match_rule_list in e as hr. destruct hr as [n ?].
        erewrite elim_kn_lhs in et. 2-5: eauto. 2: exact I.
        discriminate.
      }
      rewrite decompose_app_mkApps. 1: auto.
      unfold unfold_cofix in heq_unfold_cofix |- *.
      destruct nth_error eqn:Heq; noconf heq_unfold_cofix.
      eapply All2_nth_error_Some_right in Heq; eauto.
      destruct Heq as [t' [Hnth Hrel]]. destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
      unfold map_fix. rewrite Hnth /=.
      econstructor. eapply pred_mkApps; eauto.
      + rewrite - fold_fix_context_rho_ctx. 1,2: cbn ; eauto.
        rewrite rho_ctx_app in Hreleq1.
        eapply substitution_pred1; eauto.
        eapply wf_rho_cofix_subst; eauto. 1: cbn ; eauto.
        now eapply All2_length in X3.
      + eapply All2_sym, All2_map_left, All2_impl; eauto; simpl; intuition eauto.

    - simp rho. destruct lhs_viewc.
      + simp rho.
        eapply first_match_match_rule in e0 as h.
        destruct h as [? [hr h]].
        unfold all_rewrite_rules in hr.
        eapply first_match_lookup_sound in e0 as hs. 2,4: eauto. 2: exact I.
        rewrite hs.
        eapply lookup_rewrite_decl_lookup_env in e as e'.
        eapply rule_linear in hr as hl. 2: eauto.
        unfold lhs in hs. rewrite !mkElims_subst in hs. cbn in hs.
        eapply first_match_subst_length in e0 as σl.
        destruct (Nat.leb_spec0 #|σ| (#|pat_context r| + head r)). 2: lia.
        replace (#|pat_context r| + head r - #|σ|) with r.(head) in hs by lia.
        destruct (nth_error _ r.(head)) eqn:e2.
        2:{
          eapply nth_error_None in e2. rewrite symbols_subst_length in e2.
          eapply rule_head in hr as hh. 2: eauto.
          lia.
        }
        unfold symbols_subst in e2.
        eapply list_make_nth_error in e2. subst.
        cbn in hs. apply (f_equal decompose_elims) in hs. cbn in hs.
        rewrite mkElims_decompose_elims in hs. cbn in hs.
        apply (f_equal snd) in hs. cbn in hs.
        symmetry in hs. apply map_eq_nil in hs. apply map_eq_nil in hs.
        rewrite hs in hl. cbn in hl.
        destruct #|pat_context r| eqn:e1.
        2:{ cbn in hl. discriminate. }
        destruct σ. 2: discriminate.
        cbn - [match_lhs] in *.
        eapply nth_error_app_dec in hr as [[? hr] | [? hr]].
        * eapply pred_par_rewrite_rule. all: eauto.
          destruct pat_context. 2: discriminate.
          constructor.
        * eapply pred_rewrite_rule. all: eauto.
          destruct pat_context. 2: discriminate.
          constructor.
      + cbn. eapply pred1_refl_gen. assumption.

    - simp rho. destruct lhs_viewc eqn:hv.
      2:{
        eapply lhs_viewc_not_lhs in hv. 2,3: cbn ; eauto.
        exfalso. apply hv. cbn.
        unfold declared_symbol in H.
        unfold lookup_rd.
        eexists k, decl. rewrite H.
        assert (hn : ∑ n, nth_error (all_rewrite_rules decl) n = Some r).
        { unfold all_rewrite_rules.
          exists (#|prules decl| + n).
          rewrite nth_error_app_ge. 1: lia.
          rewrite <- heq_nth_error. f_equal. lia.
        }
        destruct hn as [m e].
        assert (h : ∑ x, first_match k (all_rewrite_rules decl) lhs = Some x).
        { eapply match_lhs_first_match. 1: eauto.
          subst lhs.
          eapply match_lhs_rule. all: eauto.
          apply untyped_subslet_length in X2.
          rewrite subst_context_length in X2.
          auto.
        }
        destruct h as [? ?].
        eexists. intuition eauto.
      }
      clear hv.
      simp rho.
      eapply lookup_rewrite_decl_lookup_env in e as e1.
      eapply lookup_env_triangle in e1 as h. 2,3: auto.
      unfold triangle_rules' in h.
      match goal with
      | _ : nth_error (rules ?decl) ?n = Some ?r |- _ =>
        specialize (h r (#|prules decl| + n))
      end.
      eapply lhs_footprint_first_match in e0 as hf. 2: auto.
      destruct hf as [? [l'' [τ' [θ [hf [fm ?]]]]]]. subst.
      pose proof (match_lhs_complete #|pat_context r| k r.(head) ui r.(elims) s)
      as hl.
      eapply lookup_on_global_env in H as hlr. 2: eauto.
      destruct hlr as [Σ' [_ [_ [hlr _]]]].
      eapply All_nth_error in hlr. 2: eauto.
      destruct hlr as [_ _ _ hh ll hep hac]. clear Σ'.
      forward hl by auto. forward hl by auto.
      match goal with
      | u : untyped_subslet _ _ _ |- _ =>
        apply untyped_subslet_length in u as sl
      end.
      rewrite subst_context_length in sl.
      forward hl by auto.
      eapply lhs_footprint_match_lhs in hl as ft. 2: auto.
      destruct ft as [l' [τ [α [fe' [hm ?]]]]].
      lazymatch goal with
      | h1 : lhs_footprint _ = Some ?x, h2 : lhs_footprint lhs = Some ?y
        |- _ =>
        assert (ee : x = y)
      end.
      { apply some_inj. rewrite <- fe'. rewrite <- hf.
        f_equal. subst lhs. f_equal. unfold lhs.
        rewrite mkElims_subst. cbn.
        destruct (Nat.leb_spec0 #|s| (#|pat_context r| + head r)). 2: lia.
        replace (#|pat_context r| + head r - #|s|) with r.(head) by lia.
        destruct (nth_error ss (head r)) eqn:e3.
        2:{
          apply nth_error_None in e3.
          eapply declared_symbol_head in H. 2,3: eauto.
          subst ss. rewrite symbols_subst_length in e3. lia.
        }
        subst ss. unfold symbols_subst in e3.
        apply list_make_nth_error in e3. subst.
        cbn. f_equal. 1: f_equal ; lia.
        symmetry. apply All_map_id. eapply All_impl. 1: eauto.
        intros ? ?. apply subst_elim_symbols_subst. rewrite sl. assumption.
      }
      symmetry in ee. inversion ee. subst. clear ee.
      eapply lhs_footprint_eq in hf as fe.
      rewrite mkElims_subst in fe. cbn in fe.
      unfold lhs in fe.
      rewrite !mkElims_subst in fe. cbn in fe.
      destruct (Nat.leb_spec0 #|map (subst0 τ) α| (#|pat_context r| + head r)).
      2: lia.
      replace (#|pat_context r| + head r - #|map (subst0 τ) α|)
      with r.(head) in fe by lia.
      destruct (nth_error ss (head r)) eqn:e2.
      2:{
        apply nth_error_None in e2.
        eapply declared_symbol_head in H. 2,3: eauto.
        subst ss. rewrite symbols_subst_length in e2. lia.
      }
      subst lhs rhs. cbn.
      unfold declared_symbol in H. rewrite e1 in H.
      symmetry in H. inversion H. subst. clear H.
      match goal with
      | ss' := ?t |- _ =>
        subst ss' ;
        set (ss := t) in *
      end.
      unfold ss in e2. unfold symbols_subst in e2.
      apply list_make_nth_error in e2. subst.
      cbn in fe.
      apply (f_equal decompose_elims) in fe.
      rewrite !mkElims_decompose_elims in fe. cbn in fe.
      apply (f_equal snd) in fe. cbn in fe.
      eapply first_match_lookup_sound in fm as elhs. 2,4: eauto. 2: exact I.
      eapply lhs_footprint_pattern in hf as hpl.
      eapply lhs_footprint_linear in hf as hll.
      set (Δ := map (vass nAnon) (list_init (tRel 0) #|τ|)).
      specialize (h #|τ| (Γ' ,,, Δ) (rho_ctx Σ None Γ ,,, Δ) α ui θ r0).
      forward h.
      { unfold all_rewrite_rules.
        rewrite nth_error_app_ge. 1: lia.
        replace (#|prules rd| + n - #|prules rd|) with n by lia.
        assumption.
      }
      assert (hα : All (pattern #|τ|) α × pattern_list_linear #|τ| α).
      { eapply match_lhs_pattern_subst. 5: eauto. all: eauto. }
      assert (hθ : All (pattern #|τ|) θ × pattern_list_linear #|τ| θ).
      { eapply first_match_pattern_subst in hpl. all: eauto. }
      destruct hα as [hα lα].
      destruct hθ as [hθ lθ].
      forward h by auto.
      forward h.
      { rewrite map_length in sl.
        eapply untyped_subslet_assumption_context. 2: auto.
        eapply rule_assumption_context with (n := #|prules rd| + n). 1: eauto.
        unfold all_rewrite_rules.
        rewrite nth_error_app_ge. 1: lia.
        replace (#|prules rd| + n - #|prules rd|) with n by lia.
        assumption.
      }
      forward h.
      { rewrite <- fm. f_equal.
        unfold lhs. rewrite !mkElims_subst. cbn.
        rewrite map_length in sl.
        destruct (Nat.leb_spec0 #|α| (#|pat_context r| + head r)). 2: lia.
        replace (#|pat_context r| + head r - #|α|) with r.(head) by lia.
        destruct (nth_error _ r.(head)) eqn:e2.
        2:{
          apply nth_error_None in e2.
          rewrite map_length in hh.
          rewrite symbols_subst_length in e2. lia.
        }
        unfold symbols_subst in e2.
        apply list_make_nth_error in e2. subst.
        cbn. replace (head r + 0) with r.(head) by lia.
        eapply match_lhs_sound in hm as e2. 2: auto.
        rewrite e2. rewrite mkElims_subst. cbn. f_equal. f_equal.
        apply All_map_id. eapply All_impl. 1: eauto.
        intros ? ?. apply subst_elim_symbols_subst. rewrite sl. assumption.
      }
      forward h.
      { clear - X0. cbn in X0. subst Δ.
        induction τ.
        - auto.
        - cbn. constructor. 1: auto.
          cbn. apply pred1_refl_gen. auto.
      }
      rewrite !map_length.
      lazymatch goal with
      | hh : All2 ?P _ _ |- _ =>
        rename hh into hs
      end.
      eapply subst_factorisation in hs as hτ. 2,3: auto.
      destruct hτ as [τ' [? hτ]]. subst.
      eapply substitution_pred1
      with (s := τ') (s' := map (rho Σ None (rho_ctx Σ None Γ)) τ)
      in h. 2: auto.
      2:{
        clear - hτ predΓ' X0. cbn in X0. subst Δ. induction hτ.
        - constructor.
        - cbn. constructor.
          + assumption.
          + eapply pred1_refl_gen.
            clear - r X0.
            induction l.
            * intuition auto.
            * cbn. constructor. 1: auto.
              cbn. apply pred1_refl_gen. auto.
          + intuition auto.
      }
      match goal with
      | ss' := ?t |- _ =>
        subst ss' ;
        set (ss := t) in *
      end.
      rewrite subst_subst_compose in h.
      { rewrite map_length in sl.
        eapply closed_rule_rhs in heq_nth_error. 2,3: eauto.
        eapply closedn_subst with (k := 0).
        - subst ss. unfold symbols_subst.
          generalize (#|symbols rd| - 0). generalize 0 at 2. clear.
          intros i n. induction n in i |- *.
          + reflexivity.
          + cbn. eauto.
        - cbn. subst ss. rewrite symbols_subst_length.
          rewrite sl. replace (#|symbols rd| - 0) with #|symbols rd| by lia.
          assumption.
      }
      rewrite subst_subst_compose in h.
      { eapply first_match_subst_length in e0 as tl.
        rewrite map_length in tl. rewrite tl.
        eapply first_match_rule_list in e0 as [? e0].
        eapply rule_closed_rhs in e0. 2: eauto.
        eapply closedn_subst with (k := 0).
        - subst ss. unfold symbols_subst.
          generalize (#|symbols rd| - 0). generalize 0 at 2. clear.
          intros i n. induction n in i |- *.
          + reflexivity.
          + cbn. eauto.
        - cbn. subst ss. rewrite symbols_subst_length.
          replace (#|symbols rd| - 0) with #|symbols rd| by lia.
          assumption.
      }
      rewrite map_rho_subst_pattern. 1: auto.
      assumption.

    - simp rho. destruct lhs_viewc eqn:hv.
      2:{
        eapply lhs_viewc_not_lhs in hv. 2,3: cbn ; eauto.
        exfalso. apply hv. cbn.
        unfold declared_symbol in H.
        unfold lookup_rd.
        eexists k, decl. rewrite H.
        assert (hn : ∑ n, nth_error (all_rewrite_rules decl) n = Some r).
        { unfold all_rewrite_rules.
          exists n.
          rewrite nth_error_app_lt.
          1:{ apply nth_error_Some_length in heq_nth_error. auto. }
          auto.
        }
        destruct hn as [m e].
        assert (h : ∑ x, first_match k (all_rewrite_rules decl) lhs = Some x).
        { eapply match_lhs_first_match. 1: eauto.
          subst lhs.
          eapply match_lhs_rule. all: eauto.
          apply untyped_subslet_length in X2.
          rewrite subst_context_length in X2.
          auto.
        }
        destruct h as [? ?].
        eexists. intuition eauto.
      }
      clear hv.
      (* Copy of the above case *)
      simp rho.
      eapply lookup_rewrite_decl_lookup_env in e as e1.
      eapply lookup_env_triangle in e1 as h. 2,3: auto.
      unfold triangle_rules' in h.
      match goal with
      | _ : nth_error (prules ?decl) ?n = Some ?r |- _ =>
        specialize (h r n)
      end.
      eapply lhs_footprint_first_match in e0 as hf. 2: auto.
      destruct hf as [? [l'' [τ' [θ [hf [fm ?]]]]]]. subst.
      pose proof (match_lhs_complete #|pat_context r| k r.(head) ui r.(elims) s)
      as hl.
      eapply lookup_on_global_env in H as hlr. 2: eauto.
      destruct hlr as [Σ' [_ [_ [_ [hlr _]]]]].
      eapply All_nth_error in hlr. 2: eauto.
      destruct hlr as [_ _ _ hh ll hep hac]. clear Σ'.
      forward hl by auto. forward hl by auto.
      match goal with
      | u : untyped_subslet _ _ _ |- _ =>
        apply untyped_subslet_length in u as sl
      end.
      rewrite subst_context_length in sl.
      forward hl by auto.
      eapply lhs_footprint_match_lhs in hl as ft. 2: auto.
      destruct ft as [l' [τ [α [fe' [hm ?]]]]].
      lazymatch goal with
      | h1 : lhs_footprint _ = Some ?x, h2 : lhs_footprint lhs = Some ?y
        |- _ =>
        assert (ee : x = y)
      end.
      { apply some_inj. rewrite <- fe'. rewrite <- hf.
        f_equal. subst lhs. f_equal. unfold lhs.
        rewrite mkElims_subst. cbn.
        destruct (Nat.leb_spec0 #|s| (#|pat_context r| + head r)). 2: lia.
        replace (#|pat_context r| + head r - #|s|) with r.(head) by lia.
        destruct (nth_error ss (head r)) eqn:e3.
        2:{
          apply nth_error_None in e3.
          eapply declared_symbol_par_head in H. 2,3: eauto.
          subst ss. rewrite symbols_subst_length in e3. lia.
        }
        subst ss. unfold symbols_subst in e3.
        apply list_make_nth_error in e3. subst.
        cbn. f_equal. 1: f_equal ; lia.
        symmetry. apply All_map_id. eapply All_impl. 1: eauto.
        intros ? ?. apply subst_elim_symbols_subst. rewrite sl. assumption.
      }
      symmetry in ee. inversion ee. subst. clear ee.
      eapply lhs_footprint_eq in hf as fe.
      rewrite mkElims_subst in fe. cbn in fe.
      unfold lhs in fe.
      rewrite !mkElims_subst in fe. cbn in fe.
      destruct (Nat.leb_spec0 #|map (subst0 τ) α| (#|pat_context r| + head r)).
      2: lia.
      replace (#|pat_context r| + head r - #|map (subst0 τ) α|)
      with r.(head) in fe by lia.
      destruct (nth_error ss (head r)) eqn:e2.
      2:{
        apply nth_error_None in e2.
        eapply declared_symbol_par_head in H. 2,3: eauto.
        subst ss. rewrite symbols_subst_length in e2. lia.
      }
      subst lhs rhs. cbn.
      unfold declared_symbol in H. rewrite e1 in H.
      symmetry in H. inversion H. subst. clear H.
      match goal with
      | ss' := ?t |- _ =>
        subst ss' ;
        set (ss := t) in *
      end.
      unfold ss in e2. unfold symbols_subst in e2.
      apply list_make_nth_error in e2. subst.
      cbn in fe.
      apply (f_equal decompose_elims) in fe.
      rewrite !mkElims_decompose_elims in fe. cbn in fe.
      apply (f_equal snd) in fe. cbn in fe.
      eapply first_match_lookup_sound in fm as elhs. 2,4: eauto. 2: exact I.
      eapply lhs_footprint_pattern in hf as hpl.
      eapply lhs_footprint_linear in hf as hll.
      set (Δ := map (vass nAnon) (list_init (tRel 0) #|τ|)).
      specialize (h #|τ| (Γ' ,,, Δ) (rho_ctx Σ None Γ ,,, Δ) α ui θ r0).
      forward h.
      { unfold all_rewrite_rules.
        rewrite nth_error_app_lt.
        1:{ eapply nth_error_Some_length. eassumption. }
        assumption.
      }
      assert (hα : All (pattern #|τ|) α × pattern_list_linear #|τ| α).
      { eapply match_lhs_pattern_subst. 5: eauto. all: eauto. }
      assert (hθ : All (pattern #|τ|) θ × pattern_list_linear #|τ| θ).
      { eapply first_match_pattern_subst in hpl. all: eauto. }
      destruct hα as [hα lα].
      destruct hθ as [hθ lθ].
      forward h by auto.
      forward h.
      { rewrite map_length in sl.
        eapply untyped_subslet_assumption_context. 2: auto.
        eapply rule_assumption_context with (n := n). 1: eauto.
        unfold all_rewrite_rules.
        rewrite nth_error_app_lt.
        1:{ eapply nth_error_Some_length. eauto. }
        assumption.
      }
      forward h.
      { rewrite <- fm. f_equal.
        unfold lhs. rewrite !mkElims_subst. cbn.
        rewrite map_length in sl.
        destruct (Nat.leb_spec0 #|α| (#|pat_context r| + head r)). 2: lia.
        replace (#|pat_context r| + head r - #|α|) with r.(head) by lia.
        destruct (nth_error _ r.(head)) eqn:e2.
        2:{
          apply nth_error_None in e2.
          rewrite map_length in hh.
          rewrite symbols_subst_length in e2. lia.
        }
        unfold symbols_subst in e2.
        apply list_make_nth_error in e2. subst.
        cbn. replace (head r + 0) with r.(head) by lia.
        eapply match_lhs_sound in hm as e2. 2: auto.
        rewrite e2. rewrite mkElims_subst. cbn. f_equal. f_equal.
        apply All_map_id. eapply All_impl. 1: eauto.
        intros ? ?. apply subst_elim_symbols_subst. rewrite sl. assumption.
      }
      forward h.
      { clear - X0. cbn in X0. subst Δ.
        induction τ.
        - auto.
        - cbn. constructor. 1: auto.
          cbn. apply pred1_refl_gen. auto.
      }
      rewrite !map_length.
      lazymatch goal with
      | hh : All2 ?P _ _ |- _ =>
        rename hh into hs
      end.
      eapply subst_factorisation in hs as hτ. 2,3: auto.
      destruct hτ as [τ' [? hτ]]. subst.
      eapply substitution_pred1
      with (s := τ') (s' := map (rho Σ None (rho_ctx Σ None Γ)) τ)
      in h. 2: auto.
      2:{
        clear - hτ predΓ' X0. cbn in X0. subst Δ. induction hτ.
        - constructor.
        - cbn. constructor.
          + assumption.
          + eapply pred1_refl_gen.
            clear - r X0.
            induction l.
            * intuition auto.
            * cbn. constructor. 1: auto.
              cbn. apply pred1_refl_gen. auto.
          + intuition auto.
      }
      match goal with
      | ss' := ?t |- _ =>
        subst ss' ;
        set (ss := t) in *
      end.
      rewrite subst_subst_compose in h.
      { rewrite map_length in sl.
        eapply closed_prule_rhs in heq_nth_error. 2,3: eauto.
        eapply closedn_subst with (k := 0).
        - subst ss. unfold symbols_subst.
          generalize (#|symbols rd| - 0). generalize 0 at 2. clear.
          intros i n. induction n in i |- *.
          + reflexivity.
          + cbn. eauto.
        - cbn. subst ss. rewrite symbols_subst_length.
          rewrite sl. replace (#|symbols rd| - 0) with #|symbols rd| by lia.
          assumption.
      }
      rewrite subst_subst_compose in h.
      { eapply first_match_subst_length in e0 as tl.
        rewrite map_length in tl. rewrite tl.
        eapply first_match_rule_list in e0 as [? e0].
        eapply rule_closed_rhs in e0. 2: eauto.
        eapply closedn_subst with (k := 0).
        - subst ss. unfold symbols_subst.
          generalize (#|symbols rd| - 0). generalize 0 at 2. clear.
          intros i n. induction n in i |- *.
          + reflexivity.
          + cbn. eauto.
        - cbn. subst ss. rewrite symbols_subst_length.
          replace (#|symbols rd| - 0) with #|symbols rd| by lia.
          assumption.
      }
      rewrite map_rho_subst_pattern. 1: auto.
      assumption.

    - simpl; simp rho lhs_viewc; simpl.
      simpl in X0. red in H. rewrite H /= heq_cst_body /=.
      now eapply pred1_refl_gen.

    - simpl in *. simp rho lhs_viewc; simpl.
      destruct (lookup_env Σ c) eqn:Heq; pcuic. destruct g; pcuic.
      destruct cst_body eqn:Heq'; pcuic.

    - simpl in *.
      rewrite rho_app_proj.
      { intros [? [rd [[[? ?] ?] [? e]]]].
        cbn in e. eapply first_match_lookup_sound in e as et. 2-4: eauto.
        2: exact I.
        apply (f_equal elim_kn) in et. cbn in et.
        rewrite elim_kn_mkApps in et. cbn in et.
        apply first_match_subst_length in e as σl.
        rewrite σl in et.
        eapply first_match_rule_list in e as hr. destruct hr as [n ?].
        erewrite elim_kn_lhs in et. 2-5: eauto. 2: exact I.
        discriminate.
      }
      rewrite decompose_app_mkApps; auto.
      change eq_inductive with (@eqb inductive _).
      destruct (eqb_spec i i) => //.
      eapply All2_nth_error_Some_right in heq_nth_error as [t' [? ?]]; eauto.
      simpl in y. rewrite e0. simpl.
      auto.

    - simpl; simp rho lhs_viewc.
      rewrite <- !fold_rho.
      eapply pred_abs; auto. unfold snoc in *. simpl in X2.
      rewrite app_context_nil_l in X2. apply X2.

    - (** Application *)
      simp rho.
      (* An application might be a lhs *)
      destruct lhs_viewc.
      + simp rho.
        eapply first_match_match_rule in e0 as h.
        destruct h as [? [hr h]].
        unfold all_rewrite_rules in hr.
        eapply first_match_lookup_sound in e0 as hs. 2,4: eauto. 2: exact I.
        unfold lhs in hs. rewrite !mkElims_subst in hs.
        eapply lookup_rewrite_decl_lookup_env in e as e'.
        eapply first_match_subst_length in e0 as σl.
        erewrite rule_symbols_subst in hs. 2-4: eauto.
        cbn in hs.
        destruct (elims r) as [| [] l _] eqn:e1 using list_rect_rev.
        1: discriminate.
        2:{
          rewrite !map_app in hs. rewrite mkElims_app in hs.
          cbn in hs. discriminate.
        }
        2:{
          rewrite !map_app in hs. rewrite mkElims_app in hs.
          cbn in hs. discriminate.
        }
        rewrite !map_app in hs. rewrite mkElims_app in hs.
        cbn in hs. inversion hs.
        cbn. set (ss := symbols_subst k 0 ui #|symbols rd|) in *.
        subst.
        apply pred1_elim_not_lhs_inv in X.
        2:{
          eapply lookup_env_nosubmatch in e' as h'. 2-3: eauto.
          unfold nosubmatch' in h'.
          specialize h' with (1 := hr).
          intros el' hx. eapply h'.
          rewrite e1. rewrite !map_app.
          eapply prefix_strict_prefix_append. eassumption.
        }
        destruct X as [el' [rel ?]]. subst.
        assert (assumption_context (pat_context r)).
        { eapply rule_assumption_context. all: eauto. }
        match type of rel with
        | All2 ?P (map ?f (map ?g ?l)) ?l' =>
          assert (h' : All2 P (map f (map g (elims r))) (l' ++ [eApp N1]))
        end.
        { rewrite e1. rewrite !map_app.
          apply All2_app.
          - assumption.
          - constructor. 2: constructor.
            cbn. constructor. assumption.
        }
        eapply lhs_elim_reduct in h'. 2: auto.
        2:{ eapply rule_is_rewrite_rule. all: eauto. }
        2:{
          eapply untyped_subslet_assumption_context.
          - apply assumption_context_subst_context. auto.
          - rewrite subst_context_length. auto.
        }
        destruct h' as [σ' [rσ e2]].
        match goal with
        | |- pred1 _ _ _ ?t _ =>
          replace t with (mkElims (tSymb k r.(head) ui) (el' ++ [eApp N1]))
        end.
        2:{
          rewrite mkElims_app. cbn. reflexivity.
        }
        rewrite e2.
        eapply All2_length in rσ as lσ. rewrite lσ.
        match goal with
        | |- pred1 _ _ _ ?t _ =>
          replace t with (subst0 σ' (subst ss #|σ'| (lhs r)))
        end.
        2:{
          unfold lhs. rewrite !mkElims_subst.
          erewrite rule_symbols_subst. 2-3: eauto. 2: lia.
          reflexivity.
        }
        assert (
          All2 (pred1 Σ Γ' (rho_ctx Σ None Γ))
            σ'
            (map (rho Σ None (rho_ctx Σ None Γ)) σ)
        ).
        { rewrite e1 in e2. rewrite !map_app in e2.
          apply (f_equal rev) in e2. rewrite !rev_app in e2.
          cbn in e2. eapply cons_inv in e2 as [e2 e3].
          apply (f_equal rev) in e3. rewrite !rev_invol in e3. subst.
          inversion e2. subst. clear e2.
          apply pred1_elim_not_lhs_inv in X0.
          2:{
            eapply lookup_env_nosubmatch in e' as h'. 2-3: eauto.
            unfold nosubmatch' in h'.
            specialize h' with (1 := hr).
            intros ? hx. rewrite lσ in hx. eapply h'.
            rewrite e1. rewrite !map_app.
            eapply prefix_strict_prefix_append. eassumption.
          }
          destruct X0 as [elρ [relρ e3]].
          match type of relρ with
          | All2 ?P (map ?f (map ?g ?l)) ?l' =>
            match type of X2 with
            | pred1 _ _ _ _ ?p =>
              assert (h' : All2 P (map f (map g (elims r))) (l' ++ [eApp p]))
            end
          end.
          { rewrite e1. rewrite !map_app.
            apply All2_app.
            - assumption.
            - constructor. 2: constructor.
              cbn. constructor. assumption.
          }
          rewrite lσ in h'.
          eapply lhs_elim_reduct in h'. 2: auto.
          2:{ eapply rule_is_rewrite_rule. all: eauto. }
          2:{
            eapply untyped_subslet_assumption_context.
            - apply assumption_context_subst_context. auto.
            - rewrite subst_context_length. lia.
          }
          destruct h' as [ρσ [rρσ e2]].
          rewrite e1 in e2. rewrite !map_app in e2.
          apply (f_equal rev) in e2. rewrite !rev_app in e2.
          cbn in e2. eapply cons_inv in e2 as [e2 e4].
          apply (f_equal rev) in e4. rewrite !rev_invol in e4. subst.
          inversion e2. subst. clear e2.
          rewrite rho_mkElims_not_lhs in e3.
          { eapply lookup_env_nosubmatch in e' as h'. 2-3: eauto.
            unfold nosubmatch' in h'.
            specialize h' with (1 := hr).
            intros el' hx. eapply h'.
            rewrite e1. rewrite !map_app.
            eapply prefix_strict_prefix_append. eassumption.
          }
          apply (f_equal decompose_elims) in e3.
          rewrite !mkElims_decompose_elims in e3. cbn in e3.
          apply (f_equal snd) in e3. cbn in e3.
          lazymatch type of e3 with
          | (map ?f (map ?g (map ?h ?b))) = (map ?i (map ?k ?d)) =>
            assert (h' :
              map f (map g (map h (b ++ [eApp p]))) =
              map i (map k (d ++ [eApp p]))
            )
          end.
          { rewrite !map_app. cbn. f_equal. 1: auto.
            rewrite lσ. f_equal. f_equal. auto.
          }
          rewrite <- e1 in h'.
          rewrite subst_elims_symbols_subst in h'.
          { rewrite <- lσ. rewrite σl. eapply rule_elim_pattern. all: eauto. }
          rewrite subst_elims_symbols_subst in h'.
          { rewrite σl. eapply rule_elim_pattern. all: eauto. }
          rewrite map_rho_subst_elim in h'.
          { rewrite σl. eapply rule_elim_pattern. all: eauto. }
          eapply map_subst_elim_inj in h'.
          2:{ eapply rule_elim_pattern. all: eauto. }
          2:{ eapply rule_linear. all: eauto. }
          2:{ rewrite map_length. auto. }
          2:{ apply All2_length in rρσ. lia. }
          subst. auto.
        }
        eapply nth_error_app_dec in hr as [[? hr] | [? hr]].
        * {
          eapply pred_par_rewrite_rule. all: eauto.
          - eapply pred1_pred1_ctx. eauto.
          - apply untyped_subslet_assumption_context.
            + apply assumption_context_subst_context. auto.
            + rewrite subst_context_length. lia.
        }
        * {
          eapply pred_rewrite_rule. all: eauto.
          - eapply pred1_pred1_ctx. eauto.
          - apply untyped_subslet_assumption_context.
            + apply assumption_context_subst_context. auto.
            + rewrite subst_context_length. lia.
        }
      + cbn. destruct view_lambda_fix_app.
        * {
          simpl; simp rho; simpl.
          (* Fix at head *)
          destruct (rho_fix_elim Σ None wfΣ I (rho_ctx Σ None Γ) mfix i l).
          - rewrite /unfold_fix {1}/map_fix nth_error_map e /=.
            eapply (is_constructor_app_ge (rarg d) _ _) in i0 => //.
            rewrite -> i0.
            rewrite map_app - !mkApps_nested.
            eapply (pred_mkApps _ _ _ _ _ [N1]) => //.
            2: repeat constructor; auto.
            rewrite - fold_fix_context_rho_ctx. 1,2: cbn ; eauto.
            rewrite rho_fix_subst. 1,2: cbn ; eauto.
            subst fn.
            rewrite /rho_fix_context in X0.
            rewrite fold_fix_context_rho_ctx. 1,2: auto with rho.
          - simp rho lhs_viewc in X0.
            simpl in X0. simp rho in X0.
            destruct (rho_fix_elim Σ None wfΣ I (rho_ctx Σ None Γ) mfix i (l ++ [a])).
            (* Shorter application does not reduce *)
            + (* Longer application reduces *)
              rewrite e in i0.
              rewrite /unfold_fix nth_error_map e /= i1.
              simpl.
              destruct (pred1_mkApps_tFix_inv _ _ _ _ _ _ _ _ wfΣ e i0 X) as
                [mfix1 [args1 [[HM1 Hmfix] Hargs]]].
              subst M1.
              rewrite [tApp _ _](mkApps_nested _ _ [N1]).
              red in Hmfix.
              eapply All2_nth_error_Some in Hmfix; eauto.
              destruct Hmfix as [d' [Hd' [eqd' [pred' eqsd']]]].
              eapply (pred1_mkApps_tFix_refl_inv _ _ _ mfix1) in X0; eauto.
              2:{ noconf eqsd'. simpl in H; noconf H.
                  rewrite -H0.
                  pose proof (All2_length _ _ Hargs).
                  unfold is_constructor in i1.
                  move: i1 i0.
                  elim: nth_error_spec => //.
                  rewrite app_length; intros x hnth. simpl.
                  unfold is_constructor.
                  elim: nth_error_spec => // x' hnth' rargl rargsl.
                  - destruct (eq_dec (rarg d) #|l|).
                    + lia.
                    + rewrite nth_error_app_lt in hnth. 1: lia.
                      rewrite hnth in hnth'.
                      noconf hnth'. intros. rewrite i1 in i0 => //.
                  - destruct (nth_error args1 (rarg d)) eqn:hnth'' => //.
                    eapply nth_error_Some_length in hnth''. lia.
              }
              move: X0 => [redo redargs].
              rewrite map_app.
              eapply pred_fix; eauto with pcuic.
              * eapply pred1_rho_fix_context_2; auto with pcuic.
                red in redo.
                solve_all.
                unfold on_Trel in *. intuition auto. now noconf b0.
              * unfold PCUICTyping.unfold_fix. rewrite nth_error_map e /=.
                rewrite map_fix_subst /= //.
                intros ?. simp rho lhs_viewc; simpl; now simp rho.
              * move: i1.
                eapply is_constructor_pred1. 1: eauto.
                eapply All2_app; eauto.
              * eapply All2_app => //. repeat constructor; auto.

            + (* None reduce *)
              simpl. rewrite map_app.
              rewrite /unfold_fix nth_error_map.
              destruct nth_error eqn:hnth => /=.
              * destruct (is_constructor (rarg d) (l ++ [a])) => //.
                rewrite -mkApps_nested.
                apply (pred_mkApps _ _ _ _ _ [N1] _). 1: auto.
                repeat constructor; auto.
              * rewrite -mkApps_nested.
                apply (pred_mkApps _ _ _ _ _ [N1] _). 1: auto.
                repeat constructor; auto.
        }
        * { (* Beta at top *)
          rewrite rho_app_lambda' in X0. 1,2: cbn ; eauto.
          destruct l.
          - simpl in X.
            (* Bug with depelim forgetting let bindings *)
            (* depelim X. *)
            generalize_by_eqs_vars X. destruct X.
            all: try solve [ simplify_dep_elim ].
            + simplify_dep_elim. solve_discr.
            + subst lhs rhs. simplify_dep_elim.
              apply (f_equal isElimSymb) in H. cbn in H.
              rewrite isElimSymb_subst in H.
              { apply untyped_subslet_length in u. rewrite u.
                rewrite subst_context_length.
                apply isElimSymb_lhs.
                eapply declared_symbol_head in d. all: eauto.
              }
              discriminate.
            + subst lhs rhs. simplify_dep_elim.
              apply (f_equal isElimSymb) in H. cbn in H.
              rewrite isElimSymb_subst in H.
              { apply untyped_subslet_length in u. rewrite u.
                rewrite subst_context_length.
                apply isElimSymb_lhs.
                eapply declared_symbol_par_head in d. all: eauto.
              }
              discriminate.
            + simplify_dep_elim.
              simp rho lhs_viewc in X4. rewrite <- !fold_rho in X4.
              (* Same bug *)
              (* depelim X4... *)
              generalize_by_eqs_vars X4.
              destruct X4 ; try solve [ simplify_dep_elim ; solve_discr ].
              * subst lhs rhs. simplify_dep_elim.
                apply (f_equal isElimSymb) in H0. cbn in H0.
                rewrite isElimSymb_subst in H0.
                { apply untyped_subslet_length in u. rewrite u.
                  rewrite subst_context_length.
                  apply isElimSymb_lhs.
                  eapply declared_symbol_head in d. all: eauto.
                }
                discriminate.
              * subst lhs rhs. simplify_dep_elim.
                apply (f_equal isElimSymb) in H0. cbn in H0.
                rewrite isElimSymb_subst in H0.
                { apply untyped_subslet_length in u. rewrite u.
                  rewrite subst_context_length.
                  apply isElimSymb_lhs.
                  eapply declared_symbol_par_head in d. all: eauto.
                }
                discriminate.
              * simplify_dep_elim. solve_discr. subst. econstructor ; eauto.
              * simplify_dep_elim. solve_discr. subst. inversion i.
            + simplify_dep_elim. discriminate.
          - simpl. simp rho. rewrite <- !fold_rho.
            rewrite map_app -mkApps_nested.
            constructor; eauto.
        }
        * (* No head redex *)
          simpl. constructor; auto.

    - simpl; simp rho lhs_viewc; rewrite <- !fold_rho. simpl.
      eapply pred_zeta; eauto.
      now simpl in X4; rewrite app_context_nil_l in X4.

    - (* Case reduction *)
      destruct ind.
      (* A pattern-matching may be a lhs *)
      destruct (lhs_viewc Σ None (tCase (i, n) p0 c0 brs0)) eqn:elhs.
      + simp rho. rewrite elhs. simp rho.
        simp rho.
        eapply first_match_match_rule in e0 as h.
        destruct h as [? [hr h]].
        unfold all_rewrite_rules in hr.
        eapply first_match_lookup_sound in e0 as hs. 2,4: eauto. 2: exact I.
        unfold lhs in hs. rewrite !mkElims_subst in hs.
        eapply lookup_rewrite_decl_lookup_env in e as e'.
        eapply first_match_subst_length in e0 as σl.
        erewrite rule_symbols_subst in hs. 2-4: eauto.
        cbn in hs.
        destruct (elims r) as [| [] l _] eqn:e1 using list_rect_rev.
        1: discriminate.
        1:{
          rewrite !map_app in hs. rewrite mkElims_app in hs.
          cbn in hs. discriminate.
        }
        2:{
          rewrite !map_app in hs. rewrite mkElims_app in hs.
          cbn in hs. discriminate.
        }
        rewrite !map_app in hs. rewrite mkElims_app in hs.
        cbn in hs. inversion hs. clear hs.
        cbn. set (ss := symbols_subst k 0 ui #|symbols rd|) in *.
        subst.
        apply pred1_elim_not_lhs_inv in X1.
        2:{
          eapply lookup_env_nosubmatch in e' as h'. 2-3: eauto.
          unfold nosubmatch' in h'.
          specialize h' with (1 := hr).
          intros el' hx. eapply h'.
          rewrite e1. rewrite !map_app.
          eapply prefix_strict_prefix_append. eassumption.
        }
        destruct X1 as [el' [rel ?]]. subst.
        assert (assumption_context (pat_context r)).
        { eapply rule_assumption_context. all: eauto. }
        match type of rel with
        | All2 ?P (map ?f (map ?g ?l)) ?l' =>
          assert (h' : All2 P (map f (map g (elims r))) (l' ++ [eCase (i, n) p1 brs1]))
        end.
        { rewrite e1. rewrite !map_app.
          apply All2_app.
          - assumption.
          - constructor. 2: constructor.
            cbn. constructor.
            + assumption.
            + eapply All2_impl. 1: eauto.
              intros [] []. cbn. intros. intuition eauto.
        }
        eapply lhs_elim_reduct in h'. 2: auto.
        2:{ eapply rule_is_rewrite_rule. all: eauto. }
        2:{
          eapply untyped_subslet_assumption_context.
          - apply assumption_context_subst_context. auto.
          - rewrite subst_context_length. auto.
        }
        destruct h' as [σ' [rσ e2]].
        match goal with
        | |- pred1 _ _ _ ?t _ =>
          replace t with (mkElims (tSymb k r.(head) ui) (el' ++ [eCase (i, n) p1 brs1]))
        end.
        2:{
          rewrite mkElims_app. cbn. reflexivity.
        }
        rewrite e2.
        eapply All2_length in rσ as lσ. rewrite lσ.
        match goal with
        | |- pred1 _ _ _ ?t _ =>
          replace t with (subst0 σ' (subst ss #|σ'| (lhs r)))
        end.
        2:{
          unfold lhs. rewrite !mkElims_subst.
          erewrite rule_symbols_subst. 2-3: eauto. 2: lia.
          reflexivity.
        }
        assert (
          All2 (pred1 Σ Γ' (rho_ctx Σ None Γ))
            σ'
            (map (rho Σ None (rho_ctx Σ None Γ)) σ)
        ).
        { rewrite e1 in e2. rewrite !map_app in e2.
          apply (f_equal rev) in e2. rewrite !rev_app in e2.
          cbn in e2. eapply cons_inv in e2 as [e2 e3].
          apply (f_equal rev) in e3. rewrite !rev_invol in e3. subst.
          inversion e2. subst. clear e2.
          apply pred1_elim_not_lhs_inv in X2.
          2:{
            eapply lookup_env_nosubmatch in e' as h'. 2-3: eauto.
            unfold nosubmatch' in h'.
            specialize h' with (1 := hr).
            intros ? hx. rewrite lσ in hx. eapply h'.
            rewrite e1. rewrite !map_app.
            eapply prefix_strict_prefix_append. eassumption.
          }
          destruct X2 as [elρ [relρ e3]].
          match type of relρ with
          | All2 ?P (map ?f (map ?g ?l)) ?l' =>
            match type of X0 with
            | pred1 _ _ _ _ ?p =>
              match type of X3 with
              | All2_prop_eq _ _ _ _ _ ?brs _ =>
                assert (h' : All2 P (map f (map g (elims r))) (l' ++ [eCase (i,n) p (map (on_snd (rho Σ None (rho_ctx Σ None Γ))) brs)]))
              end
            end
          end.
          { rewrite e1. rewrite !map_app.
            apply All2_app.
            - assumption.
            - constructor. 2: constructor.
              cbn. constructor.
              + assumption.
              + apply All2_map_right. apply All2_sym in X3.
                eapply All2_impl. 1: eauto.
                intros [] []. cbn. intros. intuition eauto.
          }
          rewrite lσ in h'.
          eapply lhs_elim_reduct in h'. 2: auto.
          2:{ eapply rule_is_rewrite_rule. all: eauto. }
          2:{
            eapply untyped_subslet_assumption_context.
            - apply assumption_context_subst_context. auto.
            - rewrite subst_context_length. lia.
          }
          destruct h' as [ρσ [rρσ e2]].
          rewrite e1 in e2. rewrite !map_app in e2.
          apply (f_equal rev) in e2. rewrite !rev_app in e2.
          cbn in e2. eapply cons_inv in e2 as [e2 e4].
          apply (f_equal rev) in e4. rewrite !rev_invol in e4. subst.
          inversion e2. subst. clear e2.
          rewrite rho_mkElims_not_lhs in e3.
          { eapply lookup_env_nosubmatch in e' as h'. 2-3: eauto.
            unfold nosubmatch' in h'.
            specialize h' with (1 := hr).
            intros el' hx. eapply h'.
            rewrite e1. rewrite !map_app.
            eapply prefix_strict_prefix_append. eassumption.
          }
          apply (f_equal decompose_elims) in e3.
          rewrite !mkElims_decompose_elims in e3. cbn in e3.
          apply (f_equal snd) in e3. cbn in e3.
          lazymatch type of e3 with
          | (map ?f (map ?g (map ?h ?b))) = (map ?j (map ?k ?d)) =>
            assert (h' :
              map f (map g (map h (b ++ [eCase (i, n) p brs]))) =
              map j (map k (d ++ [eCase (i, n) p brs]))
            )
          end.
          { rewrite !map_app. cbn. f_equal. 1: auto.
            rewrite lσ. f_equal. f_equal. all: auto.
          }
          rewrite <- e1 in h'.
          rewrite subst_elims_symbols_subst in h'.
          { rewrite <- lσ. rewrite σl. eapply rule_elim_pattern. all: eauto. }
          rewrite subst_elims_symbols_subst in h'.
          { rewrite σl. eapply rule_elim_pattern. all: eauto. }
          rewrite map_rho_subst_elim in h'.
          { rewrite σl. eapply rule_elim_pattern. all: eauto. }
          eapply map_subst_elim_inj in h'.
          2:{ eapply rule_elim_pattern. all: eauto. }
          2:{ eapply rule_linear. all: eauto. }
          2:{ rewrite map_length. auto. }
          2:{ apply All2_length in rρσ. lia. }
          subst. auto.
        }
        eapply nth_error_app_dec in hr as [[? hr] | [? hr]].
        * {
          eapply pred_par_rewrite_rule. all: eauto.
          - eapply pred1_pred1_ctx. eauto.
          - apply untyped_subslet_assumption_context.
            + apply assumption_context_subst_context. auto.
            + rewrite subst_context_length. lia.
        }
        * {
          eapply pred_rewrite_rule. all: eauto.
          - eapply pred1_pred1_ctx. eauto.
          - apply untyped_subslet_assumption_context.
            + apply assumption_context_subst_context. auto.
            + rewrite subst_context_length. lia.
        }
      + eapply lhs_viewc_not_lhs in elhs as notlhs. 2,3: cbn ; eauto.
        rewrite rho_app_case. 1: auto.
        destruct (decompose_app c0) eqn:Heq. simpl.
        destruct (construct_cofix_discr t) eqn:Heq'.
        * {
          destruct t; noconf Heq'.
          - (* Iota *)
            apply decompose_app_inv in Heq.
            subst c0. simpl.
            simp rho.
            rewrite <- !fold_rho.
            simpl. simp rho in X2.
            change eq_inductive with (@eqb inductive _).
            destruct (eqb_spec i ind).
            + subst ind.
              eapply pred1_mkApps_tConstruct in X1 as [args' [? ?]]. 2: auto.
              subst c1.
              eapply pred1_mkApps_refl_tConstruct in X2. 2: auto.
              econstructor; eauto. 1: pcuic.
              eapply All2_sym, All2_map_left, All2_impl; eauto.
              intros. hnf in X1. destruct X1. unfold on_Trel in *.
              intuition pcuic.
            + econstructor; pcuic.
              eapply All2_sym, All2_map_left, All2_impl; eauto.
              intros. unfold on_Trel in *. intuition pcuic.

          - (* CoFix *)
            apply decompose_app_inv in Heq.
            subst c0. simpl. simp rho. rewrite <- !fold_rho.
            simpl. simp rho in X2.
            eapply pred1_mkApps_tCoFix_inv in X1 as [mfix' [idx' [[? ?] ?]]].
            2: auto.
            subst c1.
            simpl in X2. eapply pred1_mkApps_tCoFix_refl_inv in X2. 2: auto.
            intuition.
            eapply All2_prop2_eq_split in a1. intuition.
            unfold unfold_cofix.
            assert (All2 (on_Trel eq dname) mfix'
                      (map_fix (rho Σ None) (rho_ctx Σ None Γ) (fold_fix_context (rho Σ None) (rho_ctx Σ None Γ) [] mfix) mfix)).
            { eapply All2_impl; [eapply b0|]; pcuic. }
            pose proof (All2_mix a1 X1).
            eapply pred1_rho_fix_context_2 in X2; pcuic.
            rewrite - fold_fix_context_rho_ctx in X2. 1: auto with rho.
            rewrite fix_context_map_fix in X2. 1: auto with rho.
            eapply rho_All_All2_local_env_inv in X2; pcuic.
            rewrite /rho_fix_context - fold_fix_context_rho_ctx in a1.
            1: auto with rho.

            destruct nth_error eqn:Heq.
            + (* CoFix unfolding *)
              simpl.
              pose proof Heq.
              eapply All2_nth_error_Some in Heq; eauto.
              destruct Heq; intuition auto.
              eapply pred_cofix_case
                with (map_fix (rho Σ None) (rho_ctx Σ None Γ) (rho_ctx_over Σ None (rho_ctx Σ None Γ)
                                                      (fix_context mfix)) mfix)
                                          (rarg d); pcuic.
              * eapply All2_local_env_pred_fix_ctx; eauto with rho.
                eapply All2_prop2_eq_split in a. intuition auto.
                eapply All2_local_env_sym.
                pcuic.
              * eapply All2_mix; pcuic.
                rewrite /rho_fix_context - fold_fix_context_rho_ctx in b1.
                1: auto with rho.
                eapply All2_mix. 1: eauto.
                now rewrite /rho_fix_context - fold_fix_context_rho_ctx in b0.
              * unfold unfold_cofix.
                rewrite nth_error_map.
                rewrite H. simpl. f_equal. f_equal.
                unfold map_fix.
                rewrite fold_fix_context_rho_ctx. 1: auto with rho.
                rewrite (map_cofix_subst _ (fun Γ Γ' => rho Σ None (Γ ,,,  Γ'))) //.
                intros. simp rho lhs_viewc; simpl; simp rho. reflexivity.
              * apply All2_sym. eapply All2_map_left. eapply All2_impl; eauto.
                unfold on_Trel in *.
                intros. intuition pcuic.

            + eapply pred_case; eauto.
              * {
                eapply pred_mkApps.
                - constructor.
                  + pcuic.
                  + rewrite /rho_fix_context - fold_fix_context_rho_ctx.
                    1: auto with rho.
                    eapply All2_local_env_pred_fix_ctx. 1,2: auto with rho.
                    eapply All2_prop2_eq_split in a. intuition auto.
                    eapply All2_local_env_sym.
                    pcuic.
                  + eapply All2_mix; pcuic.
                    * rewrite /rho_fix_context - fold_fix_context_rho_ctx in b1.
                      1: auto with rho.
                      now rewrite /rho_fix_context - fold_fix_context_rho_ctx.
                    * eapply All2_mix; pcuic.
                - pcuic.
              }
              * eapply All2_sym, All2_map_left, All2_impl; eauto.
                unfold on_Trel in *.
                intros. intuition pcuic.
        }
        * apply decompose_app_inv in Heq. subst c0.
          assert (All2 (on_Trel_eq (pred1 Σ Γ' (rho_ctx Σ None Γ)) snd fst) brs1
                      (map (λ x : nat * term, (fst x, rho Σ None (rho_ctx Σ None Γ) (snd x))) brs0)).
          { eapply All2_sym, All2_map_left, All2_impl; eauto.
            unfold on_Trel in *.
            intros. intuition pcuic.
          }
          destruct t; try discriminate; simpl; pcuic.

    - (* Proj *)
      simpl.
      destruct p as [[ind pars] arg].
      (* A projection may be a lhs *)
      destruct (lhs_viewc Σ None (tProj (ind, pars, arg) c)) eqn:elhs.
      + simp rho. rewrite elhs. simp rho.
        eapply first_match_match_rule in e0 as h.
        destruct h as [? [hr h]].
        unfold all_rewrite_rules in hr.
        eapply first_match_lookup_sound in e0 as hs. 2,4: eauto. 2: exact I.
        unfold lhs in hs. rewrite !mkElims_subst in hs.
        eapply lookup_rewrite_decl_lookup_env in e as e'.
        eapply first_match_subst_length in e0 as σl.
        erewrite rule_symbols_subst in hs. 2-4: eauto.
        cbn in hs.
        destruct (elims r) as [| [] l _] eqn:e1 using list_rect_rev.
        1: discriminate.
        1:{
          rewrite !map_app in hs. rewrite mkElims_app in hs.
          cbn in hs. discriminate.
        }
        1:{
          rewrite !map_app in hs. rewrite mkElims_app in hs.
          cbn in hs. discriminate.
        }
        rewrite !map_app in hs. rewrite mkElims_app in hs.
        cbn in hs. inversion hs. clear hs.
        cbn. set (ss := symbols_subst k 0 ui #|symbols rd|) in *.
        subst.
        apply pred1_elim_not_lhs_inv in X.
        2:{
          eapply lookup_env_nosubmatch in e' as h'. 2-3: eauto.
          unfold nosubmatch' in h'.
          specialize h' with (1 := hr).
          intros el' hx. eapply h'.
          rewrite e1. rewrite !map_app.
          eapply prefix_strict_prefix_append. eassumption.
        }
        destruct X as [el' [rel ?]]. subst.
        assert (assumption_context (pat_context r)).
        { eapply rule_assumption_context. all: eauto. }
        match type of rel with
        | All2 ?P (map ?f (map ?g ?l)) ?l' =>
          assert (h' : All2 P (map f (map g (elims r))) (l' ++ [eProj (ind, pars, arg )]))
        end.
        { rewrite e1. rewrite !map_app.
          apply All2_app.
          - assumption.
          - constructor. 2: constructor.
            cbn. constructor.
        }
        eapply lhs_elim_reduct in h'. 2: auto.
        2:{ eapply rule_is_rewrite_rule. all: eauto. }
        2:{
          eapply untyped_subslet_assumption_context.
          - apply assumption_context_subst_context. auto.
          - rewrite subst_context_length. auto.
        }
        destruct h' as [σ' [rσ e2]].
        match goal with
        | |- pred1 _ _ _ ?t _ =>
          replace t with (mkElims (tSymb k r.(head) ui) (el' ++ [eProj (ind, pars, arg)]))
        end.
        2:{
          rewrite mkElims_app. cbn. reflexivity.
        }
        rewrite e2.
        eapply All2_length in rσ as lσ. rewrite lσ.
        match goal with
        | |- pred1 _ _ _ ?t _ =>
          replace t with (subst0 σ' (subst ss #|σ'| (lhs r)))
        end.
        2:{
          unfold lhs. rewrite !mkElims_subst.
          erewrite rule_symbols_subst. 2-3: eauto. 2: lia.
          reflexivity.
        }
        assert (
          All2 (pred1 Σ Γ' (rho_ctx Σ None Γ))
            σ'
            (map (rho Σ None (rho_ctx Σ None Γ)) σ)
        ).
        { rewrite e1 in e2. rewrite !map_app in e2.
          apply (f_equal rev) in e2. rewrite !rev_app in e2.
          cbn in e2. eapply cons_inv in e2 as [e2 e3].
          apply (f_equal rev) in e3. rewrite !rev_invol in e3. subst.
          inversion e2. subst. clear e2.
          apply pred1_elim_not_lhs_inv in X0.
          2:{
            eapply lookup_env_nosubmatch in e' as h'. 2-3: eauto.
            unfold nosubmatch' in h'.
            specialize h' with (1 := hr).
            intros ? hx. rewrite lσ in hx. eapply h'.
            rewrite e1. rewrite !map_app.
            eapply prefix_strict_prefix_append. eassumption.
          }
          destruct X0 as [elρ [relρ e3]].
          match type of relρ with
          | All2 ?P (map ?f (map ?g ?l)) ?l' =>
            assert (h' : All2 P (map f (map g (elims r))) (l' ++ [eProj (ind, pars, arg)]))
          end.
          { rewrite e1. rewrite !map_app.
            apply All2_app.
            - assumption.
            - constructor. 2: constructor.
              cbn. constructor.
          }
          rewrite lσ in h'.
          eapply lhs_elim_reduct in h'. 2: auto.
          2:{ eapply rule_is_rewrite_rule. all: eauto. }
          2:{
            eapply untyped_subslet_assumption_context.
            - apply assumption_context_subst_context. auto.
            - rewrite subst_context_length. lia.
          }
          destruct h' as [ρσ [rρσ e2]].
          rewrite e1 in e2. rewrite !map_app in e2.
          apply (f_equal rev) in e2. rewrite !rev_app in e2.
          cbn in e2. eapply cons_inv in e2 as [e2 e4].
          apply (f_equal rev) in e4. rewrite !rev_invol in e4. subst.
          inversion e2. subst. clear e2.
          rewrite rho_mkElims_not_lhs in e3.
          { eapply lookup_env_nosubmatch in e' as h'. 2-3: eauto.
            unfold nosubmatch' in h'.
            specialize h' with (1 := hr).
            intros el' hx. eapply h'.
            rewrite e1. rewrite !map_app.
            eapply prefix_strict_prefix_append. eassumption.
          }
          apply (f_equal decompose_elims) in e3.
          rewrite !mkElims_decompose_elims in e3. cbn in e3.
          apply (f_equal snd) in e3. cbn in e3.
          lazymatch type of e3 with
          | (map ?f (map ?g (map ?h ?b))) = (map ?i (map ?k ?d)) =>
            assert (h' :
              map f (map g (map h (b ++ [eProj (ind, pars, arg)]))) =
              map i (map k (d ++ [eProj (ind, pars, arg)]))
            )
          end.
          { rewrite !map_app. cbn. f_equal. auto. }
          rewrite <- e1 in h'.
          rewrite subst_elims_symbols_subst in h'.
          { rewrite <- lσ. rewrite σl. eapply rule_elim_pattern. all: eauto. }
          rewrite subst_elims_symbols_subst in h'.
          { rewrite σl. eapply rule_elim_pattern. all: eauto. }
          rewrite map_rho_subst_elim in h'.
          { rewrite σl. eapply rule_elim_pattern. all: eauto. }
          eapply map_subst_elim_inj in h'.
          2:{ eapply rule_elim_pattern. all: eauto. }
          2:{ eapply rule_linear. all: eauto. }
          2:{ rewrite map_length. auto. }
          2:{ apply All2_length in rρσ. lia. }
          subst. auto.
        }
        eapply nth_error_app_dec in hr as [[? hr] | [? hr]].
        * {
          eapply pred_par_rewrite_rule. all: eauto.
          - eapply pred1_pred1_ctx. eauto.
          - apply untyped_subslet_assumption_context.
            + apply assumption_context_subst_context. auto.
            + rewrite subst_context_length. lia.
        }
        * {
          eapply pred_rewrite_rule. all: eauto.
          - eapply pred1_pred1_ctx. eauto.
          - apply untyped_subslet_assumption_context.
            + apply assumption_context_subst_context. auto.
            + rewrite subst_context_length. lia.
        }
      + eapply lhs_viewc_not_lhs in elhs as notlhs. 2,3: cbn ; eauto.
        rewrite rho_app_proj. 1: auto.
        destruct decompose_app eqn:Heq.
        destruct (view_construct_cofix t).
        * {
          apply decompose_app_inv in Heq.
          subst c. simpl. simp rho in X0 |- *.
          pose proof (pred1_pred1_ctx _ X0).
          eapply pred1_mkApps_tConstruct in X as [args' [? ?]]; subst. 2: auto.
          eapply pred1_mkApps_refl_tConstruct in X0. 2: auto.
          destruct nth_error eqn:Heq.
          - change eq_inductive with (@eqb inductive _).
            destruct (eqb_spec ind c0); subst.
            + econstructor; eauto.
              now rewrite nth_error_map Heq.
            + eapply pred_proj_congr, pred_mkApps; auto with pcuic.
          - destruct eq_inductive.
            + constructor; auto.
              eapply pred_mkApps; auto.
              econstructor; eauto.
            + constructor; auto.
              eapply pred_mkApps; auto.
              econstructor; eauto.
        }
        * {
          apply decompose_app_inv in Heq.
          subst c. simpl.
          simp rho in X0 |- *.
          eapply pred1_mkApps_tCoFix_inv in X as [mfix' [idx' [[? ?] ?]]].
          2: auto.
          subst c'.
          simpl in a.
          pose proof X0.
          eapply pred1_mkApps_tCoFix_refl_inv in X0. 2: auto.
          destruct X0.
          unfold unfold_cofix.
          eapply All2_prop2_eq_split in a1. intuition auto.
          assert (All2 (on_Trel eq dname) mfix'
                      (map_fix (rho Σ None) (rho_ctx Σ None Γ) (fold_fix_context (rho Σ None) (rho_ctx Σ None Γ) [] mfix) mfix)).
          { eapply All2_impl; [eapply b|]; pcuic. }
          pose proof (All2_mix a1 X0) as X2.
          eapply pred1_rho_fix_context_2 in X2; pcuic.
          rewrite - fold_fix_context_rho_ctx in X2. 1: auto with rho.
          rewrite fix_context_map_fix in X2. 1: auto with rho.
          eapply rho_All_All2_local_env_inv in X2; pcuic.
          rewrite /rho_fix_context - fold_fix_context_rho_ctx in a1.
          1: auto with rho.
          intuition auto.
          destruct nth_error eqn:Heq.
          (* Proj cofix *)
          - (* CoFix unfolding *)
            simpl.
            pose proof Heq.
            eapply All2_nth_error_Some in Heq; eauto. destruct Heq; intuition auto.

            eapply pred_cofix_proj with (map_fix (rho Σ None) (rho_ctx Σ None Γ) (rho_ctx_over Σ None (rho_ctx Σ None Γ) (fix_context mfix)) mfix)
                                        (rarg d); pcuic.

            + eapply All2_local_env_pred_fix_ctx; eauto with rho.
              eapply All2_prop2_eq_split in a. intuition auto.
              eapply All2_local_env_sym.
              pcuic.

            + eapply All2_mix; pcuic.
              rewrite /rho_fix_context - fold_fix_context_rho_ctx in b0.
              1: auto with rho.
              eapply All2_mix. 1: eauto.
              now rewrite /rho_fix_context - fold_fix_context_rho_ctx in b.
            + unfold unfold_cofix.
              rewrite nth_error_map.
              rewrite H. simpl. f_equal. f_equal.
              unfold map_fix.
              rewrite fold_fix_context_rho_ctx. 1: auto with rho.
              rewrite (map_cofix_subst _ (fun Γ Γ' => rho Σ None (Γ ,,,  Γ'))) //.
              intros. simp rho lhs_viewc; simpl; simp rho. reflexivity.

          - eapply pred_proj_congr; eauto.
        }
        * eapply decompose_app_inv in Heq. subst c.
          destruct t; noconf d; econstructor; eauto.

    - simp rho lhs_viewc; simpl; simp rho.
      rewrite /rho_fix_context - fold_fix_context_rho_ctx. 1: auto with rho.
      constructor; eauto.
      1: now eapply All2_local_env_pred_fix_ctx.
      red. red in X3.
      eapply All2_sym, All2_map_left, All2_impl; eauto.
      simpl. unfold on_Trel; intuition pcuic.
      rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

    - simp rho lhs_viewc; simpl; simp rho.
      rewrite - fold_fix_context_rho_ctx. 1: auto with rho.
      constructor; eauto.
      1: now eapply All2_local_env_pred_fix_ctx.
      red. red in X3.
      eapply All2_sym, All2_map_left, All2_impl; eauto.
      simpl. unfold on_Trel; intuition pcuic.
      rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

    - simp rho lhs_viewc; rewrite <- !fold_rho ; simpl; econstructor; eauto.
      simpl in X2. now rewrite !app_context_nil_l in X2.

    - simpl in *. simp rho lhs_viewc. constructor. 1: eauto.
      eapply All2_sym, All2_map_left, All2_impl. 1: eauto.
      intros. simpl in X. intuition.

    - destruct t; noconf H; simpl; constructor; eauto.
  Qed.

End Triangle.

(* The diamond lemma for parallel reduction follows directly from the triangle lemma. *)

Corollary pred1_diamond {cf : checker_flags} {Σ : global_env} {Γ Δ Δ' t u v} :
  forall (hΣ : wf Σ),
    confluenv Σ ->
    pred1 Σ Γ Δ t u ->
    pred1 Σ Γ Δ' t v ->
    pred1 Σ Δ (rho_ctx Σ None Γ) u (rho Σ None (rho_ctx Σ None Γ) t) *
    pred1 Σ Δ' (rho_ctx Σ None Γ) v (rho Σ None (rho_ctx Σ None Γ) t).
Proof.
  intros.
  split; eapply triangle; auto.
Qed.

(* Print Assumptions pred1_diamond. *)
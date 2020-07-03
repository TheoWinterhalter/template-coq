(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".
Require Import ssreflect ssrbool.
From Coq Require Import Bool List Utf8 ZArith Lia Morphisms String.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSize
  PCUICLiftSubst PCUICSigmaCalculus PCUICUnivSubst PCUICTyping PCUICReduction
  PCUICSubstitution PCUICReflect PCUICClosed PCUICParallelReduction
  PCUICPattern PCUICInduction PCUICRW.

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

  Lemma pred1_mkApps_tInd (Σ : global_env) (Γ Δ : context)
        ind u (args : list term) c :
    pred1 Σ Γ Δ (mkApps (tInd ind u) args) c ->
    {args' : list term & (c = mkApps (tInd ind u) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    - depelim X...
      + (* TODO Rewrite rules *) admit.
      + (* TODO Rewrite rules *) admit.
      + exists []. intuition auto.
    - intros. rewrite <- mkApps_nested in X.
      depelim X...
      + simpl in H; noconf H. solve_discr.
      + prepare_discr. apply mkApps_eq_decompose_app in H.
        rewrite !decompose_app_rec_mkApps in H. noconf H.
      + admit.
      + admit.
      + destruct (IHargs _ X1) as [args' [-> Hargs']].
        exists (args' ++ [N1])%list.
        rewrite <- mkApps_nested. intuition auto.
        eapply All2_app; auto.
  (* Qed. *)
  Admitted.

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
  Context (wfΣ : wf Σ).

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
  Context (on_extra : on_option (fun '(k,rd) => onrd rd) extra).

  (* All the rewrite rules of a rewrite_decl *)
  Definition all_rewrite_rules (rd : rewrite_decl) :=
    rd.(prules) ++ rd.(rules).

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
      + eapply typecheck_closed in hrhs. 2: auto.
        destruct hrhs as [_ hrhs].
        apply MCProd.andP in hrhs. destruct hrhs as [hrhs _].
        rewrite app_context_length in hrhs.
        rewrite map_length in hrhs.
        assumption.
    - eapply All_impl. 1: exact hpr.
      intros r [? ? hrhs hh ? he ?]. unfold onrr. split. 2: split.
      + rewrite map_length in hh. assumption.
      + assumption.
      + eapply typecheck_closed in hrhs. 2: auto.
        destruct hrhs as [_ hrhs].
        apply MCProd.andP in hrhs. destruct hrhs as [hrhs _].
        rewrite app_context_length in hrhs.
        rewrite map_length in hrhs.
        assumption.
  Qed.

  Definition lookup_rewrite_decl (k : kername) : option rewrite_decl :=
    match extra with
    | Some (kn, rd) =>
        if eq_kername k kn
        then Some rd
        else lookup_rd k
    | None => lookup_rd k
    end.

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
      not_lhs t ->
      lhs_view t.

  Arguments is_lhs {_}.
  Arguments is_not_lhs {_}.

  Equations? lhs_viewc (t : term) : lhs_view t :=
    lhs_viewc t with inspect (elim_kn t) := {
    | @exist (Some k) e1 with inspect (lookup_rewrite_decl k) := {
      | @exist (Some rd) e2 with inspect (first_match k (all_rewrite_rules rd) t) := {
        | @exist (Some (ui, σ, r)) e3 := is_lhs k rd r ui σ _ _ ;
        | @exist None e3 := is_not_lhs _
        } ;
      | @exist None e2 := is_not_lhs _
      } ;
    | @exist None e1 := is_not_lhs _
    }.
  Proof.
    - destruct X as [? [? [[[? ?] ?] [e e0]]]]. cbn in e0.
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
      rewrite e0 in e3.
      discriminate.
    - destruct X as [? [? [[[? ?] ?] [e e0]]]]. cbn in e0.
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
    - destruct X as [? [? [[[? ?] ?] [e e0]]]]. cbn in e0.
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
  Qed.

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

    | is_not_lhs notlhs with t := {
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
      revert n. rewrite -mkApps_nested. intro n.
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
    simpl. revert n. rewrite -mkApps_nested. intro n. simp rho.
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
    - simpl. simp rho lhs_viewc. cbn.
      rewrite map_fix_rho_map. reflexivity.
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
        * revert n. rewrite -mkApps_nested /=. intro n.
          autorewrite with rho.
          simpl. simp rho. repeat fold_rho. rewrite /unfold_fix.
          rewrite /map_fix nth_error_map eqfix /= isc map_fix_subst ?map_app //.
          intros m; simp rho lhs_viewc. simpl. f_equal; now simp rho.
        * revert n. rewrite -mkApps_nested /=. intro n.
          simp rho lhs_viewc. simpl. simp rho lhs_viewc.
          repeat fold_rho.
          now rewrite /unfold_fix /map_fix nth_error_map eqfix /= isc map_app.
      + revert n. rewrite -mkApps_nested /=. intro n. simp rho lhs_viewc.
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
    forall r t h,
      lhs_viewc t = is_not_lhs h ->
      ∑ h', lhs_viewc (rename r t) = is_not_lhs h'.
  Proof.
    intros r t h e.
    destruct (lhs_viewc t). 1: discriminate.
    destruct (lhs_viewc (rename r t)).
    1:{
      exfalso. clear e.
      eapply not_lhs_rename with (r := r) in h.
      apply h. eexists k, rd, _. intuition eauto.
    }
    eexists. reflexivity.
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
      simp rho. destruct (lhs_viewc (rename _ _)) as [? ? ? ?| notlhs].
      2:{
        exfalso. apply notlhs.
        eexists k, rd, _. intuition eauto.
      }
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
      specialize (h n0).
      destruct (nth_error Γ n0) as [c|] eqn:e.
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
      red in h. specialize (h n0).
      destruct nth_error eqn:e.
      2:{ cbn in Heq. discriminate. }
      cbn in Heq. apply some_inj in Heq. rewrite Heq in h.
      rewrite h. cbn. reflexivity.

    (* Undeclared rel *)
    - red in h. specialize (h n0).
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
      revert n0. cbn [rename]. rewrite rename_mkApps. intros n0.
      simpl.
      assert (eqargs : map (rename r) (map (rho Γ) (l ++ [a])) =
              map (rho Δ) (map (rename r) (l ++ [a]))).
      { rewrite !map_map_compose !map_app.
        apply app_cong.
        (* f_equal => /= //. *)
        2:{
          cbn. (* clear - Heq0 H1.
          f_equal. *)
          erewrite H2. all: eauto.
          cbn. lia.
        }
        solve_all.
        eapply All_size with (f := size).
        intros t ht. eapply H2. 2: auto.
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
          - clear - H2 h Hren.
            unfold fix_subst. autorewrite with len. generalize #|mfix| at 1 4.
            induction n; simpl; auto.
            rewrite IHn. clear IHn. f_equal; auto.
            specialize (H2 Γ (tFix mfix n)) as Hbod.
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
          rewrite H3.
          rewrite -(map_app (rename r) l [a]) -is_constructor_rename H3 //.
          rewrite rename_mkApps. clear - h H2 eqargs.
          f_equal.
          ++ simpl. f_equal.
            autorewrite with len.
            eapply (map_fix_rho_rename mfix i l); eauto.
            intros. eapply H2. all: eauto.
            cbn. lia.
          ++ apply eqargs.
        -- rewrite rename_mkApps.
          clear - eqargs h H2.
          f_equal; auto.
          2:{ now rewrite -(map_app (rename r) _ [_]). }
          simpl. f_equal. autorewrite with len.
          apply (map_fix_rho_rename mfix i l); eauto.
          intros; eapply H2; simpl; try lia. auto.

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
      destruct e as [n' e]. rewrite e.
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
      destruct er as [n' er]. rewrite er.
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
      destruct er as [n' er]. rewrite er.
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
      destruct er as [n' er]. rewrite er.
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
      destruct er as [n' er]. rewrite er.
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
      destruct er as [n' er]. rewrite er.
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
      destruct er as [n' er]. rewrite er.
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
      destruct er as [n' er]. rewrite er.
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
      destruct er as [n' er]. rewrite er.
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
        * red. clear -wfΣ eqf redr redl.
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
        * red. clear -wfΣ eqf redr redl.
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
  Proof.
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

  Inductive triangle_rules  Σ kn nsymb (rho : context → term → term) rho_ctx : list rewrite_rule → Type :=
  | triangle_rules_nil : triangle_rules Σ kn nsymb rho rho_ctx []
  | triangle_rules_cons :
      ∀ r rl,
        (∀ npat' Γ σ ui θ r',
          All (pattern npat') σ →
          untyped_subslet Γ σ r.(pat_context) →
          let ss := symbols_subst kn 0 ui nsymb in
          let tl := subst0 σ (subst ss #|σ| (lhs r)) in
          let tr := subst0 (map (rho Γ) σ) (subst ss #|σ| (rhs r)) in
          let tr' := subst0 (map (rho Γ) θ) (subst ss #|θ| (rhs r')) in
          first_match kn rl tl = Some (ui, θ, r') →
          (* TODO Use the env notion of pred1, right now too weak as it doesn't
          include the extra rules! *)
          pred1 Σ Γ (rho_ctx Γ) tr tr'
        ) →
        triangle_rules Σ kn nsymb rho rho_ctx rl →
        triangle_rules Σ kn nsymb rho rho_ctx (rl ++ [r]).

  Definition confl_rew_decl Σ wfΣ kn d :=
    let l := d.(prules) ++ d.(rules) in
    let extra := Some (kn, d) in
    ∑ on_extra,
      triangle_rules
        Σ kn #|d.(symbols)| (rho Σ wfΣ extra on_extra) (rho_ctx Σ wfΣ extra on_extra) l.

  Definition confl_decl Σ hΣ kn decl : Type :=
    match decl with
    | RewriteDecl rew => confl_rew_decl Σ hΣ kn rew
    | _ => True
    end.

  Inductive confluenv : global_env → Type :=
  | confluenv_nil : confluenv []
  | confluenv_decl Σ hΣ kn d :
      confluenv Σ →
      confl_decl Σ hΣ kn d →
      confluenv (Σ ,, (kn, d)).

End Confluenv.

Section Triangle.

  Context {cf : checker_flags}.
  Context (Σ : global_env).
  Context (wfΣ : wf Σ).

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
      All (on_rewrite_rule
        (lift_typing typing)
        Σ'
        (map (vass nAnon) rd.(symbols))
      ) (all_rewrite_rules rd)
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

  Context (cΣ : confluenv Σ).

  Axiom todo_triangle : forall {A}, A.

  Ltac todo_triangle := (exact todo_triangle).

  Lemma triangle Γ Δ t u :
    let Pctx := fun (Γ Δ : context) => pred1_ctx Σ Δ (rho_ctx Σ wfΣ None I Γ) in
    pred1 Σ Γ Δ t u ->
    pred1 Σ Δ (rho_ctx Σ wfΣ None I Γ) u (rho Σ wfΣ None I (rho_ctx Σ wfΣ None I Γ) t).
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
      rewrite (rho_app_lambda _ _ _ _ _ _ _ _ _ []).
      eapply (substitution0_pred1); simpl in *. 1-2: eauto.
      rewrite app_context_nil_l in X0.
      eapply X0.

    - simp rho.
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
        rewrite -{1}(firstn_skipn (S i) (rho_ctx _ _ _ _ Γ)).
        pose proof (All2_local_env_length X0).
        assert (S i = #|firstn (S i) Γ'|).
        { rewrite !firstn_length_le; try lia. }
        assert (S i = #|firstn (S i) (rho_ctx Σ wfΣ None I Γ)|).
        { rewrite !firstn_length_le; try lia. }
        rewrite {5}H0 {6}H1.
        eapply weakening_pred1_pred1; eauto.
        eapply All2_local_env_over_firstn_skipn. auto.
      + noconf heq_option_map.

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
      rewrite rho_app_fix.
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
          rewrite /rho_fix_context -fold_fix_context_rho_ctx.
          eapply strong_substitutivity; eauto.
          -- apply ctxmap_fix_subst.
          -- rewrite -rho_fix_subst -{1}fix_context_map_fix.
             apply ctxmap_fix_subst.
          -- rewrite -rho_fix_subst.
             eapply All2_prop2_eq_split in X3.
             apply pred_subst_rho_fix; intuition auto.
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
          rewrite - fold_fix_context_rho_ctx.
          set (rhoΓ := rho_ctx _ _ _ _ Γ ,,, rho_ctx_over _ _ _ _ (rho_ctx _ _ _ _ Γ) (fix_context mfix0)) in *.
          rewrite !subst_inst. eapply simpl_pred; try now sigma.
          eapply strong_substitutivity; eauto.
          -- apply ctxmap_cofix_subst.
          -- unfold rhoΓ.
             rewrite -{1}fix_context_map_fix.
             rewrite -rho_cofix_subst.
             now eapply ctxmap_cofix_subst.
          -- rewrite -rho_cofix_subst.
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
      + rewrite - fold_fix_context_rho_ctx.
        rewrite rho_ctx_app in Hreleq1.
        eapply substitution_pred1; eauto.
        eapply wf_rho_cofix_subst; eauto.
        now eapply All2_length in X3.
      + eapply All2_sym, All2_map_left, All2_impl; eauto; simpl; intuition eauto.

    - simp rho. destruct lhs_viewc.
      + simp rho. todo_triangle.
      + cbn. eapply pred1_refl_gen. assumption.

    - simp rho. destruct lhs_viewc.
      2:{
        exfalso. apply n0. cbn.
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
      simp rho. todo_triangle.

    - simp rho. destruct lhs_viewc.
      2:{
        exfalso. apply n0. cbn.
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
      (* Deal with the above, then copy and adapt *)
      simp rho. todo_triangle.

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

    - simpl; simp rho. eapply pred_abs; auto. unfold snoc in *. simpl in X2.
      rewrite app_context_nil_l in X2. apply X2.

    - (** Application *)
      simp rho.
      (* An application might be a lhs *)
      destruct lhs_viewc.
      + simp rho. todo_triangle.
      + cbn. destruct view_lambda_fix_app.
        * {
          simpl; simp rho; simpl.
          (* Fix at head *)
          destruct (rho_fix_elim _ wfΣ None I (rho_ctx Σ wfΣ None I Γ) mfix i l).
          - rewrite /unfold_fix {1}/map_fix nth_error_map e /=.
            eapply (is_constructor_app_ge (rarg d) _ _) in i0 => //.
            rewrite -> i0.
            rewrite map_app - !mkApps_nested.
            eapply (pred_mkApps _ _ _ _ _ [N1]) => //.
            2: repeat constructor; auto.
            rewrite - fold_fix_context_rho_ctx.
            rewrite rho_fix_subst. subst fn.
            rewrite /rho_fix_context in X0.
            rewrite fold_fix_context_rho_ctx.
            auto.
          - simp rho lhs_viewc in X0.
            simpl in X0. simp rho in X0.
            destruct (rho_fix_elim Σ wfΣ None I (rho_ctx Σ wfΣ None I Γ) mfix i (l ++ [a])).
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
          rewrite rho_app_lambda' in X0.
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

    - simpl; simp rho; simpl. eapply pred_zeta; eauto.
      now simpl in X4; rewrite app_context_nil_l in X4.

    - (* Case reduction *)
      destruct ind.
      (* A pattern-matching may be a lhs *)
      destruct (lhs_viewc Σ wfΣ None I (tCase (i, n) p0 c0 brs0)) eqn:elhs.
      + simp rho. rewrite elhs. simp rho.
        todo_triangle.
      + rewrite rho_app_case. 1: auto.
        destruct (decompose_app c0) eqn:Heq. simpl.
        destruct (construct_cofix_discr t) eqn:Heq'.
        * {
          destruct t; noconf Heq'.
          - (* Iota *)
            apply decompose_app_inv in Heq.
            subst c0. simpl.
            simp rho. rewrite <- !fold_rho.
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
                      (map_fix (rho Σ wfΣ None I) (rho_ctx Σ wfΣ None I Γ) (fold_fix_context (rho Σ wfΣ None I) (rho_ctx Σ wfΣ None I Γ) [] mfix) mfix)).
            { eapply All2_impl; [eapply b0|]; pcuic. }
            pose proof (All2_mix a1 X1).
            eapply pred1_rho_fix_context_2 in X2; pcuic.
            rewrite - fold_fix_context_rho_ctx in X2.
            rewrite fix_context_map_fix in X2.
            eapply rho_All_All2_local_env_inv in X2; pcuic.
            rewrite /rho_fix_context - fold_fix_context_rho_ctx in a1.

            destruct nth_error eqn:Heq.
            + (* CoFix unfolding *)
              simpl.
              pose proof Heq.
              eapply All2_nth_error_Some in Heq; eauto.
              destruct Heq; intuition auto.
              eapply pred_cofix_case
                with (map_fix (rho Σ wfΣ None I) (rho_ctx Σ wfΣ None I Γ) (rho_ctx_over Σ wfΣ None I (rho_ctx Σ wfΣ None I Γ)
                                                      (fix_context mfix)) mfix)
                                          (rarg d); pcuic.
              * eapply All2_local_env_pred_fix_ctx; eauto.
                eapply All2_prop2_eq_split in a. intuition auto.
                eapply All2_local_env_sym.
                pcuic.
              * eapply All2_mix; pcuic.
                rewrite /rho_fix_context - fold_fix_context_rho_ctx in b1.
                eapply All2_mix. 1: eauto.
                now rewrite /rho_fix_context - fold_fix_context_rho_ctx in b0.
              * unfold unfold_cofix.
                rewrite nth_error_map.
                rewrite H. simpl. f_equal. f_equal.
                unfold map_fix.
                rewrite fold_fix_context_rho_ctx.
                rewrite (map_cofix_subst _ (fun Γ Γ' => rho Σ wfΣ None I (Γ ,,,  Γ'))) //.
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
                    eapply All2_local_env_pred_fix_ctx.
                    eapply All2_prop2_eq_split in a. intuition auto.
                    eapply All2_local_env_sym.
                    pcuic.
                  + eapply All2_mix; pcuic.
                    * rewrite /rho_fix_context - fold_fix_context_rho_ctx in b1.
                      now rewrite /rho_fix_context - fold_fix_context_rho_ctx.
                    * eapply All2_mix; pcuic.
                - pcuic.
              }
              * eapply All2_sym, All2_map_left, All2_impl; eauto.
                unfold on_Trel in *.
                intros. intuition pcuic.
        }
        * apply decompose_app_inv in Heq. subst c0.
          assert (All2 (on_Trel_eq (pred1 Σ Γ' (rho_ctx Σ wfΣ None I Γ)) snd fst) brs1
                      (map (λ x : nat * term, (fst x, rho Σ wfΣ None I (rho_ctx Σ wfΣ None I Γ) (snd x))) brs0)).
          { eapply All2_sym, All2_map_left, All2_impl; eauto.
            unfold on_Trel in *.
            intros. intuition pcuic.
          }
          destruct t; try discriminate; simpl; pcuic.

    - (* Proj *)
      simpl.
      destruct p as [[ind pars] arg].
      (* A projection may be a lhs *)
      destruct (lhs_viewc Σ wfΣ None I (tProj (ind, pars, arg) c)) eqn:elhs.
      + simp rho. rewrite elhs. simp rho.
        todo_triangle.
      + rewrite rho_app_proj. 1: auto.
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
                      (map_fix (rho Σ wfΣ None I) (rho_ctx Σ wfΣ None I Γ) (fold_fix_context (rho Σ wfΣ None I) (rho_ctx Σ wfΣ None I Γ) [] mfix) mfix)).
          { eapply All2_impl; [eapply b|]; pcuic. }
          pose proof (All2_mix a1 X0) as X2.
          eapply pred1_rho_fix_context_2 in X2; pcuic.
          rewrite - fold_fix_context_rho_ctx in X2.
          rewrite fix_context_map_fix in X2.
          eapply rho_All_All2_local_env_inv in X2; pcuic.
          rewrite /rho_fix_context - fold_fix_context_rho_ctx in a1.
          intuition auto.
          destruct nth_error eqn:Heq.
          (* Proj cofix *)
          - (* CoFix unfolding *)
            simpl.
            pose proof Heq.
            eapply All2_nth_error_Some in Heq; eauto. destruct Heq; intuition auto.

            eapply pred_cofix_proj with (map_fix (rho Σ wfΣ None I) (rho_ctx Σ wfΣ None I Γ) (rho_ctx_over Σ wfΣ None I (rho_ctx Σ wfΣ None I Γ)
                                                                              (fix_context mfix)) mfix)
                                        (rarg d); pcuic.

            + eapply All2_local_env_pred_fix_ctx; eauto.
              eapply All2_prop2_eq_split in a. intuition auto.
              eapply All2_local_env_sym.
              pcuic.

            + eapply All2_mix; pcuic.
              rewrite /rho_fix_context - fold_fix_context_rho_ctx in b0.
              eapply All2_mix. 1: eauto.
              now rewrite /rho_fix_context - fold_fix_context_rho_ctx in b.
            + unfold unfold_cofix.
              rewrite nth_error_map.
              rewrite H. simpl. f_equal. f_equal.
              unfold map_fix.
              rewrite fold_fix_context_rho_ctx. auto.
              rewrite (map_cofix_subst _ (fun Γ Γ' => rho Σ wfΣ None I (Γ ,,,  Γ'))) //.
              intros. simp rho lhs_viewc; simpl; simp rho. reflexivity.

          - eapply pred_proj_congr; eauto.
        }
        * eapply decompose_app_inv in Heq. subst c.
          destruct t; noconf d; econstructor; eauto.

    - simp rho lhs_viewc; simpl; simp rho.
      rewrite /rho_fix_context - fold_fix_context_rho_ctx.
      constructor; eauto.
      1: now eapply All2_local_env_pred_fix_ctx.
      red. red in X3.
      eapply All2_sym, All2_map_left, All2_impl; eauto.
      simpl. unfold on_Trel; intuition pcuic.
      rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

    - simp rho lhs_viewc; simpl; simp rho.
      rewrite - fold_fix_context_rho_ctx.
      constructor; eauto.
      1: now eapply All2_local_env_pred_fix_ctx.
      red. red in X3.
      eapply All2_sym, All2_map_left, All2_impl; eauto.
      simpl. unfold on_Trel; intuition pcuic.
      rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

    - simp rho; simpl; econstructor; eauto.
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
    pred1 Σ Δ (rho_ctx Σ hΣ None I Γ) u (rho Σ hΣ None I (rho_ctx Σ hΣ None I Γ) t) *
    pred1 Σ Δ' (rho_ctx Σ hΣ None I Γ) v (rho Σ hΣ None I (rho_ctx Σ hΣ None I Γ) t).
Proof.
  intros.
  split; eapply triangle; auto.
Qed.

(* Print Assumptions pred1_diamond. *)
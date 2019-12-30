(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils Universes BasicAst AstUtils
UnivSubst EnvironmentTyping.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
PCUICPosition.

From MetaCoq Require Export LibHypsNaming.

Require Import String.
Require Import Wf Wellfounded Relation_Definitions.
Require Import Relation_Operators Lexicographic_Product Wf_nat.
Require Import ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.

From Equations Require Import Equations.
Require Import CRelationClasses.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Import MonadNotation.

(** * Typing derivations

  Inductive relations for reduction, conversion and typing of PCUIC terms.
  These come with many additional functions, to define the reduction operations,
  deal with arities, declarations in the environment etc...

 *)

Definition isSort T :=
  match T with
  | tSort u => True
  | _ => False
  end.

Fixpoint isArity T :=
  match T with
  | tSort u => True
  | tProd _ _ codom => isArity codom
  | tLetIn _ _ _ codom => isArity codom
  | _ => False
  end.

Definition subst_context s k (Γ : context) : context :=
  fold_context (fun k' => subst s (k' + k)) Γ.

Lemma subst_context_length s n Γ : #|subst_context s n Γ| = #|Γ|.
Proof.
  induction Γ as [|[na [body|] ty] tl] in Γ |- *; cbn; eauto.
  - rewrite !List.rev_length !mapi_length !app_length !List.rev_length. simpl.
    lia.
  - rewrite !List.rev_length !mapi_length !app_length !List.rev_length. simpl.
    lia.
Qed.

Fixpoint smash_context (Γ Γ' : context) : context :=
  match Γ' with
  | {| decl_body := Some b |} :: Γ' => smash_context (subst_context [b] 0 Γ) Γ'
  | {| decl_body := None |} as d :: Γ' => smash_context (Γ ++ [d])%list Γ'
  | [] => Γ
  end.

Lemma smash_context_length Γ Γ' : #|smash_context Γ Γ'| = #|Γ| + context_assumptions Γ'.
Proof.
  induction Γ' as [|[na [body|] ty] tl] in Γ |- *; cbn; eauto.
  - now rewrite IHtl subst_context_length.
  - rewrite IHtl app_length. simpl. lia.
Qed.

Module PCUICLookup := Lookup PCUICTerm PCUICEnvironment.
Include PCUICLookup.

(** Inductive substitution, to produce a constructors' type *)
Definition inds ind u (l : list one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Lemma inds_length ind u l : #|inds ind u l| = #|l|.
Proof.
  unfold inds. induction l; simpl; congruence.
Qed.

Lemma inds_spec ind u l :
  inds ind u l = List.rev (mapi (fun i _ => tInd {| inductive_mind := ind; inductive_ind := i |} u) l).
Proof.
  unfold inds, mapi. induction l using rev_ind. simpl. reflexivity.
  now rewrite app_length /= Nat.add_1_r IHl mapi_rec_app /= rev_app_distr /= Nat.add_0_r.
Qed.

Definition type_of_constructor mdecl (cdecl : ident * term * nat) (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance_constr u (snd (fst cdecl))).

(** ** Reduction *)

(** *** Helper functions for reduction *)

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d =>
    if isLambda d.(dbody) then
      Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
    else None (* We don't unfold ill-formed fixpoints, which would
                 render confluence unprovable, creating an infinite
                 number of critical pairs between unfoldings of fixpoints.
                 e.g. [fix f := f] is not allowed. *)
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a => isConstruct_app a
  | None => false
  end.

Lemma fix_subst_length mfix : #|fix_subst mfix| = #|mfix|.
Proof.
  unfold fix_subst. generalize (tFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma cofix_subst_length mfix : #|cofix_subst mfix| = #|mfix|.
Proof.
  unfold cofix_subst. generalize (tCoFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma fix_context_length mfix : #|fix_context mfix| = #|mfix|.
Proof. unfold fix_context. now rewrite List.rev_length mapi_length. Qed.

Definition tDummy := tVar "".

Definition iota_red npar c args brs :=
  (mkApps (snd (List.nth c brs (0, tDummy))) (List.skipn npar args)).


(** *** One step strong beta-zeta-iota-fix-delta reduction

  Inspired by the reduction relation from Coq in Coq [Barras'99].
*)

Local Open Scope type_scope.
Arguments OnOne2 {A} P%type l l'.

(* TODO MOVE *)
Fixpoint list_make {A} (f : nat -> A) (i n : nat) : list A :=
  match n with
  | 0 => []
  | S n => f i :: list_make f (S i) n
  end.

(* TODO MOVE *)
Lemma list_make_length :
  forall A f i n,
    #|@list_make A f i n| = n.
Proof.
  intros A f i n.
  induction n in i |- *.
  - reflexivity.
  - simpl. f_equal. apply IHn.
Qed.

(* TODO MOVE *)
Lemma list_make_map :
  forall A f i n B (g : A -> B),
    map g (@list_make A f i n) = list_make (fun i => g (f i)) i n.
Proof.
  intros A f i n B g.
  induction n in i |- *.
  - reflexivity.
  - simpl. f_equal. eapply IHn.
Qed.

Definition symbols_subst k n u m :=
  list_make (fun i => tSymb k i u) n (m - n).

Lemma symbols_subst_length :
  forall k n u m,
    #|symbols_subst k n u m| = m - n.
Proof.
  intros k n u m.
  unfold symbols_subst.
  apply list_make_length.
Qed.

(* MOVED from PCUICSubtitution *)
Inductive untyped_subslet (Γ : context) : list term -> context -> Type :=
| untyped_emptyslet : untyped_subslet Γ [] []
| untyped_cons_let_ass Δ s na t T :
    untyped_subslet Γ s Δ ->
    untyped_subslet Γ (t :: s) (Δ ,, vass na T)
| untyped_cons_let_def Δ s na t T :
    untyped_subslet Γ s Δ ->
    untyped_subslet Γ (subst0 s t :: s) (Δ ,, vdef na t T).

Lemma untyped_subslet_length :
  forall Γ s Δ,
    untyped_subslet Γ s Δ ->
    #|s| = #|Δ|.
Proof.
  intros Γ s Δ h.
  induction h.
  all: cbn ; eauto.
Qed.

Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
(** Reductions *)
(** Beta *)
| red_beta na t b a :
    red1 Σ Γ (tApp (tLambda na t b) a) (subst10 a b)

(** Let *)
| red_zeta na b t b' :
    red1 Σ Γ (tLetIn na b t b') (subst10 b b')

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    red1 Σ Γ (tRel i) (lift0 (S i) body)

(** Case *)
| red_iota ind pars c u args p brs :
    red1 Σ Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args) brs)
         (iota_red pars c args brs)

(** Fix unfolding, with guard *)
| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Γ (mkApps (tFix mfix idx) args) (mkApps fn args)

(** CoFix-case unfolding *)
| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tProj p (mkApps (tCoFix mfix idx) args))
         (tProj p (mkApps fn args))

(** Constant unfolding *)
| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    red1 Σ Γ (tConst c u) (subst_instance_constr u body)

(** Proj *)
| red_proj i pars narg args k u arg :
    nth_error args (pars + narg) = Some arg ->
    red1 Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args)) arg

(** Rewrite rule *)
| red_rewrite_rule k ui decl n r s :
    declared_symbol Σ k decl ->
    nth_error decl.(rules) n = Some r ->
    let ss := symbols_subst k 0 ui #|decl.(symbols)| in
    untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
    let lhs := subst0 s (subst ss #|s| (lhs r)) in
    let rhs := subst0 s (subst ss #|s| (rhs r)) in
    red1 Σ Γ lhs rhs


| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_pred ind p p' c brs : red1 Σ Γ p p' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p' c brs)
| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c' brs)
| case_red_brs ind p c brs brs' :
    OnOne2 (on_Trel_eq (red1 Σ Γ) snd fst) brs brs' ->
    red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

| proj_red p c c' : red1 Σ Γ c c' -> red1 Σ Γ (tProj p c) (tProj p c')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (tApp N1 M2)
| app_red_r M2 N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tProd na M1 M2) (tProd na N1 M2)
| prod_red_r na M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (tProd na M1 M2) (tProd na M1 N2)

| evar_red ev l l' : OnOne2 (red1 Σ Γ) l l' -> red1 Σ Γ (tEvar ev l) (tEvar ev l')

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx).

Lemma red1_ind_all :
  forall (Σ : global_env) (P : context -> term -> term -> Type),

       (forall (Γ : context) (na : name) (t b a : term),
        P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

       (forall (Γ : context) (na : name) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args : list term)
          (p : term) (brs : list (nat * term)),
        P Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args) brs) (iota_red pars c args brs)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) (ip : inductive * nat) (p : term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (nat * term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) (c : ident) (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : universe_instance, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance_constr u body)) ->

       (forall (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (k : nat) (u : universe_instance)
         (arg : term),
           nth_error args (pars + narg) = Some arg ->
           P Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args)) arg) ->

       (forall Γ k ui decl n r s,
          declared_symbol Σ k decl ->
          nth_error decl.(rules) n = Some r ->
          let ss := symbols_subst k 0 ui #|decl.(symbols)| in
          untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
          let lhs := subst0 s (subst ss #|s| (lhs r)) in
          let rhs := subst0 s (subst ss #|s| (rhs r)) in
          P Γ lhs rhs) ->

       (forall (Γ : context) (na : name) (M M' N : term),
        red1 Σ Γ M M' -> P Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

       (forall (Γ : context) (na : name) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : name) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : name) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : name) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ind : inductive * nat) (p p' c : term) (brs : list (nat * term)),
        red1 Σ Γ p p' -> P Γ p p' -> P Γ (tCase ind p c brs) (tCase ind p' c brs)) ->

       (forall (Γ : context) (ind : inductive * nat) (p c c' : term) (brs : list (nat * term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) (ind : inductive * nat) (p c : term) (brs brs' : list (nat * term)),
           OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) snd fst) brs brs' ->
           P Γ (tCase ind p c brs) (tCase ind p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' ->
                                                             P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) (M1 N1 : term) (M2 : term), red1 Σ Γ M1 N1 -> P Γ M1 N1 ->
                                                         P Γ (tApp M1 M2) (tApp N1 M2)) ->

       (forall (Γ : context) (M2 N2 : term) (M1 : term), red1 Σ Γ M2 N2 -> P Γ M2 N2 ->
                                                         P Γ (tApp M1 M2) (tApp M1 N2)) ->

       (forall (Γ : context) (na : name) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : name) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term),
           OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
Proof.
  intros Σ P X X0 X1 X2 X3 X4 X5 X6 X7 XSymb X8 X9 X10 X11 X12 X13 X14 X15 X16
         X17 X18 X19 X20 X21 X22 X23 X24 X25 Γ t t0 Xlast.
  revert Γ t t0 Xlast.
  fix aux 4. intros Γ t T.
  move aux at top.
  destruct 1 ;
  match goal with
  | |- P _ (tFix _ _) (tFix _ _) => idtac
  | |- P _ (tCoFix _ _) (tCoFix _ _) => idtac
  | |- P _ (mkApps (tFix _ _) _) _ => idtac
  | |- P _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
  | |- P _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
  | lhs0 := _ |- P _ _ _ => idtac
  | H : _ |- _ => eapply H; eauto
  end.
  - eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.

  - eapply XSymb. all: eauto.

  - revert brs brs' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. intuition auto. constructor. intuition auto.

  - revert l l' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    constructor. split; auto.
    constructor. auto.

  - eapply X22.
    revert mfix0 mfix1 o; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X23.
    revert o. generalize (fix_context mfix0). intros c Xnew.
    revert mfix0 mfix1 Xnew; fix auxl 3; intros l l' Hl;
    destruct Hl; constructor; try split; auto; intuition.

  - eapply X24.
    revert mfix0 mfix1 o.
    fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X25.
    revert o. generalize (fix_context mfix0). intros c new.
    revert mfix0 mfix1 new; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
Defined.


(** *** Reduction

  The reflexive-transitive closure of 1-step reduction. *)

Inductive red Σ Γ M : term -> Type :=
| refl_red : red Σ Γ M M
| trans_red : forall (P : term) N, red Σ Γ M P -> red1 Σ Γ P N -> red Σ Γ M N.

Fixpoint subst_app (t : term) (us : list term) : term :=
  match t, us with
  | tLambda _ A t, u :: us => subst_app (t {0 := u}) us
  | _, [] => t
  | _, _ => mkApps t us
  end.

(** *** η-conversion *)

(* [eta_expands u v] states v is an expansion of u *)
Definition eta_expands u v : Type :=
  ∑ na A t π,
    u = zipc t π /\
    v = zipc (tLambda na A (tApp (lift0 1 t) (tRel 0))) π.

Definition eta_eq :=
  clos_refl_sym_trans eta_expands.

(** ** Utilities for typing *)

(** Decompose an arity into a context and a sort *)

Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.

Lemma destArity_app_aux {Γ Γ' t}
  : destArity (Γ ,,, Γ') t = option_map (fun '(ctx, s) => (Γ ,,, ctx, s))
                                        (destArity Γ' t).
Proof.
  revert Γ'.
  induction t; cbn; intro Γ'; try reflexivity.
  - rewrite <- app_context_cons. now eapply IHt2.
  - rewrite <- app_context_cons. now eapply IHt3.
Qed.

Lemma destArity_app {Γ t}
  : destArity Γ t = option_map (fun '(ctx, s) => (Γ ,,, ctx, s))
                               (destArity [] t).
Proof.
  exact (@destArity_app_aux Γ [] t).
Qed.

Lemma destArity_app_Some {Γ t ctx s}
  : destArity Γ t = Some (ctx, s)
    -> ∑ ctx', destArity [] t = Some (ctx', s) /\ ctx = Γ ,,, ctx'.
Proof.
  intros H. rewrite destArity_app in H.
  destruct (destArity [] t) as [[ctx' s']|]; cbn in *.
  exists ctx'. inversion H. now subst.
  discriminate H.
Qed.

Lemma mkApps_nonempty f l :
  l <> [] -> mkApps f l = tApp (mkApps f (removelast l)) (last l f).
Proof.
  destruct l using rev_ind. intros; congruence.
  intros. rewrite <- mkApps_nested. simpl. f_equal.
  rewrite removelast_app. congruence. simpl. now rewrite app_nil_r.
  rewrite last_app. congruence.
  reflexivity.
Qed.

Lemma destArity_tFix {mfix idx args} :
  destArity [] (mkApps (tFix mfix idx) args) = None.
Proof.
  induction args. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.

Lemma destArity_tApp {t u l} :
  destArity [] (mkApps (tApp t u) l) = None.
Proof.
  induction l. reflexivity.
  rewrite mkApps_nonempty.
  intros e; discriminate e.
  reflexivity.
Qed.


Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t <= u " (at level 50, Γ, t, u at next level).

(** ** Cumulativity *)

Inductive cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| cumul_refl t u : leq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <= u
| cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_red_r t u v : Σ ;;; Γ |- t <= v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <= u
| cumul_eta_l t u v : eta_expands t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_eta_r t u v : Σ ;;; Γ |- t <= v -> eta_expands u v -> Σ ;;; Γ |- t <= u

where " Σ ;;; Γ |- t <= u " := (cumul Σ Γ t u) : type_scope.

(** *** Conversion

   Defined as cumulativity in both directions.
 *)

Definition conv `{checker_flags} Σ Γ T U : Type :=
  (Σ ;;; Γ |- T <= U) * (Σ ;;; Γ |- U <= T).

Notation " Σ ;;; Γ |- t = u " := (conv Σ Γ t u) (at level 50, Γ, t, u at next level) : type_scope.


(** ** Typing relation *)

Module PCUICEnvTyping := EnvTyping PCUICTerm PCUICEnvironment.
Include PCUICEnvTyping.

Section WfArity.
  Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).

  Definition isWfArity Σ (Γ : context) T :=
    { ctx & { s & (destArity [] T = Some (ctx, s)) * All_local_env (lift_typing typing Σ) (Γ ,,, ctx) } }.

  Context (property : forall (Σ : global_env_ext) (Γ : context),
              All_local_env (lift_typing typing Σ) Γ ->
              forall (t T : term), typing Σ Γ t T -> Type).

  Definition isWfArity_prop Σ (Γ : context) T :=
    { wfa : isWfArity Σ Γ T & All_local_env_over typing property Σ _ (snd (projT2 (projT2 wfa))) }.
End WfArity.

(* AXIOM GUARD CONDITION *)
Axiom fix_guard : mfixpoint term -> bool.

Axiom fix_guard_red1 :
  forall Σ Γ mfix mfix' idx,
    fix_guard mfix ->
    red1 Σ Γ (tFix mfix idx) (tFix mfix' idx) ->
    fix_guard mfix'.

Axiom fix_guard_eq_term :
  forall mfix mfix' idx,
    fix_guard mfix ->
    upto_names (tFix mfix idx) (tFix mfix' idx) ->
    fix_guard mfix'.

Axiom fix_guard_rename :
  forall mfix f,
    let mfix' :=
        map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix
    in
    fix_guard mfix ->
    fix_guard mfix'.

Axiom fix_guard_lift :
  forall mfix n k,
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (lift n k) (lift n k')) mfix in
    fix_guard mfix ->
    fix_guard mfix'.

Axiom fix_guard_subst :
  forall mfix s k,
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    fix_guard mfix ->
    fix_guard mfix'.

(* AXIOM INDUCTIVE GUARD CONDITION *)
Axiom ind_guard : mutual_inductive_body -> bool.


(** Compute the type of a case from the predicate [p], actual parameters [pars] and
    an inductive declaration. *)

Fixpoint instantiate_params_subst params pars s ty :=
  match params with
  | [] => match pars with
          | [] => Some (s, ty)
          | _ :: _ => None (* Too many arguments to substitute *)
          end
  | d :: params =>
    match d.(decl_body), ty with
    | None, tProd _ _ B =>
      match pars with
      | hd :: tl => instantiate_params_subst params tl (hd :: s) B
      | [] => None (* Not enough arguments to substitute *)
      end
    | Some b, tLetIn _ _ _ b' => instantiate_params_subst params pars (subst0 s b :: s) b'
    | _, _ => None (* Not enough products in the type *)
    end
  end.

(* If [ty] is [Π params . B] *)
(* and [⊢ pars : params] *)
(* then [instantiate_params] is [B{pars}] *)

Definition instantiate_params (params : context) (pars : list term) (ty : term) : option term :=
  match instantiate_params_subst (List.rev params) pars [] ty with
  | Some (s, ty) => Some (subst0 s ty)
  | None => None
  end.

Lemma instantiate_params_ params pars ty :
  instantiate_params params pars ty
  = option_map (fun '(s, ty) => subst0 s ty)
               (instantiate_params_subst (List.rev params) pars [] ty).
Proof.
  unfold instantiate_params.
  repeat (destruct ?; cbnr).
Qed.

(* [params], [p] and output are already instanciated by [u] *)
Definition build_branches_type ind mdecl idecl params u p : list (option (nat × term)) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let branch_type i '(id, t, ar) :=
    let ty := subst0 inds (subst_instance_constr u t) in
    match instantiate_params (subst_instance_context u mdecl.(ind_params)) params ty with
    | Some ty =>
      let '(sign, ccl) := decompose_prod_assum [] ty in
      let nargs := List.length sign in
      let allargs := snd (decompose_app ccl) in
      let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
      let cstr := tConstruct ind i u in
      let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)])%list in
      Some (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args))
    | None => None
    end
  in mapi branch_type idecl.(ind_ctors).

Lemma build_branches_type_ ind mdecl idecl params u p :
  build_branches_type ind mdecl idecl params u p
  = let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
    let branch_type i '(id, t, ar) :=
        let ty := subst0 inds (subst_instance_constr u t) in
        option_map (fun ty =>
         let '(sign, ccl) := decompose_prod_assum [] ty in
         let nargs := List.length sign in
         let allargs := snd (decompose_app ccl) in
         let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
         let cstr := tConstruct ind i u in
         let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)])%list in
         (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args)))
                  (instantiate_params (subst_instance_context u mdecl.(ind_params))
                                      params ty)
    in mapi branch_type idecl.(ind_ctors).
Proof.
  apply mapi_ext. intros ? [[? ?] ?]; cbnr.
  repeat (destruct ?; cbnr).
Qed.

(* [params] and output already instanciated by [u] *)
Definition build_case_predicate_type ind mdecl idecl params u ps : option term :=
  X <- instantiate_params (subst_instance_context u (ind_params mdecl)) params
                         (subst_instance_constr u (ind_type idecl)) ;;
  X <- destArity [] X ;;
  let inddecl :=
      {| decl_name := nNamed idecl.(ind_name);
         decl_body := None;
         decl_type := mkApps (tInd ind u) (map (lift0 #|X.1|) params ++ to_extended_list X.1) |} in
  ret (it_mkProd_or_LetIn (X.1 ,, inddecl) (tSort ps)).

Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| type_Rel n decl :
    All_local_env (lift_typing typing Σ) Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)

| type_Sort l :
    All_local_env (lift_typing typing Σ) Γ ->
    LevelSet.In l (global_ext_levels Σ) ->
    Σ ;;; Γ |- tSort (Universe.make l) : tSort (Universe.super l)

| type_Prod na A B s1 s2 :
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- B : tSort s2 ->
    Σ ;;; Γ |- tProd na A B : tSort (Universe.sort_of_product s1 s2)

| type_Lambda na A t s1 B :
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- t : B ->
    Σ ;;; Γ |- (tLambda na A t) : tProd na A B

| type_LetIn na b B t s1 A :
    Σ ;;; Γ |- B : tSort s1 ->
    Σ ;;; Γ |- b : B ->
    Σ ;;; Γ ,, vdef na b B |- t : A ->
    Σ ;;; Γ |- tLetIn na b B t : tLetIn na b B A

| type_App t na A B u :
    Σ ;;; Γ |- t : tProd na A B ->
    Σ ;;; Γ |- u : A ->
    Σ ;;; Γ |- tApp t u : B{0 := u}

| type_Symb k n u :
    All_local_env (lift_typing typing Σ) Γ ->
    forall decl (isdecl : declared_symbol Σ.1 k decl) ty,
      nth_error decl.(symbols) n = Some ty ->
      consistent_instance_ext Σ decl.(rew_universes) u ->
      Σ ;;; Γ |- tSymb k n u : subst (symbols_subst k (S n) u #|decl.(symbols)|) 0 (subst_instance_constr u ty)

| type_Const cst u :
    All_local_env (lift_typing typing Σ) Γ ->
    forall decl (isdecl : declared_constant Σ.1 cst decl),
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- (tConst cst u) : subst_instance_constr u decl.(cst_type)

| type_Ind ind u :
    All_local_env (lift_typing typing Σ) Γ ->
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tInd ind u) : subst_instance_constr u idecl.(ind_type)

| type_Construct ind i u :
    All_local_env (lift_typing typing Σ) Γ ->
    forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 mdecl idecl (ind, i) cdecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tConstruct ind i u) : type_of_constructor mdecl cdecl (ind, i) u

| type_Case indnpar u p c brs args :
    let ind := indnpar.1 in
    let npar := indnpar.2 in
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    mdecl.(ind_npars) = npar ->
    let params := List.firstn npar args in
    forall ps pty, build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
    Σ ;;; Γ |- p : pty ->
    existsb (leb_sort_family (universe_family ps)) idecl.(ind_kelim) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    forall btys, map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
    All2 (fun br bty => (br.1 = bty.1) * (Σ ;;; Γ |- br.2 : bty.2) * (Σ ;;; Γ |- bty.2 : tSort ps)) brs btys ->
    Σ ;;; Γ |- tCase indnpar p c brs : mkApps p (skipn npar args ++ [c])

| type_Proj p c u :
    forall mdecl idecl pdecl (isdecl : declared_projection Σ.1 mdecl idecl p pdecl) args,
    Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
    #|args| = ind_npars mdecl ->
    let ty := snd pdecl in
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) (subst_instance_constr u ty)

| type_Fix mfix n decl :
    let types := fix_context mfix in
    fix_guard mfix ->
    nth_error mfix n = Some decl ->
    All_local_env (lift_typing typing Σ) (Γ ,,, types) ->
    All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))
    * (isLambda d.(dbody) = true)%type) mfix ->
    Σ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix mfix n decl :
    allow_cofix ->
    let types := fix_context mfix in
    nth_error mfix n = Some decl ->
    All_local_env (lift_typing typing Σ) (Γ ,,, types) ->
    All (fun d => Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype)) mfix ->
    Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)

| type_Cumul t A B :
    Σ ;;; Γ |- t : A ->
    (isWfArity typing Σ Γ B + {s & Σ ;;; Γ |- B : tSort s})%type ->
    Σ ;;; Γ |- A <= B -> Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (typing Σ Γ t T) : type_scope.

Notation wf_local Σ Γ := (All_local_env (lift_typing typing Σ) Γ).

Lemma meta_conv {cf : checker_flags} Σ Γ t A B :
    Σ ;;; Γ |- t : A ->
    A = B ->
    Σ ;;; Γ |- t : B.
Proof.
  intros h []; assumption.
Qed.


(** ** Typechecking of global environments *)

Definition has_nparams npars ty :=
  decompose_prod_n_assum [] npars ty <> None.

Definition unlift_opt_pred (P : global_env_ext -> context -> option term -> term -> Type) :
  (global_env_ext -> context -> term -> term -> Type) :=
  fun Σ Γ t T => P Σ Γ (Some t) T.

(* Pattern definition
   TODO Find a suitable place

   This definition is relative to the number of pattern variables,
   and the number of bound variables introduced afterwards.

   TODO Can we have an "exact" pattern this way?

   TODO How to guarantee the tConstruct is fully applied?
   Maybe we don't have to.

   TODO Maybe constraint pattern_variable so the list is without duplicates.
*)
Inductive pattern (npat : nat) (nb : nat) : term -> Prop :=
| pattern_variable :
    forall n l,
      nb <= n ->
      n < npat + nb ->
      Forall (fun m => m < nb) l ->
      pattern npat nb (mkApps (tRel n) (map tRel l))

| pattern_bound :
    forall n,
      n < nb ->
      pattern npat nb (tRel n)

| pattern_lambda :
    forall na A t,
      pattern npat nb A ->
      pattern npat (S nb) t ->
      pattern npat nb (tLambda na A t)

| pattern_construct :
    forall ind n ui args,
      Forall (pattern npat nb) args ->
      pattern npat nb (mkApps (tConstruct ind n ui) args)

| pattern_symbol :
    forall k n ui args,
      Forall (pattern npat nb) args ->
      pattern npat nb (mkApps (tSymb k n ui) args)
.

Inductive elim_pattern (npat : nat) : elimination -> Prop :=
| pat_elim_App :
    forall p,
      pattern npat 0 p ->
      elim_pattern npat (eApp p)

| pat_elim_Case :
    forall indn p brs,
      pattern npat 0 p ->
      Forall (fun br => pattern npat 0 br.2) brs ->
      elim_pattern npat (eCase indn p brs)

| pat_elim_Proj :
    forall p,
      elim_pattern npat (eProj p).

(** Recognising pattern eliminations

  The goal is to know when some t is actually of the form
  subst0 s lhs.

  We assume the ss subst is already done in the elimination list.
*)

Definition option_assert (b : bool) : option () :=
  if b then ret tt else None.

(* Structure to build a substitution *)
Definition subs_empty npat : list (option term) :=
  list_make (fun _ => None) 0 npat.

(* Why do I need it again? *)
Import PCUICReflect.

Open Scope list_scope.

Definition subs_add x t (l : list (option term)) : option (list (option term)) :=
  match nth_error l x with
  | None => None
  | Some None => Some (firstn x l ++ Some t :: skipn (S x) l)
  | Some (Some t') => if eqb t t' then Some l else None
  end.

Definition subs_flatten (l : list (option term)) : option (list term) :=
  map_option_out l.

(** To deal with a partial substitution we consider all its complete extensions.
*)

Inductive subs_complete : list (option term) -> list term -> Prop :=
| subs_complete_nil : subs_complete [] []
| subs_complete_Some :
    forall a s s',
      subs_complete s s' ->
      subs_complete (Some a :: s) (a :: s')
| subs_complete_None :
    forall a s s',
      subs_complete s s' ->
      subs_complete (None :: s) (a :: s').

Lemma subs_complete_spec :
  forall s s',
    subs_complete s s' <->
    (#|s| = #|s'| /\
     forall n t, nth_error s n = Some (Some t) -> nth_error s' n = Some t).
Proof.
  intros s s'. split.
  - intro h. induction h.
    + split. 1: reflexivity.
      intros [] t e. all: discriminate.
    + cbn. destruct IHh as [el ih].
      split. 1: auto.
      intros [|n] t e.
      * cbn in *. apply some_inj in e. assumption.
      * cbn in *. eapply ih. assumption.
    + cbn. destruct IHh as [el ih].
      split. 1: auto.
      intros [|n] t e.
      * cbn in *. discriminate.
      * cbn in *. eapply ih. assumption.
  - intros [e h]. induction s in s', e, h |- *.
    + destruct s'. 2: discriminate.
      constructor.
    + destruct s'. 1: discriminate.
      cbn in e. destruct a.
      * specialize h with (n := 0) as h'.
        cbn in h'. specialize h' with (1 := eq_refl).
        apply some_inj in h'. subst.
        constructor.
        eapply IHs. 1: lia.
        intros n t hn.
        specialize h with (n := S n). cbn in h.
        eapply h. assumption.
      * constructor. eapply IHs. 1: lia.
        intros n ? hn.
        specialize h with (n := S n). cbn in h.
        eapply h. assumption.
Qed.

Lemma subs_complete_length :
  forall s s',
    subs_complete s s' ->
    #|s| = #|s'|.
Proof.
  intros s s' h.
  apply subs_complete_spec in h. apply h.
Qed.

Definition subs_init npat x t :=
  subs_add x t (subs_empty npat).

Fixpoint subs_merge (s1 s2 : list (option term)) : option (list (option term)) :=
  match s1, s2 with
  | [], [] => ret []
  | None :: s1, d :: s2
  | d :: s1, None :: s2 => s <- subs_merge s1 s2 ;; ret (d :: s)
  | Some t1 :: s1, Some t2 :: s2 =>
    option_assert (eqb t1 t2) ;;
    s <- subs_merge s1 s2 ;;
    ret (Some t1 :: s)
  | _, _ => None
  end.

(* Particular case of completion *)
Fixpoint subs_flatten_default (l : list (option term)) : list term :=
  match l with
  | [] => []
  | None :: l => tRel 0 :: subs_flatten_default l
  | Some t :: l => t :: subs_flatten_default l
  end.

Lemma subs_flatten_default_complete :
  forall s,
    subs_complete s (subs_flatten_default s).
Proof.
  intro s. induction s as [| [t|] s ih].
  - constructor.
  - cbn. constructor. assumption.
  - cbn. constructor. assumption.
Qed.

Lemma subs_flatten_default_length :
  forall s,
    #|subs_flatten_default s| = #|s|.
Proof.
  intro s. induction s as [| [t|] s ih].
  - reflexivity.
  - cbn. f_equal. assumption.
  - cbn. f_equal. assumption.
Qed.

Lemma subs_merge_complete :
  forall s1 s2 s,
    subs_merge s1 s2 = Some s ->
    forall s',
      subs_complete s s' ->
      subs_complete s1 s' /\ subs_complete s2 s'.
Proof.
  intros s1 s2 s e s' hs. induction hs in s1, s2, e |- *.
  - assert (h : s1 = [] /\ s2 = []).
    { induction s1 in s2, e |- *.
      - destruct s2.
        + intuition auto.
        + cbn in e. discriminate.
      - destruct a.
        + destruct s2. 1: discriminate.
          destruct o.
          * cbn in e. unfold eq_dec_to_bool in e.
            destruct eq_dec.
            2: discriminate.
            subst. cbn in e. destruct (subs_merge s1 s2) eqn: es.
            all: discriminate.
          * cbn in e. destruct (subs_merge s1 s2) eqn: es.
            all: discriminate.
        + cbn in e. destruct s2. 1: discriminate.
          destruct (subs_merge s1 s2) eqn: es. all: discriminate.
      }
      destruct h. subst. intuition constructor.
  - destruct s1, s2. all: try discriminate.
    1:{ cbn in e. destruct o. all: discriminate. }
    destruct o, o0.
    + cbn in e. unfold eq_dec_to_bool in e.
      destruct eq_dec. 2: discriminate.
      subst. cbn in e.
      destruct (subs_merge s1 s2) eqn: es. 2: discriminate.
      apply some_inj in e. inversion e. subst. clear e.
      eapply IHhs in es as [h1 h2].
      intuition (constructor ; auto).
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. 2: discriminate.
      apply some_inj in e. inversion e. subst. clear e.
      eapply IHhs in es as [h1 h2].
      intuition (constructor ; auto).
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. 2: discriminate.
      apply some_inj in e. inversion e. subst. clear e.
      eapply IHhs in es as [h1 h2].
      intuition (constructor ; auto).
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. all: discriminate.
  - destruct s1, s2. all: try discriminate.
    1:{ cbn in e. destruct o. all: discriminate. }
    destruct o, o0.
    + cbn in e. unfold eq_dec_to_bool in e. destruct eq_dec. 2: discriminate.
      cbn in e. destruct (subs_merge s1 s2) eqn: es. all: discriminate.
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. all: discriminate.
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. all: discriminate.
    + cbn in e. destruct (subs_merge s1 s2) eqn: es. 2: discriminate.
      inversion e. subst.
      eapply IHhs in es as [h1 h2].
      intuition (constructor ; auto).
Qed.

  (* Other direction *)
  (* - intro h. induction s1 in s2, s, h |- *.
    + assert (s = []).
      { specialize (h (subs_flatten_default s)).
        forward h.
        { apply subs_flatten_default_complete. }
        destruct h as [h _].
        apply subs_complete_length in h.
        destruct s. 1: reflexivity.
        rewrite subs_flatten_default_length in h.
        cbn in h. discriminate.
      } subst.
      specialize (h []). forward h by constructor.
      destruct h as [_ h].
      destruct s2. 1: reflexivity.
      apply subs_complete_length in h. discriminate.
    +
Admitted. *)

Lemma subs_init_nth_error :
  forall npat n t s,
    subs_init npat n t = Some s ->
    nth_error s n = Some (Some t).
Proof.
  intros npat n t s.
  unfold subs_init. unfold subs_add.
  destruct nth_error eqn:e1. 2: discriminate.
  destruct o.
  - exfalso.
    unfold subs_empty in e1. revert e1.
    generalize 0. intros m e.
    induction n in m, npat, e |- *.
    + cbn in e. destruct npat.
      * cbn in e. discriminate.
      * cbn in e. discriminate.
    + cbn in e. destruct npat.
      * cbn in e. discriminate.
      * cbn in e. eapply IHn. eassumption.
  - intro e. apply some_inj in e. subst.
    rewrite nth_error_app_ge.
    { eapply firstn_le_length. }
    assert (e : #|firstn n (subs_empty npat)| = n).
    { apply nth_error_Some_length in e1.
      rewrite -> firstn_length. lia.
    }
    rewrite e. replace (n - n) with 0 by lia. cbn. reflexivity.
Qed.

Definition option_map_def {A B : Set}
  (tf bf : A -> option B) (d : def A) : option (def B) :=
  ty <- tf d.(dtype) ;;
  bo <- bf d.(dbody) ;;
  ret {|
    dname := d.(dname) ;
    dtype := ty ;
    dbody := bo ;
    rarg := d.(rarg)
  |}.

Definition option_on_snd {A B C : Type}
  (f : B -> option C) (p : A × B) : option (A × C) :=
  c <- f p.2 ;;
  ret (p.1, c).

Fixpoint strengthen n k t : option term :=
  match t with
  | tRel i =>
      if k + n <=? i then ret (tRel (i - n))
      else if k <=? i then None
      else ret (tRel i)
  | tEvar ev args =>
      args' <- monad_map (strengthen n k) args ;;
      ret (tEvar ev args')
  | tLambda na A t =>
      A' <- strengthen n k A ;;
      t' <- strengthen n (S k) t ;;
      ret (tLambda na A' t')

  | tApp u v =>
      u' <- strengthen n k u ;;
      v' <- strengthen n k v ;;
      ret (tApp u' v')

  | tProd na A B =>
      A' <- strengthen n k A ;;
      B' <- strengthen n (S k) B ;;
      ret (tProd na A' B')

  | tLetIn na b B t =>
      b' <- strengthen n k b ;;
      B' <- strengthen n k B ;;
      t' <- strengthen n (S k) t ;;
      ret (tLetIn na b' B' t')

  | tCase ind p c brs =>
      brs' <- monad_map (option_on_snd (strengthen n k)) brs ;;
      p' <- strengthen n k p ;;
      c' <- strengthen n k c ;;
      ret (tCase ind p' c' brs')

  | tProj p c =>
      c' <- strengthen n k c ;;
      ret (tProj p c')

  | tFix mfix idx =>
      let k' := (#|mfix| + k)%nat in
      mfix' <- monad_map (option_map_def (strengthen n k) (strengthen n k')) mfix ;;
      ret (tFix mfix' idx)

  | tCoFix mfix idx =>
      let k' := (#|mfix| + k)%nat in
      mfix' <- monad_map (option_map_def (strengthen n k) (strengthen n k')) mfix ;;
      ret (tCoFix mfix' idx)

  | x => ret x
  end.

Lemma strengthen_lift :
  forall n k t,
    strengthen n k (lift n k t) = Some t.
Proof.
  intros n k t.
  induction t using term_forall_list_ind in n, k |- *.
  all: simpl.
  all: rewrite ?IHt ?IHt1 ?IHt2 ?IHt3.
  all: try reflexivity.
  - destruct (Nat.leb_spec k n0).
    + simpl. destruct (Nat.leb_spec (k + n) (n + n0)). 2: lia.
      f_equal. f_equal. lia.
    + simpl. destruct (Nat.leb_spec (k + n) n0). 1: lia.
      destruct (Nat.leb_spec k n0). 1: lia.
      reflexivity.
  - match goal with
    | |- context [ monad_map ?f ?a ] =>
      assert (e : monad_map f a = Some l)
    end.
    { induction H. 1: reflexivity.
      cbn. rewrite p. rewrite IHAll. reflexivity.
    }
    rewrite e. reflexivity.
  - match goal with
    | |- context [ monad_map ?f ?a ] =>
      assert (e : monad_map f a = Some l)
    end.
    { induction X. 1: reflexivity.
      cbn. rewrite p0. rewrite IHX. destruct x. reflexivity.
    }
    rewrite e. reflexivity.
  - match goal with
    | |- context [ monad_map ?f ?a ] =>
      assert (e : monad_map f a = Some m)
    end.
    { rewrite map_length. generalize #|m|. intro p.
      induction X. 1: reflexivity.
      cbn. destruct p0 as [h1 h2].
      rewrite h1. rewrite h2. rewrite IHX. destruct x. reflexivity.
    }
    rewrite e. reflexivity.
  - match goal with
    | |- context [ monad_map ?f ?a ] =>
      assert (e : monad_map f a = Some m)
    end.
    { rewrite map_length. generalize #|m|. intro p.
      induction X. 1: reflexivity.
      cbn. destruct p0 as [h1 h2].
      rewrite h1. rewrite h2. rewrite IHX. destruct x. reflexivity.
    }
    rewrite e. reflexivity.
Qed.

Lemma option_monad_map_length :
  forall A B f l l',
    @monad_map option _ A B f l = ret l' ->
    #|l| = #|l'|.
Proof.
  intros A B f l l' e.
  induction l in l', e |- *.
  - cbn in e. apply some_inj in e. subst. reflexivity.
  - cbn in e. destruct (f a) eqn: e1. 2: discriminate.
    destruct (monad_map f l) eqn: e2. 2: discriminate.
    apply some_inj in e. subst. cbn. f_equal.
    eapply IHl. reflexivity.
Qed.

Lemma strengthen_inv :
  forall n k t u,
    strengthen n k t = Some u ->
    t = lift n k u.
Proof.
  intros n k t u h.
  induction t using term_forall_list_ind in n, k, u, h |- *.
  all: simpl in h.
  all:
    repeat match type of h with
    | context [ monad_map ?f ?l ] =>
      let e := fresh "e" in
      destruct (monad_map f l) eqn: e ; [| discriminate ]
    end.
  all:
    repeat match type of h with
    | context [ strengthen ?n ?k ?t ] =>
      let e := fresh "e" in
      destruct (strengthen n k t) eqn:e ; [
        idtac
      | discriminate
      ]
    end.
  all: try (apply some_inj in h ; subst ; cbn).
  all:
    repeat match goal with
    | ih : _ -> _ -> _ -> _ -> ?t = _, e : strengthen ?k ?n ?t = _ |- _ =>
      eapply ih in e ; subst
    end.
  all: try reflexivity.
  - destruct (Nat.leb_spec (k + n) n0).
    + apply some_inj in h. subst. cbn.
      destruct (Nat.leb_spec k (n0 - n)). 2: lia.
      f_equal. lia.
    + destruct (Nat.leb_spec k n0). 1: discriminate.
      apply some_inj in h. subst. cbn.
      destruct (Nat.leb_spec k n0). 1: lia.
      reflexivity.
  - f_equal.
    induction H in l0, e |- *.
    + cbn in e. apply some_inj in e. subst. reflexivity.
    + cbn in e. destruct (strengthen n k x) eqn:ex. 2: discriminate.
      destruct (monad_map (strengthen n k) l) eqn:el. 2: discriminate.
      eapply p in ex. subst.
      specialize (IHAll _ eq_refl). subst.
      apply some_inj in e. subst. reflexivity.
  - f_equal. induction X in l0, e |- *.
    + cbn in e. apply some_inj in e. subst. reflexivity.
    + cbn in e. destruct x. simpl in *.
      repeat match type of e with
      | context [ strengthen ?n ?k ?t ] =>
        let e := fresh "e" in
        destruct (strengthen n k t) eqn:e ; [
          idtac
        | discriminate
        ]
      end.
      repeat match type of e with
      | context [ monad_map ?f ?l ] =>
        let e := fresh "e" in
        destruct (monad_map f l) eqn: e ; [| discriminate ]
      end.
      apply some_inj in e. subst. cbn.
      repeat match goal with
      | ih : _ -> _ -> _ -> _ -> ?t = _, e : strengthen ?k ?n ?t = _ |- _ =>
        eapply ih in e ; subst
      end.
      unfold on_snd. cbn. f_equal.
      eapply IHX.
      reflexivity.
  - f_equal.
    apply option_monad_map_length in e as el. rewrite <- el. clear el.
    revert e.
    generalize #|m|. intros q e.
    induction X in q, l, e |- *.
    + cbn in e. apply some_inj in e. subst. reflexivity.
    + cbn in e.
      repeat match type of e with
      | context [ strengthen ?n ?k ?t ] =>
        let e := fresh "e" in
        destruct (strengthen n k t) eqn:e ; [
          idtac
        | discriminate
        ]
      end.
      repeat match type of e with
      | context [ monad_map ?f ?l ] =>
        let e := fresh "e" in
        destruct (monad_map f l) eqn: e ; [| discriminate ]
      end.
      apply some_inj in e. subst. cbn.
      destruct p. destruct x. simpl in *.
      repeat match goal with
      | ih : _ -> _ -> _ -> _ -> ?t = _, e : strengthen ?k ?n ?t = _ |- _ =>
        eapply ih in e ; subst
      end.
      unfold map_def. cbn. f_equal.
      eapply IHX. assumption.
  - f_equal.
    apply option_monad_map_length in e as el. rewrite <- el. clear el.
    revert e.
    generalize #|m|. intros q e.
    induction X in q, l, e |- *.
    + cbn in e. apply some_inj in e. subst. reflexivity.
    + cbn in e.
      repeat match type of e with
      | context [ strengthen ?n ?k ?t ] =>
        let e := fresh "e" in
        destruct (strengthen n k t) eqn:e ; [
          idtac
        | discriminate
        ]
      end.
      repeat match type of e with
      | context [ monad_map ?f ?l ] =>
        let e := fresh "e" in
        destruct (monad_map f l) eqn: e ; [| discriminate ]
      end.
      apply some_inj in e. subst. cbn.
      destruct p. destruct x. simpl in *.
      repeat match goal with
      | ih : _ -> _ -> _ -> _ -> ?t = _, e : strengthen ?k ?n ?t = _ |- _ =>
        eapply ih in e ; subst
      end.
      unfold map_def. cbn. f_equal.
      eapply IHX. assumption.
Qed.

Fixpoint option_map2 {A B C}
  (f : A -> B -> option C) (l1 : list A) (l2 : list B) : option (list C) :=
  match l1, l2 with
  | [], [] => ret []
  | x :: l1, y :: l2 =>
      z <- f x y ;;
      l <- option_map2 f l1 l2 ;;
      ret (z :: l)
  | _, _ => None
  end.

Require PCUICSize.

Equations rec_pattern_discr
  (p : term) (pl : list term) (t : term) (tl : list term) : Prop :=
  rec_pattern_discr (tRel n) pl t tl := False ;
  rec_pattern_discr (tLambda na A t) [] (tLambda na' A' t') [] := False ;
  rec_pattern_discr (tConstruct ind n ui) pl (tConstruct ind' n' ui') tl := False ;
  rec_pattern_discr (tSymb k n ui) pl (tSymb k' n' ui') tl := False ;
  rec_pattern_discr _ _ _ _ := True.

Inductive rec_pattern_view : term -> list term -> term -> list term -> Set :=
| rec_pattern_rel n pl t tl :
    rec_pattern_view (tRel n) pl t tl

| rec_pattern_lam na A t na' A' t' :
    rec_pattern_view (tLambda na A t) [] (tLambda na' A' t') []

| rec_pattern_construct ind n ui args ind' n' ui' args' :
    rec_pattern_view (tConstruct ind n ui) args (tConstruct ind' n' ui') args'

| rec_pattern_symb k n ui args k' n' ui' args' :
    rec_pattern_view (tSymb k n ui) args (tSymb k' n' ui') args'

| rec_pattern_other :
    forall p pl t tl,
      rec_pattern_discr p pl t tl ->
      rec_pattern_view p pl t tl.

Equations rec_pattern_viewc p pl t tl : rec_pattern_view p pl t tl :=
  rec_pattern_viewc (tRel n) pl t tl :=
    rec_pattern_rel n pl t tl ;

  rec_pattern_viewc (tLambda na A t) [] (tLambda na' A' t') [] :=
    rec_pattern_lam na A t na' A' t' ;

  rec_pattern_viewc (tConstruct ind n ui) args (tConstruct ind' n' ui') args' :=
    rec_pattern_construct ind n ui args ind' n' ui' args' ;

  rec_pattern_viewc (tSymb k n ui) args (tSymb k' n' ui') args' :=
    rec_pattern_symb k n ui args k' n' ui' args' ;

  rec_pattern_viewc p pl t tl :=
    rec_pattern_other p pl t tl I.

(* TODO Duplicate *)
Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

Inductive decompose_app_view : term -> Set :=
| is_apps t l (e : isApp t = false) : decompose_app_view (mkApps t l).

Equations decompose_app_viewc t : decompose_app_view t :=
  decompose_app_viewc t with inspect (decompose_app t) := {
  | @exist (u,l) e := _
  }.
Next Obligation.
  symmetry in e.
  apply decompose_app_inv in e as e'.
  apply decompose_app_notApp in e as h. subst.
  constructor. assumption.
Defined.

Program Fixpoint wf_option_map2 {A B C} {m : A -> nat} {y}
  (f : forall x : A, B -> m x < y -> option C) (l1 : list A) (l2 : list B)
  {h : Forall (fun x => m x < y) l1}
  : option (list C) :=
  match l1, l2 with
  | [], [] => ret []
  | x :: l1, y :: l2 =>
      z <- f x y _ ;;
      l <- wf_option_map2 f l1 l2 ;;
      ret (z :: l)
  | _, _ => None
  end.
Next Obligation.
  inversion h. assumption.
Qed.
Next Obligation.
  inversion h. assumption.
Qed.
Next Obligation.
  split.
  - intros. intro. intuition auto. discriminate.
  - intro. intuition auto. discriminate.
Qed.
Next Obligation.
  split.
  - intros. intro. intuition auto. discriminate.
  - intro. intuition auto. discriminate.
Qed.

(* Print Assumptions wf_option_map2. *)

Equations rec_pattern (npat nb : nat) (p t : term) : option (list (option term))
  by wf (PCUICSize.size p) lt :=

  rec_pattern npat nb p t with decompose_app_viewc p := {
  | is_apps u args e1 with decompose_app_viewc t := {
    | is_apps v args' e2 with rec_pattern_viewc u args v args' := {
      | rec_pattern_rel n pl t tl :=
          if n <? nb then
            match pl with
            | [] =>
              if eqb (mkApps t tl) (tRel n)
              then ret (subs_empty npat)
              else None
            | _ => None
            end
          else if n <? npat + nb then
            let nargs := #|tl| - #|pl| in
            let l := skipn nargs tl in
            if eqb pl l then
              t' <- strengthen nb 0 (mkApps t (firstn nargs tl)) ;;
              subs_init npat (n - nb) t'
            else None
          else None ;

      | rec_pattern_lam na A b na' A' b' :=
          option_assert (eqb na na') ;;
          s1 <- rec_pattern npat nb A A' ;;
          s2 <- rec_pattern npat (S nb) b b' ;;
          subs_merge s1 s2 ;

      | rec_pattern_construct ind n ui args ind' n' ui' args' :=
          option_assert (eqb ind ind' && eqb n n' && eqb ui ui') ;;
          sl <- wf_option_map2
                  (m := PCUICSize.size)
                  (y := PCUICSize.size (mkApps (tConstruct ind n ui) args))
                  (fun p t h => rec_pattern npat nb p t) args args' ;;
          monad_fold_left (subs_merge) sl (subs_empty npat) ;

      | rec_pattern_symb k n ui args k' n' ui' args' :=
          option_assert (eqb k k' && eqb n n' && eqb ui ui') ;;
          sl <- wf_option_map2
                  (m := PCUICSize.size)
                  (y := PCUICSize.size (mkApps (tSymb k n ui) args))
                  (fun p t h => rec_pattern npat nb p t) args args' ;;
          monad_fold_left (subs_merge) sl (subs_empty npat) ;

      | rec_pattern_other p pl t tl _ := None
      }
    }
  }.
(* Solve All Obligations with lia. *)
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.
Next Obligation.
  clear.
  rewrite mkApps_size. cbn. induction args. 1: constructor.
  cbn. constructor.
  - lia.
  - eapply Forall_impl. 1: eassumption.
    intros. lia.
Qed.
Next Obligation.
  clear.
  rewrite mkApps_size. cbn. induction args. 1: constructor.
  cbn. constructor.
  - lia.
  - eapply Forall_impl. 1: eassumption.
    intros. lia.
Qed.

Fixpoint isAppRel (t : term) : bool :=
  match t with
  | tRel n => true
  | tApp t u => isAppRel t
  | _ => false
  end.

Lemma isAppRel_mkApps :
  forall t l,
    isAppRel (mkApps t l) = isAppRel t.
Proof.
  intros t l. induction l in t |- *. 1: reflexivity.
  cbn. rewrite IHl. reflexivity.
Qed.

Lemma mkApps_Rel_inj :
  forall n m l l',
    mkApps (tRel n) l = mkApps (tRel m) l' ->
    n = m /\ l = l'.
Proof.
  intros n m l l' e.
  induction l in n, m, l', e |- * using list_ind_rev.
  - destruct l'.
    + cbn in e. inversion e. auto.
    + cbn in e. apply (f_equal nApp) in e. cbn in e.
      rewrite nApp_mkApps in e. cbn in e. discriminate.
  - rewrite <- mkApps_nested in e. cbn in e.
    destruct l' using list_ind_rev.
    + cbn in e. discriminate.
    + rewrite <- mkApps_nested in e. cbn in e.
      inversion e. eapply IHl in H0. intuition auto.
      subst. reflexivity.
Qed.

Fixpoint isAppLambda (t : term) : bool :=
  match t with
  | tLambda na A t => true
  | tApp t u => isAppLambda t
  | _ => false
  end.

Lemma isAppLambda_mkApps :
  forall t l,
    isAppLambda (mkApps t l) = isAppLambda t.
Proof.
  intros t l. induction l in t |- *. 1: reflexivity.
  cbn. rewrite IHl. reflexivity.
Qed.

Fixpoint isAppConstruct (t : term) : bool :=
  match t with
  | tConstruct ind n ui => true
  | tApp t u => isAppConstruct t
  | _ => false
  end.

Lemma isAppConstruct_mkApps :
  forall t l,
    isAppConstruct (mkApps t l) = isAppConstruct t.
Proof.
  intros t l. induction l in t |- *. 1: reflexivity.
  cbn. rewrite IHl. reflexivity.
Qed.

Lemma mkApps_Construct_inj :
  forall ind n ui ind' n' ui' l l',
    mkApps (tConstruct ind n ui) l = mkApps (tConstruct ind' n' ui') l' ->
    ind = ind' /\ n = n' /\ ui = ui' /\ l = l'.
Proof.
  intros ind n ui ind' n' ui' l l' e.
  induction l in ind, n, ui, ind', n', ui', l', e |- * using list_ind_rev.
  - destruct l'.
    + cbn in e. inversion e. auto.
    + cbn in e. apply (f_equal nApp) in e. cbn in e.
      rewrite nApp_mkApps in e. cbn in e. discriminate.
  - rewrite <- mkApps_nested in e. cbn in e.
    destruct l' using list_ind_rev.
    + cbn in e. discriminate.
    + rewrite <- mkApps_nested in e. cbn in e.
      inversion e. eapply IHl in H0. intuition auto.
      subst. reflexivity.
Qed.

Lemma mkApps_lift_inv :
  forall t l n k u,
    mkApps t l = lift n k u ->
    ∑ t' l',
      u = mkApps t' l' /\
      t = lift n k t' /\
      l = map (lift n k) l'.
Proof.
  intros t l n k u e.
  induction l in t, n, k, u, e |- * using list_rect_rev.
  - cbn in e. subst. exists u, []. intuition auto.
  - rewrite <- mkApps_nested in e. cbn in e.
    destruct u. all: cbn in e. all: try discriminate.
    1:{ destruct (k <=? n0). all: discriminate. }
    inversion e. subst.
    eapply IHl in H0 as [t' [l' ?]].
    intuition eauto. subst.
    eexists _, (_ ++ [_]).
    rewrite <- mkApps_nested. cbn.
    rewrite map_app. cbn.
    intuition eauto.
Qed.

Lemma rec_pattern_sound :
  forall npat nb p t s,
    pattern npat nb p ->
    rec_pattern npat nb p t = Some s ->
    forall s', subs_complete s s' -> t = subst s' nb p.
Proof.
  intros npat nb p t s hp.
  funelim (rec_pattern npat nb p t).
  - inversion hp.
    all: try solve [
      apply (f_equal isAppRel) in H ;
      rewrite !isAppRel_mkApps in H ;
      discriminate
    ].
    + apply mkApps_Rel_inj in H as [? ?]. subst.
      destruct (Nat.ltb_spec n nb). 1: lia.
      destruct (Nat.ltb_spec n (npat + nb)). 2: lia.
      match goal with
      | |- context [ eqb ?u ?v ] =>
        destruct (eqb_spec u v)
      end.
      2: discriminate.
      match goal with
      | |- context [ strengthen ?n ?k ?t ] =>
        destruct (strengthen n k t) eqn:es
      end.
      2: discriminate.
      cbn. intros h s' hs.
      rewrite subst_mkApps.
      apply strengthen_inv in es.
      apply mkApps_lift_inv in es as [t' [l' [? [? el]]]]. subst.
      cbn. destruct (Nat.leb_spec nb n). 2: lia.
      apply subs_init_nth_error in h as h'.
      apply subs_complete_spec in hs as [sl hs'].
      apply hs' in h'.
      rewrite h'.
      rewrite lift_mkApps. rewrite mkApps_nested. f_equal.
      rewrite <- el. erewrite <- (firstn_skipn _ tl0) at 1.
      f_equal. rewrite <- e1. clear - H2.
      induction H2 in |- *. 1: reflexivity.
      cbn. destruct (Nat.leb_spec nb x). 1: lia.
      f_equal. assumption.
    + destruct pl using list_rect_rev.
      2:{ rewrite <- mkApps_nested in H. cbn in H. discriminate. }
      cbn in H. inversion H. subst. clear H.
      destruct (Nat.ltb_spec n nb). 2: lia.
      destruct (eqb_spec (mkApps t tl0) (tRel n)). 2: discriminate.
      destruct tl0 using list_rect_rev.
      2:{ rewrite <- mkApps_nested in e1. cbn in e1. discriminate. }
      cbn in e1. subst. cbn.
      intro e1. apply some_inj in e1. subst.
      destruct (Nat.leb_spec nb n). 1: lia.
      reflexivity.
  - cbn in hp. inversion hp.
    all: try solve [
      apply (f_equal isAppLambda) in H1 ;
      rewrite !isAppLambda_mkApps in H1 ;
      discriminate
    ]. subst.
    destruct (eqb_spec na na'). 2: discriminate.
    subst. simpl.
    destruct (rec_pattern npat nb A A') eqn:eA. 2: discriminate.
    specialize (H tt _ H3 eq_refl).
    destruct (rec_pattern npat (S nb) t2 t') eqn:et. 2: discriminate.
    specialize (H0 tt [] _ H5 eq_refl).
    intros es s' hs.
    eapply subs_merge_complete in es as es'.
    2: eassumption.
    destruct es' as [h1 h2].
    eapply H in h1. eapply H0 in h2. subst.
    reflexivity.
  - inversion hp.
    all: try solve [
      apply (f_equal isAppConstruct) in H1 ;
      rewrite !isAppConstruct_mkApps in H1 ;
      discriminate
    ].
    apply mkApps_Construct_inj in H1 as [? [? [? ?]]]. subst.
    repeat match goal with
    | |- context [ eqb ?x ?y ] =>
      destruct (eqb_spec x y) ; [| discriminate]
    end. subst.
    cbn.
    match goal with
    | |- context [ wf_option_map2 ?f ?l1 ?l2 ] =>
      destruct (wf_option_map2 f l1 l2) eqn:e2 ; [| discriminate]
    end.
    intros e3 s' hs.
    rewrite subst_mkApps. cbn. f_equal.
    rewrite mkApps_size in H. cbn in H.
    assert (ih :
      forall p t,
        PCUICSize.size p < S (list_size PCUICSize.size args) ->
        forall s,
          pattern npat nb p ->
          rec_pattern npat nb p t = Some s ->
          forall s',
            subs_complete s s' ->
            t = subst s' nb p
    ).
    { clear - H.
      intros p t si s hp e s' hs.
      specialize H with (1 := tt) (4 := eq_refl).
      eapply H. all: eauto.
    }
    clear H H0.
    induction H2 in args', l, e2, e3, s', hs, ih |- *.
    + destruct args'. 1: reflexivity.
      cbn in e2. discriminate.
    + cbn. destruct args'. 1: discriminate.
      cbn in e2.
      match type of e2 with
      | context [ rec_pattern ?npat ?nb ?p ?t ] =>
        destruct (rec_pattern npat nb p t) eqn:e4 ; [| discriminate]
      end.
      match type of e2 with
      | context [ wf_option_map2 ?f ?l1 ?l2 ] =>
        destruct (wf_option_map2 f l1 l2) eqn:e5 ; [| discriminate]
      end.
      apply some_inj in e2. subst.
      cbn in e3.
      match type of e3 with
      | context [ subs_merge ?s1 ?s2 ] =>
        destruct (subs_merge s1 s2) eqn:e6 ; [| discriminate]
      end.
      cbn in ih.
      f_equal.
      * admit.
      * eapply IHForall. all: eauto.
Abort.

(* Fixpoint rec_elim (e : elimination) (t : term) : option ? :=
  match e, t with
  | eApp p, tApp u v =>

Fixpoint rec_lhs
  (npat : nat) (k : kername) (n : nat) (ui : universe_instance)
  (l : list elimination) (t : term) : option (list term) :=


Lemma rec_lhs_spec :
  forall npat k n ui l t,
    Forall (elim_pattern npat) l ->
    rec_lhs npat k n ui l t = Some s <->
    t = subst0 s (mkElims (tSymb k n ui) l). *)

Module PCUICTypingDef <: Typing PCUICTerm PCUICEnvironment PCUICEnvTyping.

  Definition subst := @subst.
  Definition subst_context := @subst_context.
  Definition symbols_subst := @symbols_subst.
  Definition context_env_clos := @context_env_clos.
  Definition untyped_subslet := @untyped_subslet.
  Definition ind_guard := ind_guard.
  Definition red := @red.
  Definition typing := @typing.
  Definition smash_context := smash_context.
  Definition elim_pattern := elim_pattern.

End PCUICTypingDef.

Module PCUICDeclarationTyping :=
  DeclarationTyping
    PCUICTerm
    PCUICEnvironment
    PCUICEnvTyping
    PCUICTypingDef
    PCUICLookup.
Include PCUICDeclarationTyping.

Definition typing_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) : size.
Proof.
  revert Σ Γ t T d.
  fix typing_size 5.
  destruct 1 ;
    repeat match goal with
           | H : typing _ _ _ _ |- _ => apply typing_size in H
           end;
    match goal with
    | H : All2 _ _ _ |- _ => idtac
    | H : All_local_env _ _ |- _ => idtac
    | H : All _ _ |- _ => idtac
    | H : _ + _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
    | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
    | H1 : size |- _  => exact (S H1)
    | _ => exact 1
    end.
  exact (S (wf_local_size _ typing_size _ a)).
  exact (S (wf_local_size _ typing_size _ a)).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (S (wf_local_size _ typing_size _ a))).
  exact (S (Nat.max d1 (Nat.max d2
                                (all2_size _ (fun x y p => Nat.max (typing_size Σ Γ (snd x) (snd y) (snd (fst p))) (typing_size _ _ _ _ (snd p))) a)))).
  exact (S (Nat.max (wf_local_size _ typing_size _ a) (all_size _ (fun x p => typing_size Σ _ _ _ (fst p)) a0))).
  exact (S (Nat.max (wf_local_size _ typing_size _ a) (all_size _ (fun x p => typing_size Σ _ _ _ p) a0))).
  destruct s. red in i.
  exact (S (Nat.max (wf_local_size _ typing_size _ (snd (projT2 (projT2 i)))) d)).
  destruct s as [u Hu]. apply typing_size in Hu.
  exact (S (Nat.max d Hu)).
Defined.

Lemma typing_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) : typing_size d > 0.
Proof.
  induction d; simpl; try lia. destruct s as [s | [u Hu]]; try lia.
Qed.

Fixpoint globenv_size (Σ : global_env) : size :=
  match Σ with
  | [] => 1
  | d :: Σ => S (globenv_size Σ)
  end.

(** To get a good induction principle for typing derivations,
     we need:
    - size of the global_env_ext, including size of the global declarations in it
    - size of the derivation. *)

Arguments lexprod [A B].

Definition wf `{checker_flags} := Forall_decls_typing typing.
Definition wf_ext `{checker_flags} := on_global_env_ext (lift_typing typing).

Lemma wf_ext_wf {cf:checker_flags} Σ : wf_ext Σ -> wf Σ.
Proof. intro H; apply H. Qed.

Hint Resolve wf_ext_wf.

Lemma wf_ext_consistent {cf:checker_flags} Σ :
  wf_ext Σ -> consistent Σ.
Proof.
  intros [? [? [? [? ?]]]]; assumption.
Qed.

Hint Resolve wf_ext_consistent.


Definition env_prop `{checker_flags} (P : forall Σ Γ t T, Type) :=
  forall Σ (wfΣ : wf Σ.1) Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t : T ->
    Forall_decls_typing P Σ.1 * P Σ Γ t T.

Lemma env_prop_typing `{checker_flags} P : env_prop P ->
  forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t T : term),
    Σ ;;; Γ |- t : T -> P Σ Γ t T.
Proof. intros. now apply X. Qed.

Lemma type_Prop `{checker_flags} Σ : Σ ;;; [] |- tSort Universe.type0m : tSort Universe.type1.
  repeat constructor.
  apply prop_global_ext_levels.
Defined.

Lemma env_prop_sigma `{checker_flags} P : env_prop P ->
  forall Σ (wfΣ : wf Σ), Forall_decls_typing P Σ.
Proof.
  intros. red in X. eapply (X (empty_ext Σ)).
  apply wfΣ. constructor.
  apply type_Prop.
Defined.

Lemma wf_local_app `{checker_flags} Σ (Γ Γ' : context) : wf_local Σ (Γ ,,, Γ') -> wf_local Σ Γ.
Proof.
  induction Γ'. auto.
  simpl. intros H'; inv H'; eauto.
Defined.
Hint Resolve wf_local_app : wf.

Lemma typing_wf_local `{checker_flags} {Σ} {Γ t T} :
  Σ ;;; Γ |- t : T -> wf_local Σ Γ.
Proof.
  induction 1; eauto using wf_local_app.
Defined.
Hint Resolve typing_wf_local : wf.

Derive Signature for All_local_env.

Set Equations With UIP.
Derive NoConfusion for context_decl.
Derive NoConfusion for list.
Derive NoConfusion for All_local_env.

Lemma size_wf_local_app `{checker_flags} {Σ} (Γ Γ' : context) (Hwf : wf_local Σ (Γ ,,, Γ')) :
  wf_local_size Σ (@typing_size _) _ (wf_local_app _ _ _ Hwf) <=
  wf_local_size Σ (@typing_size _) _ Hwf.
Proof.
  induction Γ' in Γ, Hwf |- *; try lia. simpl. lia.
  depelim Hwf.
  - inversion H0. subst. noconf H4. simpl. unfold eq_rect_r. simpl. specialize (IHΓ' _ Hwf). lia.
  - inversion H0. subst. noconf H4. specialize (IHΓ' _ Hwf). simpl. unfold eq_rect_r. simpl. lia.
Qed.

Lemma typing_wf_local_size `{checker_flags} {Σ} {Γ t T}
      (d :Σ ;;; Γ |- t : T) :
  wf_local_size Σ (@typing_size _) _ (typing_wf_local d) < typing_size d.
Proof.
  induction d; simpl; try lia.
  - destruct indnpar as [ind' npar']; cbn in *; subst ind npar. lia.
  - pose proof (size_wf_local_app _ _ a).
    eapply Nat.le_lt_trans. eauto. subst types. lia.
  - pose proof (size_wf_local_app _ _ a).
    eapply Nat.le_lt_trans. eauto. subst types. lia.
  - destruct s as [s | [u Hu]]; try lia.
Qed.

Lemma wf_local_inv `{checker_flags} {Σ Γ'} (w : wf_local Σ Γ') :
  forall d Γ,
    Γ' = d :: Γ ->
    ∑ w' : wf_local Σ Γ,
      match d.(decl_body) with
      | Some b =>
        ∑ u (ty : Σ ;;; Γ |- b : d.(decl_type)),
          { ty' : Σ ;;; Γ |- d.(decl_type) : tSort u |
            wf_local_size Σ (@typing_size _) _ w' <
            wf_local_size _ (@typing_size _) _ w /\
            typing_size ty <= wf_local_size _ (@typing_size _) _ w /\
            typing_size ty' <= wf_local_size _ (@typing_size _) _ w }

      | None =>
        ∑ u,
          { ty : Σ ;;; Γ |- d.(decl_type) : tSort u |
            wf_local_size Σ (@typing_size _) _ w' <
            wf_local_size _ (@typing_size _) _ w /\
            typing_size ty <= wf_local_size _ (@typing_size _) _ w }
      end.
Proof.
  intros d Γ.
  destruct w.
  - simpl. congruence.
  - intros [=]. subst d Γ0.
    exists w. simpl. destruct l. exists x. exists t0. pose (typing_size_pos t0).
    simpl. split.
    + lia.
    + auto with arith.
  - intros [=]. subst d Γ0.
    exists w. simpl. simpl in l. destruct l as [u h].
    simpl in l0.
    exists u, l0, h. simpl.
    pose (typing_size_pos h).
    pose (typing_size_pos l0).
    intuition eauto.
    all: try lia.
    auto with arith.
Qed.

Derive Signature for Alli.

(** *** An induction principle ensuring the Σ declarations enjoy the same properties.
    Also theads the well-formedness of the local context and the induction principle for it,
    and gives the right induction hypothesis
    on typing judgments in application spines, fix and cofix blocks.
 *)

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_env_ext -> context -> term -> term -> Type)
         (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T),
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (l : Level.t),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        LevelSet.In l (global_ext_levels Σ) ->
        P Σ Γ (tSort (Universe.make l)) (tSort (Universe.super l))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term) (s1 s2 : universe),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (t b : term)
            (s1 : universe) (bty : term),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n t bty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : name) (b b_ty b' : term)
            (s1 : universe) (b'_ty : term),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ ;;; Γ |- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) na A B u,
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- t : tProd na A B -> P Σ Γ t (tProd na A B) ->
        Σ ;;; Γ |- u : A -> P Σ Γ u A ->
        P Σ Γ (tApp t u) (B{0 := u})) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (k : ident) (n : nat) u decl ty,
        Forall_decls_typing P Σ.1 ->
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        declared_symbol Σ.1 k decl ->
        nth_error decl.(symbols) n = Some ty ->
        consistent_instance_ext Σ decl.(rew_universes) u ->
        P Σ Γ (tSymb k n u) (subst (symbols_subst k (S n) u #|decl.(symbols)|) 0 (subst_instance_constr u ty))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (cst : ident) u (decl : constant_body),
        Forall_decls_typing P Σ.1 ->
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance_constr u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
        Forall_decls_typing P Σ.1 ->
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance_constr u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 mdecl idecl (ind, i) cdecl),
        Forall_decls_typing P Σ.1 ->
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u (npar : nat)
            (p c : term) (brs : list (nat * term))
            (args : list term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
            (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
        Forall_decls_typing P Σ.1 -> All_local_env_over typing Pdecl Σ Γ wfΓ ->
        ind_npars mdecl = npar ->
        let params := firstn npar args in
        forall ps pty, build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
        Σ ;;; Γ |- p : pty ->
        P Σ Γ p pty ->
        existsb (leb_sort_family (universe_family ps)) idecl.(ind_kelim) ->
        Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
        P Σ Γ c (mkApps (tInd ind u) args) ->
        forall btys, map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
        All2 (fun br bty => (br.1 = bty.1) *
                         (Σ ;;; Γ |- br.2 : bty.2) * P Σ Γ br.2 bty.2 *
                         (Σ ;;; Γ |- bty.2 : tSort ps) * P Σ Γ bty.2 (tSort ps))
             brs btys ->
        P Σ Γ (tCase (ind, npar) p c brs) (mkApps p (skipn npar args ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl pdecl (isdecl : declared_projection Σ.1 mdecl idecl p pdecl) args,
        Forall_decls_typing P Σ.1 -> All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
        P Σ Γ c (mkApps (tInd (fst (fst p)) u) args) ->
        #|args| = ind_npars mdecl ->
        let ty := snd pdecl in P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance_constr u ty))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        nth_error mfix n = Some decl ->
        fix_guard mfix ->
        All_local_env (lift_typing (fun Σ Γ b ty =>
                         (typing Σ Γ b ty * P Σ Γ b ty)%type) Σ) (Γ ,,, types) ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
                   (isLambda d.(dbody) = true)%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        nth_error mfix n = Some decl ->
        All_local_env (lift_typing (fun Σ Γ b ty => (typing Σ Γ b ty * P Σ Γ b ty)%type) Σ) (Γ ,,, types) ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
        allow_cofix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term),
        All_local_env_over typing Pdecl Σ Γ wfΓ ->
        Σ ;;; Γ |- t : A ->
        P Σ Γ t A ->
        (isWfArity_prop typing Pdecl Σ Γ B + {s & (Σ ;;; Γ |- B : tSort s) * P Σ Γ B (tSort s)})%type ->
        Σ ;;; Γ |- A <= B ->
        P Σ Γ t B) ->

       env_prop P.
Proof.
  intros P Pdecl; unfold env_prop.
  intros X X0 X1 X2 X3 X4 XSymb X5 X6 X7 X8 X9 X10 X11 X12 Σ wfΣ Γ wfΓ t T H.
  (* NOTE (Danil): while porting to 8.9, I had to split original "pose" into 2 pieces,
   otherwise it takes forever to execure the "pose", for some reason *)
  pose (@Fix_F ({ Σ : _ & { wfΣ : wf Σ.1 & { Γ : context & { wfΓ : wf_local Σ Γ &
                          { t : term & { T : term & Σ ;;; Γ |- t : T }}}}}})) as p0.
  specialize (p0 (dlexprod (MR lt (fun Σ => globenv_size (fst Σ)))
                            (fun Σ => MR lt (fun x => typing_size (projT2 (projT2 (projT2 (projT2 (projT2 x))))))))) as p.
  set(foo := existT _ Σ (existT _ wfΣ (existT _ Γ (existT _ wfΓ (existT _ t (existT _ _ H))))) : { Σ : _ & { wfΣ : wf Σ.1 & { Γ : context & { wfΓ & { t : term & { T : term & Σ ;;; Γ |- t : T }}}}}}).
  change Σ with (projT1 foo).
  change Γ with (projT1 (projT2 (projT2 foo))).
  change t with (projT1 (projT2 (projT2 (projT2 (projT2 foo))))).
  change T with (projT1 (projT2 (projT2 (projT2 (projT2 (projT2 foo)))))).
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply wf_dlexprod; intros; apply measure_wf; apply lt_wf].
  clear p.
  clear Σ wfΣ Γ wfΓ t T H.
  intros (Σ & wfΣ & Γ & wfΓ & t & t0 & H). simpl.
  intros IH. unfold MR in IH. simpl in IH.
  split.
  destruct Σ as [Σ φ]. destruct Σ.
  constructor.
  cbn in wfΣ; inversion_clear wfΣ. auto.
  inv wfΣ.
  rename X14 into Xg.
  constructor; auto. unfold Forall_decls_typing in IH.
  - simple refine (let IH' := IH ((Σ, udecl); (X13; []; _; (tSort Universe.type0m ); _; _)) in _).
    constructor. shelve. apply type_Prop.
    cbn in IH'; forward IH'. constructor 1; cbn. lia.
    apply IH'; auto.
  - simpl. simpl in *.
    destruct d; simpl.
    + destruct c; simpl in *.
      destruct cst_body; simpl in *.
      simpl.
      intros. red in Xg. simpl in Xg.
      specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ localenv_nil (existT _ _ (existT _ _ Xg))))))).
      simpl in IH.
      forward IH. constructor 1. simpl; lia.
      apply IH.
      red. simpl. red in Xg; simpl in Xg.
      destruct Xg as [s Hs]. red. simpl.
      specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ localenv_nil (existT _ _ (existT _ _ Hs))))))).
      simpl in IH.
      forward IH. constructor 1. simpl; lia. exists s. eapply IH.
    + red in Xg.
      destruct Xg as [onI onP onnp]; constructor; eauto.
      eapply Alli_impl; eauto. clear onI onP onnp; intros n x Xg.
      refine {| ind_indices := Xg.(ind_indices);
                ind_arity_eq := Xg.(ind_arity_eq);
                ind_ctors_sort := Xg.(ind_ctors_sort) |}.
      ++ apply onArity in Xg. destruct Xg as [s Hs]. exists s; auto.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ localenv_nil (existT _ _ (existT _ _ Hs))))))).
         simpl in IH. simpl. apply IH; constructor 1; simpl; lia.
      ++ pose proof Xg.(onConstructors) as Xg'.
         eapply All2_impl; eauto. intros.
         red in X14 |- *. destruct X14 as [[s Hs] [cs Hargsu]]. split.
         pose proof (typing_wf_local (Σ:= (Σ, udecl)) Hs). simpl in Hs.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ X14 (existT _ _ (existT _ _ Hs))))))).
         simpl in IH. red. simpl. exists s. simpl. apply IH; constructor 1; simpl; auto with arith.
         exists cs.
         eapply type_local_ctx_impl; eauto. simpl. intros. red in X14.
         destruct T.
         pose proof (typing_wf_local X14).
         specialize (IH ((Σ, udecl); (X13; _; X17; _; _; X14))).
         apply IH. simpl. constructor 1. simpl. auto with arith.
         destruct X14 as [u Hu]. exists u.
         pose proof (typing_wf_local Hu).
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ X14 (existT _ _ (existT _ _ Hu))))))).
         apply IH. simpl. constructor 1. simpl. auto with arith.
      ++ intros Hprojs; pose proof (onProjections Xg Hprojs); auto. simpl in *.
         destruct X14; constructor; auto. eapply Alli_impl; eauto. clear on_projs0. intros.
         red in X14 |- *. unfold on_type in *; intuition eauto. simpl in *.
         destruct X14 as [s Hs]. exists s.
         pose proof (typing_wf_local (Σ:= (Σ, udecl)) Hs).
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ X14 (existT _ _ (existT _ _ Hs))))))).
         simpl in IH. apply IH; constructor 1; simpl; lia.
      ++ destruct Xg. simpl. unfold check_ind_sorts in *.
         destruct universe_family; auto.
         +++ split. apply ind_sorts0. destruct indices_matter; auto.
             eapply type_local_ctx_impl. eapply ind_sorts0.
             intros. red in X14.
             destruct T.
             pose proof (typing_wf_local X14).
             specialize (IH ((Σ, udecl); (X13; _; X17; _; _; X14))).
             apply IH. simpl. constructor 1. simpl. auto with arith.
             destruct X14 as [u Hu]. exists u.
             pose proof (typing_wf_local Hu).
             specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ X14 (existT _ _ (existT _ _ Hu))))))).
             apply IH. simpl. constructor 1. simpl. auto with arith.
         +++ split. apply ind_sorts0. destruct indices_matter; auto.
             eapply type_local_ctx_impl. eapply ind_sorts0.
             intros. red in X14.
             destruct T.
             pose proof (typing_wf_local X14).
             specialize (IH ((Σ, udecl); (X13; _; X17; _; _; X14))).
             apply IH. simpl. constructor 1. simpl. auto with arith.
             destruct X14 as [u Hu]. exists u.
             pose proof (typing_wf_local Hu).
             specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ X14 (existT _ _ (existT _ _ Hu))))))).
             apply IH. simpl. constructor 1. simpl. auto with arith.
      ++ red in onP |- *.
         eapply All_local_env_impl; eauto.
         intros. destruct T; simpl in X14.
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ (typing_wf_local (Σ:=(Σ, udecl)) X14)
                                                                           (existT _ _ (existT _ _ X14))))))).
         simpl in IH. apply IH. constructor 1. simpl. lia.
         destruct X14 as [u Hu].
         specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ (typing_wf_local (Σ:=(Σ, udecl)) Hu)
                                                                           (existT _ _ (existT _ _ Hu))))))).
         simpl in IH. simpl. exists u. apply IH. constructor 1. simpl. lia.
    + red in Xg. destruct Xg as [hctx [hr [hpr hprr]]].
      split. 2: split.
      * eapply All_local_env_impl. 1: eassumption.
        intros Δ u T h. destruct T. all: simpl in h. all: simpl.
        -- specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ (typing_wf_local (Σ := (Σ, udecl)) h) (existT _ _ (existT _ _ h))))))).
          simpl in IH. apply IH. constructor 1. simpl. lia.
        -- destruct h as [s h].
           specialize (IH (existT _ (Σ, udecl) (existT _ X13 (existT _ _ (existT _ (typing_wf_local (Σ:=(Σ, udecl)) h)
            (existT _ _ (existT _ _ h))))))).
           simpl in IH. simpl. exists s. apply IH.
           constructor 1. simpl. lia.
      * eapply All_impl. 1: eassumption.
        intros rw [T onlhs onrhs onhead onelims].
        exists T.
        -- match type of IH with
           | ?T -> _ =>
             unshelve epose (y := _ : T)
           end.
           ++ exists (Σ, udecl). exists X13.
              unshelve eexists _, _, _, _.
              5: exact onlhs.
              eapply typing_wf_local. eassumption.
           ++ specialize (IH y). subst y. simpl in IH.
              apply IH. constructor 1. simpl. lia.
        -- match type of IH with
           | ?T -> _ =>
             unshelve epose (y := _ : T)
           end.
           ++ exists (Σ, udecl). exists X13.
              unshelve eexists _, _, _, _.
              5: exact onrhs.
              eapply typing_wf_local. eassumption.
           ++ specialize (IH y). subst y. simpl in IH.
              apply IH. constructor 1. simpl. lia.
        -- assumption.
        -- assumption.
      * split.
        -- eapply All_impl. 1: exact hpr.
           intros rw [T onlhs onrhs onhead onelims].
           exists T.
           ++ match type of IH with
              | ?T -> _ =>
                unshelve epose (y := _ : T)
              end.
              ** exists (Σ, udecl). exists X13.
                  unshelve eexists _, _, _, _.
                  5: exact onlhs.
                  eapply typing_wf_local. eassumption.
              ** specialize (IH y). subst y. simpl in IH.
                  apply IH. constructor 1. simpl. lia.
           ++ match type of IH with
              | ?T -> _ =>
                unshelve epose (y := _ : T)
              end.
              ** exists (Σ, udecl). exists X13.
                  unshelve eexists _, _, _, _.
                  5: exact onrhs.
                  eapply typing_wf_local. eassumption.
              ** specialize (IH y). subst y. simpl in IH.
                  apply IH. constructor 1. simpl. lia.
           ++ assumption.
           ++ assumption.
        -- eapply All_impl. 1: exact hprr.
           cbn. intros rw h. auto.

  - assert (forall Γ (wfΓ : wf_local Σ Γ) t T (Hty : Σ ;;; Γ |- t : T),
               typing_size Hty < typing_size H ->
               Forall_decls_typing P Σ.1 * P Σ Γ t T).
    intros.
    specialize (IH (existT _ Σ (existT _ wfΣ (existT _ _ (existT _ wfΓ0 (existT _ _ (existT _ _ Hty))))))).
    simpl in IH.
    forward IH.
    constructor 2. simpl. apply H0.
    apply IH. clear IH.
    rename X13 into X14.

    assert (All_local_env_over typing Pdecl Σ Γ (typing_wf_local H)).
    { clear -Pdecl wfΓ wfΣ X14.
      pose proof (typing_wf_local_size H). clear wfΓ.
      set (foo := typing_wf_local H) in *.
      clearbody foo.
      revert foo H0. generalize Γ at 1 2 4.
      induction foo; simpl in *; try destruct t2 as [u Hu]; simpl in *; constructor.
      - simpl in *. apply IHfoo. lia.
      - red. eapply (X14 _ foo _ _ Hu). lia.
      - simpl in *. apply IHfoo. lia.
      - red. apply (X14 _ foo _ _ t3). lia.
      - red. apply (X14 _ foo _ _ Hu). lia. }

    destruct H;
      try solve [  match reverse goal with
                     H : _ |- _ => eapply H
                   end; eauto;
                   unshelve eapply X14; simpl; auto with arith].

    -- match reverse goal with
         H : _ |- _ => eapply H
       end; eauto;
         unshelve eapply X14; simpl; eauto with arith wf.

    -- match reverse goal with
         H : _ |- _ => eapply H
       end; eauto;
         unshelve eapply X14; simpl; auto with arith.
       econstructor; simpl; eauto.

    -- match reverse goal with
         H : _ |- _ => eapply H
       end.
       all: eauto.
       ++ unshelve eapply X14. all: eauto. simpl. lia.
       ++ unshelve eapply X14. all: eauto. simpl. lia.
       ++ unshelve eapply X14. all: eauto.
          ** econstructor ; eauto. eexists ; eauto.
          ** simpl. lia.

    -- eapply XSymb. all: eauto.
      specialize (X14 [] localenv_nil _ _ (type_Prop _)).
      simpl in X14. forward X14; auto. lia. apply X14.

    -- eapply X5; eauto. simpl in X14.
       specialize (X14 [] localenv_nil _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. lia. apply X14.

    -- eapply X6; eauto. simpl in X14.
       specialize (X14 [] localenv_nil _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. lia. apply X14.

    -- eapply X7; eauto.
       specialize (X14 [] localenv_nil _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. lia. apply X14.

    -- destruct indnpar as [ind' npar'];
         cbn in ind; cbn in npar; subst ind; subst npar.
       eapply X8; eauto.
       ++ eapply (X14 _ wfΓ _ _ H); eauto. simpl; auto with arith.
       ++ eapply (X14 _ wfΓ _ _ H); eauto. simpl; auto with arith.
       ++ simpl in *.
          eapply (X14 _ wfΓ _ _ H0); eauto. clear. lia.
       ++ clear X13. revert a wfΓ X14. simpl. clear. intros.
          induction a; simpl in *.
          ** constructor.
          ** destruct r as [[? ?] ?]. constructor.
             --- intuition eauto.
                 +++ eapply (X14 _ wfΓ _ _ t); eauto. simpl; auto with arith.
                     lia.
                 +++ eapply (X14 _ wfΓ _ _ t0); eauto. simpl; auto with arith.
                     lia.
             --- apply IHa. auto. intros.
                 eapply (X14 _ wfΓ0 _ _ Hty). lia.

    -- eapply X9; eauto.
       specialize (X14 [] localenv_nil _ _ (type_Prop _)).
       simpl in X14. forward X14; auto. pose (typing_size_pos H). lia. apply X14.
       unshelve eapply X14; eauto.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X11 X12.
       eapply X10; eauto; clear X10. simpl in *. subst types.
       remember (Γ ,,, fix_context mfix) as Γ'.
       assert( forall Γ : context,
                 wf_local Σ Γ ->
                 forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                   typing_size Hty <
                   S ((wf_local_size Σ
                       (fun x (x0 : context) (x1 x2 : term) (x3 : x;;; x0 |- x1 : x2) =>
                          typing_size x3) Γ' a)) ->
                   Forall_decls_typing P Σ.1 * P Σ Γ t T).
       intros; eauto. eapply (X14 _ X _ _ Hty); eauto. lia.
       clear X14 a0.
       clear HeqΓ'. clear X13. revert Γ wfΓ.
       induction a; simpl in *; try econstructor; eauto.
       eapply IHa; eauto. intros. eapply (X _ X0 _ _ Hty); simpl; eauto. lia.
       --- simpl. destruct t0. exists x. split; eauto.
           eapply (X _ a _ _ t0); eauto. simpl. lia.
       --- eapply IHa. intros. eapply (X _ X0 _ _ Hty) ; eauto. lia. eapply a.
       --- simpl. destruct t0 as [u t0].
           exists u. split ; eauto.
           unshelve eapply X. all: eauto. simpl. lia.
       --- simpl. split ; eauto.
           unshelve eapply X. all: eauto. simpl. lia.
       --- simpl in X14.
           assert(forall Γ0 : context,
                wf_local Σ Γ0 ->
               forall (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                typing_size Hty <
                      S
                        (all_size (fun x : def term => (Σ;;; Γ ,,, fix_context mfix |- dbody x : lift0 #|types| (dtype x))%type
                                                        * (isLambda (dbody x) = true)%type)%type
                                   (fun (x : def term) p => typing_size (fst p)) a0) ->
                       Forall_decls_typing P Σ.1 * P Σ Γ0 t T).
           subst types. intros. eapply (X14 _ X _ _ Hty); eauto. lia. clear X14.
           subst types.
           remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.
           clear e decl X13. clear i.
           induction a0; econstructor; eauto.
       ++ split; auto.
          eapply (X _ a _ _ (fst p)). simpl. lia.
       ++ eapply IHa0. intros.
          eapply (X _ X0 _ _ Hty). simpl; lia.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X12 X13.
       eapply X11; eauto; clear X11. simpl in *. subst types.
       remember (Γ ,,, fix_context mfix) as Γ'.
       assert( forall Γ : context,
                 wf_local Σ Γ ->
                 forall (t T : term) (Hty : Σ;;; Γ |- t : T),
                   typing_size Hty <
                   S
                     (
                       (wf_local_size Σ
                                      (fun x (x0 : context) (x1 x2 : term) (x3 : x;;; x0 |- x1 : x2) =>
                                         typing_size x3) Γ' a)) ->

                   Forall_decls_typing P Σ.1 * P Σ Γ t T).
       intros; eauto. eapply (X14 _ X _ _ Hty); eauto. lia.
       clear X14 a0.
       clear HeqΓ'. revert Γ wfΓ.
       induction a; simpl in *; try econstructor; eauto.
       eapply IHa; eauto. intros. eapply (X _ X0 _ _ Hty); simpl; eauto. lia.
       --- destruct t0. exists x. split; eauto.
           eapply (X _ a _ _ t0); eauto. simpl; lia.
       --- eapply IHa. intros. eapply (X _ X0 _ _ Hty) ; eauto. lia. eapply a.
       --- simpl. destruct t0 as [u t0].
           exists u. split ; eauto.
           unshelve eapply X. all: eauto. simpl. lia.
       --- simpl. split ; eauto.
           unshelve eapply X. all: eauto. simpl. lia.
       --- simpl in X14.
           assert(forall Γ0 : context,
                     wf_local Σ Γ0 ->
                     forall (t T : term) (Hty : Σ;;; Γ0 |- t : T),
                       typing_size Hty <
                       S (all_size (fun x : def term => Σ;;; Γ ,,, fix_context mfix |- dbody x : (lift0 #|types| (dtype x)))
                                   (fun (x : def term) (p : Σ;;; Γ ,,, fix_context mfix |- dbody x : (lift0 #|types| (dtype x))) => typing_size p) a0) ->
                       Forall_decls_typing P Σ.1 * P Σ Γ0 t T).
           intros. eapply (X14 _ X _ _ Hty); eauto. subst types; lia. clear X14.
           subst types.
           remember (fix_context mfix) as mfixcontext. clear Heqmfixcontext.
           clear e decl.
           induction a0; econstructor; eauto.
       ++ split; auto.
          eapply (X _ a _ _ p). simpl. lia.
       ++ eapply IHa0. intros.
         eapply (X _ X0 _ _ Hty). simpl; lia.
    -- eapply X12; eauto.
       ++ eapply (X14 _ wfΓ _ _ H); simpl. destruct s as [s | [u Hu]]; lia.
       ++ simpl in X14, X13.
          destruct s as [s | [u Hu]].
          ** left.
             red. exists s. red in s. revert X14.
             generalize (snd (projT2 (projT2 s))).
             induction a; simpl in *; intros X14 *; constructor.
             --- apply IHa. intros. eapply (X14 _ wfΓ0 _ _ Hty). lia.
             --- red. eapply (X14 _ a _ _ (projT2 t1)). destruct t1. simpl. lia.
             --- apply IHa. intros. eapply (X14 _ wfΓ0 _ _ Hty). lia.
             --- red. destruct t1. unshelve eapply X14. all: eauto.
                 simpl. lia.
             --- red. destruct t1. unshelve eapply X14. all: eauto.
                 simpl. lia.
          ** right.
             exists u. intuition eauto. unshelve eapply X14. all: eauto. lia.
Qed.
Print Assumptions typing_ind_env.


Ltac my_rename_hyp h th :=
  match th with
  | (wf ?E) => fresh "wf" E
  | (wf (fst_ctx ?E)) => fresh "wf" E
  | (wf _) => fresh "wf"
  | (typing _ _ ?t _) => fresh "type" t
  | (@cumul _ _ _ ?t _) => fresh "cumul" t
  | (conv _ _ ?t _) => fresh "conv" t
  | (All_local_env (lift_typing (@typing _) _) ?G) => fresh "wf" G
  | (All_local_env (lift_typing (@typing _) _) _) => fresh "wf"
  | (All_local_env _ _ ?G) => fresh "H" G
  | context [typing _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.


Section All_local_env.
  (** * Lemmas about All_local_env *)

  Context {cf: checker_flags}.

  Lemma nth_error_All_local_env {P Γ n} (isdecl : n < #|Γ|) :
    All_local_env P Γ ->
    on_some (on_local_decl P (skipn (S n) Γ)) (nth_error Γ n).
  Proof.
    induction 1 in n, isdecl |- *. red; simpl.
    - destruct n; simpl; inv isdecl.
    - destruct n. red; simpl. red. simpl. apply t0.
      simpl. apply IHX. simpl in isdecl. lia.
    - destruct n. auto.
      apply IHX. simpl in *. lia.
  Qed.

  Lemma lookup_on_global_env P Σ c decl :
    on_global_env P Σ ->
    lookup_env Σ c = Some decl ->
    { Σ' & { wfΣ' : on_global_env P Σ'.1 & on_global_decl P Σ' c decl } }.
  Proof.
    induction 1; simpl. congruence.
    destruct (ident_eq_spec c kn); subst.
    intros [= ->].
    exists (Σ, udecl). exists X. auto.
    apply IHX.
  Qed.

  Lemma All_local_env_app (P : context -> term -> option term -> Type) l l' :
    All_local_env P (l ,,, l') ->
    All_local_env P l * All_local_env (fun Γ t T => P (l ,,, Γ) t T) l'.
  Proof.
    induction l'; simpl; split; auto.
    - constructor.
    - unfold app_context in X.
      inv X.
      + intuition auto.
      + apply IHl'. auto.
    - inv X.
      + eapply localenv_cons_abs.
        * apply IHl'. apply X0.
        * apply X1.
      + eapply localenv_cons_def.
        * apply IHl'. apply X0.
        * apply X1.
        * apply X2.
  Qed.

  Definition wf_local_rel_app {Σ Γ1 Γ2 Γ3} :
    wf_local_rel Σ Γ1 (Γ2 ,,, Γ3) ->
    wf_local_rel Σ Γ1 Γ2 * wf_local_rel Σ (Γ1 ,,, Γ2) Γ3.
  Proof.
    intros h. apply All_local_env_app in h as [h1 h2].
    split.
    - exact h1.
    - eapply All_local_env_impl. 1: exact h2.
      intros Γ t [T|] h.
      all: cbn in *.
      all: change PCUICEnvironment.app_context with app_context in *.
      all: rewrite <- app_context_assoc.
      all: auto.
  Defined.


  Lemma All_local_env_lookup {P Γ n} {decl} :
    All_local_env P Γ ->
    nth_error Γ n = Some decl ->
    on_local_decl P (skipn (S n) Γ) decl.
  Proof.
    induction 1 in n, decl |- *. simpl. destruct n; simpl; congruence.
    destruct n. red. simpl. intros [= <-]. simpl. apply t0.
    simpl in *. eapply IHX.
    destruct n. simpl. intros [= <-]. auto.
    eapply IHX.
  Qed.

  Lemma All_local_env_app_inv (P : context -> term -> option term -> Type) l l' :
    All_local_env P l * All_local_env (fun Γ t T => P (l ,,, Γ) t T) l' ->
    All_local_env P (l ,,, l').
  Proof.
    induction l'; simpl; auto. intuition.
    intuition. destruct a. destruct decl_body.
    inv b. econstructor; eauto. inv b; econstructor; eauto. Qed.


  Definition wf_local_rel_app_inv {Σ Γ1 Γ2 Γ3} :
    wf_local_rel Σ Γ1 Γ2 -> wf_local_rel Σ (Γ1 ,,, Γ2) Γ3
    -> wf_local_rel Σ Γ1 (Γ2 ,,, Γ3).
  Proof.
    intros h1 h2. eapply All_local_env_app_inv.
    split.
    - assumption.
    - eapply All_local_env_impl.
      + eassumption.
      + change PCUICEnvironment.app_context with app_context.
        intros Γ t []; cbn;
        now rewrite app_context_assoc.
  Defined.


  Lemma All_local_env_map (P : context -> term -> option term -> Type) f l :
    (forall u, f (tSort u) = tSort u) ->
    All_local_env (fun Γ t T => P (map (map_decl f) Γ) (f t) (option_map f T)) l
    -> All_local_env P (map (map_decl f) l).
  Proof.
    intros Hf. induction 1; econstructor; eauto.
  Qed.

  Definition property :=
    forall (Σ : global_env_ext) (Γ : context),
      All_local_env (lift_typing typing Σ) Γ -> forall t T : term, typing Σ Γ t T -> Type.

  Definition lookup_wf_local {Γ P} (wfΓ : All_local_env P Γ) (n : nat)
             (isdecl : n < #|Γ|) :
    All_local_env P (skipn (S n) Γ).
  Proof.
    induction wfΓ in n, isdecl |- *; simpl. constructor.
    cbn -[skipn] in *. destruct n.
    simpl. exact wfΓ.
    apply IHwfΓ. auto with arith.
    destruct n. exact wfΓ.
    apply IHwfΓ. auto with arith.
  Defined.

  Definition on_local_decl_glob (P : term -> option term -> Type) d :=
    match d.(decl_body) with
    | Some b => (P b (Some d.(decl_type)) * P d.(decl_type) None)%type
    | None => P d.(decl_type) None
    end.

  Definition lookup_wf_local_decl {Γ P} (wfΓ : All_local_env P Γ) (n : nat)
             {decl} (eq : nth_error Γ n = Some decl) :
    ∑ Pskip : All_local_env P (skipn (S n) Γ),
             on_local_decl_glob (P (skipn (S n) Γ)) decl.
  Proof.
    induction wfΓ in n, decl, eq |- *; simpl.
    - elimtype False. destruct n; depelim eq.
    - destruct n.
      + simpl. exists wfΓ. injection eq; intros <-. apply t0.
      + apply IHwfΓ. auto with arith.
    - destruct n.
      + exists wfΓ. injection eq; intros <-.
        simpl. split; auto.
      + apply IHwfΓ. apply eq.
  Defined.

  Definition on_wf_local_decl {Σ Γ}
             (P : forall Σ Γ (wfΓ : wf_local Σ Γ) t T, Σ ;;; Γ |- t : T -> Type)
             (wfΓ : wf_local Σ Γ) {d} (H : on_local_decl_glob (lift_typing typing Σ Γ) d) :=
    match d as d' return (on_local_decl_glob (lift_typing typing Σ Γ) d') -> Type with
    | {| decl_name := na; decl_body := Some b; decl_type := ty |} =>
      fun H => (P Σ Γ wfΓ b ty H.1 * P Σ Γ wfΓ _ _ (projT2 (snd H)))%type
    | {| decl_name := na; decl_body := None; decl_type := ty |} => fun H => P Σ Γ wfΓ _ _ (projT2 H)
    end H.

  Lemma nth_error_All_local_env_over {P Σ Γ n decl} (eq : nth_error Γ n = Some decl) {wfΓ : All_local_env (lift_typing typing Σ) Γ} :
    All_local_env_over typing P Σ Γ wfΓ ->
    let Γ' := skipn (S n) Γ in
    let p := lookup_wf_local_decl wfΓ n eq in
    (All_local_env_over typing P Σ Γ' (projT1 p) * on_wf_local_decl P (projT1 p) (projT2 p))%type.
  Proof.
    induction 1 in n, decl, eq |- *. simpl.
    - destruct n; simpl; elimtype False; discriminate eq.
    - destruct n. cbn [skipn]. noconf eq. split. apply X. simpl. apply p.
      simpl. apply IHX.
    - destruct n. noconf eq. simpl. split; auto.
      apply IHX.
  Defined.

  Lemma All_local_env_prod_inv :
    forall P Q Γ,
      All_local_env (fun Δ A t => P Δ A t × Q Δ A t) Γ ->
      All_local_env P Γ × All_local_env Q Γ.
  Proof.
    intros P Q Γ h.
    induction h.
    - split ; constructor.
    - destruct IHh, t0.
      split ; constructor ; auto.
    - destruct IHh, t0, t1.
      split ; constructor ; auto.
  Qed.

  Lemma All_local_env_lift_prod_inv :
    forall Σ P Q Δ,
      All_local_env (lift_typing (fun Σ Γ t A => P Σ Γ t A × Q Σ Γ t A) Σ) Δ ->
      All_local_env (lift_typing P Σ) Δ × All_local_env (lift_typing Q Σ) Δ.
  Proof.
    intros Σ P Q Δ h.
    induction h.
    - split ; constructor.
    - destruct IHh. destruct t0 as [? [? ?]].
      split ; constructor ; auto.
      + cbn. eexists. eassumption.
      + cbn. eexists. eassumption.
    - destruct IHh. destruct t0 as [? [? ?]]. destruct t1.
      split ; constructor ; auto.
      + cbn. eexists. eassumption.
      + cbn. eexists. eassumption.
  Qed.

End All_local_env.
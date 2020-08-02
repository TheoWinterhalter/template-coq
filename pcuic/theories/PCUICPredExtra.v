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

Local Set Keyed Unification.
Set Asymmetric Patterns.

(* All the rewrite rules of a rewrite_decl *)
Definition all_rewrite_rules (rd : rewrite_decl) :=
  rd.(prules) ++ rd.(rules).

Section ParallelReductionExtra.

  Context (Σ : global_env).

  (* Potential extra rules, might be redundant *)
  Context (extra : option (kername × rewrite_decl)).

  Inductive pred1_extra (Γ : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | predx_beta na t0 t1 b0 b1 a0 a1 :
      pred1_extra Γ t0 t1 ->
      pred1_extra (Γ ,, vass na t0) b0 b1 ->
      pred1_extra Γ a0 a1 ->
      pred1_extra Γ (tApp (tLambda na t0 b0) a0) (subst10 a1 b1)

  (** Let *)
  | predx_zeta na d0 d1 t0 t1 b0 b1 :
      pred1_extra Γ t0 t1 ->
      pred1_extra Γ d0 d1 ->
      pred1_extra (Γ ,, vdef na d0 t0) b0 b1 ->
      pred1_extra Γ (tLetIn na d0 t0 b0) (subst10 d1 b1)

  (** Local variables *)
  | predx_rel_def_unfold i body :
      option_map decl_body (nth_error Γ i) = Some (Some body) ->
      pred1_extra Γ (tRel i) (lift0 (S i) body)

  | predx_rel_refl i :
      pred1_extra Γ (tRel i)  (tRel i)

  (** Case *)
  | predx_iota ind pars c u args0 args1 p brs0 brs1 :
      All2 (pred1_extra Γ) args0 args1 ->
      All2 (on_Trel_eq (pred1_extra Γ) snd fst) brs0 brs1 ->
      pred1_extra Γ (tCase (ind, pars) p
        (mkApps (tConstruct ind c u) args0) brs0)
        (iota_red pars c args1 brs1)

  (** Fix unfolding, with guard *)
  | predx_fix mfix0 mfix1 idx args0 args1 narg fn :
      All2 (fun x y =>
        pred1_extra Γ x.(dtype) y.(dtype) ×
        pred1_extra (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
        (dname x, rarg x) = (dname y, rarg y)
      ) mfix0 mfix1 ->
      unfold_fix mfix1 idx = Some (narg, fn) ->
      is_constructor narg args0 = true ->
      All2 (pred1_extra Γ) args0 args1 ->
      pred1_extra Γ (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)

  (** CoFix-case unfolding *)
  | predx_cofix_case ip p0 p1 mfix0 mfix1 idx args0 args1 narg fn brs0 brs1 :
      All2 (fun x y =>
        pred1_extra Γ x.(dtype) y.(dtype) ×
        pred1_extra (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
        (dname x, rarg x) = (dname y, rarg y)
      ) mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1_extra Γ) args0 args1 ->
      pred1_extra Γ p0 p1 ->
      All2 (on_Trel_eq (pred1_extra Γ) snd fst) brs0 brs1 ->
      pred1_extra Γ
        (tCase ip p0 (mkApps (tCoFix mfix0 idx) args0) brs0)
        (tCase ip p1 (mkApps fn args1) brs1)

  (** CoFix-proj unfolding *)
  | predx_cofix_proj p mfix0 mfix1 idx args0 args1 narg fn :
      All2 (fun x y =>
        pred1_extra Γ x.(dtype) y.(dtype) ×
        pred1_extra (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
        (dname x, rarg x) = (dname y, rarg y)
      ) mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1_extra Γ) args0 args1 ->
      pred1_extra Γ
        (tProj p (mkApps (tCoFix mfix0 idx) args0))
        (tProj p (mkApps fn args1))

  (** Symbols and rewrite rules  *)

  | predx_symb k n u :
      pred1_extra Γ (tSymb k n u) (tSymb k n u)

  | predx_rewrite_rule k ui decl n r s s' :
      declared_symbol Σ k decl ->
      nth_error decl.(rules) n = Some r ->
      All2 (pred1_extra Γ) s s' ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let lhs := subst0 s (subst ss #|s| (lhs r)) in
      let rhs := subst0 s' (subst ss #|s| (rhs r)) in
      pred1_extra Γ lhs rhs

  | predx_par_rewrite_rule k ui decl n r s s' :
      declared_symbol Σ k decl ->
      nth_error decl.(prules) n = Some r ->
      All2 (pred1_extra Γ) s s' ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let lhs := subst0 s (subst ss #|s| (lhs r)) in
      let rhs := subst0 s' (subst ss #|s| (rhs r)) in
      pred1_extra Γ lhs rhs

  | predx_extra_rewrite_rule k ui decl n r s s' :
      extra = Some (k, decl) →
      nth_error (all_rewrite_rules decl) n = Some r ->
      All2 (pred1_extra Γ) s s' ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let lhs := subst0 s (subst ss #|s| (lhs r)) in
      let rhs := subst0 s' (subst ss #|s| (rhs r)) in
      pred1_extra Γ lhs rhs

  (** Constant unfolding *)

  | predx_delta c decl body (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = Some body ->
      pred1_extra Γ (tConst c u) (subst_instance_constr u body)

  | predx_const c u :
      pred1_extra Γ (tConst c u) (tConst c u)

  (** Proj *)
  | predx_proj i pars narg k u args0 args1 arg1 :
      All2 (pred1_extra Γ) args0 args1 ->
      nth_error args1 (pars + narg) = Some arg1 ->
      pred1_extra Γ
        (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0))
        arg1

  (** Congruences *)
  | predx_abs na M M' N N' :
      pred1_extra Γ M M' ->
      pred1_extra (Γ ,, vass na M) N N' ->
      pred1_extra Γ (tLambda na M N) (tLambda na M' N')

  | predx_app M0 M1 N0 N1 :
      pred1_extra Γ M0 M1 ->
      pred1_extra Γ N0 N1 ->
      pred1_extra Γ (tApp M0 N0) (tApp M1 N1)

  | predx_letin na d0 d1 t0 t1 b0 b1 :
      pred1_extra Γ  d0 d1 ->
      pred1_extra Γ t0 t1 ->
      pred1_extra (Γ ,, vdef na d0 t0) b0 b1 ->
      pred1_extra Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)

  | predx_case ind p0 p1 c0 c1 brs0 brs1 :
      pred1_extra Γ p0 p1 ->
      pred1_extra Γ c0 c1 ->
      All2 (on_Trel_eq (pred1_extra Γ) snd fst) brs0 brs1 ->
      pred1_extra Γ (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)

  | predx_proj_congr p c c' :
      pred1_extra Γ c c' ->
      pred1_extra Γ (tProj p c) (tProj p c')

  | predx_fix_congr mfix0 mfix1 idx :
      All2 (fun x y =>
        pred1_extra Γ x.(dtype) y.(dtype) ×
        pred1_extra (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
        (dname x, rarg x) = (dname y, rarg y)
      ) mfix0 mfix1 ->
      pred1_extra Γ (tFix mfix0 idx) (tFix mfix1 idx)

  | predx_cofix_congr mfix0 mfix1 idx :
      All2 (fun x y =>
        pred1_extra Γ x.(dtype) y.(dtype) ×
        pred1_extra (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
        (dname x, rarg x) = (dname y, rarg y)
      ) mfix0 mfix1 ->
      pred1_extra Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

  | predx_prod na M0 M1 N0 N1 :
      pred1_extra Γ M0 M1 ->
      pred1_extra (Γ ,, vass na M0) N0 N1 ->
      pred1_extra Γ (tProd na M0 N0) (tProd na M1 N1)

  | evar_pred ev l l' :
      All2 (pred1_extra Γ) l l' ->
      pred1_extra Γ (tEvar ev l) (tEvar ev l')

  | predx_atom_refl t :
      pred_atom t ->
      pred1_extra Γ t t.

  Lemma All2_impl_def :
    ∀ {A B} {P Q : A → B → Type} (l : list A) (l' : list B),
      All2 P l l' →
      (∀ x y, P x y → Q x y) →
      All2 Q l l'.
  Proof.
    intros A B P Q l l' hl h.
    induction hl. 1: constructor.
    constructor.
    - eapply h. assumption.
    - assumption.
  Defined.

  Lemma pred1_extra_ind_all_ctx :
    forall (P : forall (Γ : context) (t t0 : term), Type)
           (* (Pctx : forall (Γ : context), Type) *),
      let P' Γ x y := ((pred1_extra Γ x y) × P Γ x y)%type in
      (* (forall Γ, All2_local_env (on_decl pred1_extra) Γ Γ' -> All2_local_env (on_decl P) Γ Γ' -> Pctx Γ Γ') -> *)
      (forall (Γ : context) (na : name) (t0 t1 b0 b1 a0 a1 : term),
          pred1_extra (Γ ,, vass na t0) b0 b1 ->
          P (Γ ,, vass na t0) b0 b1 ->
          pred1_extra Γ t0 t1 -> P Γ t0 t1 ->
          pred1_extra Γ a0 a1 -> P Γ a0 a1 ->
          P Γ (tApp (tLambda na t0 b0) a0) (b1 {0 := a1})
      ) ->
      (forall (Γ : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1_extra Γ t0 t1 -> P Γ t0 t1 ->
          pred1_extra Γ d0 d1 -> P Γ d0 d1 ->
          pred1_extra (Γ ,, vdef na d0 t0) b0 b1 ->
          P (Γ ,, vdef na d0 t0) b0 b1 ->
          P Γ (tLetIn na d0 t0 b0) (b1 {0 := d1})
      ) ->
      (forall (Γ : context) (i : nat) (body : term),
          option_map decl_body (nth_error Γ i) = Some (Some body) ->
          P Γ (tRel i) (lift0 (S i) body)
      ) ->
      (forall (Γ : context) (i : nat),
          P Γ (tRel i) (tRel i)
      ) ->
      (forall (Γ : context) (ind : inductive) (pars c : nat) (u : Instance.t)
        (args0 args1 : list term)
        (p : term) (brs0 brs1 : list (nat * term)),
          All2 (P' Γ) args0 args1 ->
          All2 (on_Trel_eq (P' Γ) snd fst) brs0 brs1 ->
          P Γ
            (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0)
            (iota_red pars c args1 brs1)
      ) ->
      (forall (Γ : context) (mfix0 mfix1 : mfixpoint term) (idx : nat)
        (args0 args1 : list term) (narg : nat) (fn : term),
          All2 (fun x y =>
            P' Γ x.(dtype) y.(dtype) ×
            P' (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
            (dname x, rarg x) = (dname y, rarg y)
          ) mfix0 mfix1 ->
          unfold_fix mfix1 idx = Some (narg, fn) ->
          is_constructor narg args0 = true ->
          All2 (P' Γ) args0 args1 ->
          P Γ (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)
      ) ->
      (forall (Γ : context) (ip : inductive * nat) (p0 p1 : term)
        (mfix0 mfix1 : mfixpoint term) (idx : nat)
        (args0 args1 : list term) (narg : nat) (fn : term)
        (brs0 brs1 : list (nat * term)),
          All2 (fun x y =>
            P' Γ x.(dtype) y.(dtype) ×
            P' (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
            (dname x, rarg x) = (dname y, rarg y)
          ) mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ) args0 args1 ->
          pred1_extra Γ p0 p1 ->
          P Γ p0 p1 ->
          All2 (on_Trel_eq (P' Γ) snd fst) brs0 brs1 ->
          P Γ
            (tCase ip p0 (mkApps (tCoFix mfix0 idx) args0) brs0)
            (tCase ip p1 (mkApps fn args1) brs1)
      ) ->
      (forall (Γ : context) (p : projection) (mfix0 mfix1 : mfixpoint term)
        (idx : nat) (args0 args1 : list term)
        (narg : nat) (fn : term),
          All2 (fun x y =>
            P' Γ x.(dtype) y.(dtype) ×
            P' (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
            (dname x, rarg x) = (dname y, rarg y)
          ) mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ) args0 args1 ->
          P Γ
            (tProj p (mkApps (tCoFix mfix0 idx) args0))
            (tProj p (mkApps fn args1))
      ) ->
      (forall (Γ : context) (c : kername) (n : nat) (u : Instance.t),
          P Γ (tSymb c n u) (tSymb c n u)
      ) ->
      (forall (Γ : context) k ui decl n r s s',
          declared_symbol Σ k decl ->
          nth_error decl.(rules) n = Some r ->
          All2 (P' Γ) s s' ->
          let ss := symbols_subst k 0 ui #|decl.(symbols)| in
          untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
          let lhs := subst0 s (subst ss #|s| (lhs r)) in
          let rhs := subst0 s' (subst ss #|s| (rhs r)) in
          P Γ lhs rhs
      ) ->
      (forall (Γ : context) k ui decl n r s s',
          declared_symbol Σ k decl ->
          nth_error decl.(prules) n = Some r ->
          All2 (P' Γ) s s' ->
          let ss := symbols_subst k 0 ui #|decl.(symbols)| in
          untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
          let lhs := subst0 s (subst ss #|s| (lhs r)) in
          let rhs := subst0 s' (subst ss #|s| (rhs r)) in
          P Γ lhs rhs
      ) ->
      (forall (Γ : context) k ui decl n r s s',
          extra = Some (k, decl) →
          nth_error (all_rewrite_rules decl) n = Some r ->
          All2 (P' Γ) s s' ->
          let ss := symbols_subst k 0 ui #|decl.(symbols)| in
          untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
          let lhs := subst0 s (subst ss #|s| (lhs r)) in
          let rhs := subst0 s' (subst ss #|s| (rhs r)) in
          P Γ lhs rhs
      ) ->
      (forall (Γ : context) (c : kername) (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall u : Instance.t, cst_body decl = Some body ->
          P Γ (tConst c u) (subst_instance_constr u body)
      ) ->
      (forall (Γ : context) c (u : Instance.t),
          P Γ (tConst c u) (tConst c u)
      ) ->
      (forall (Γ : context) (i : inductive) (pars narg : nat) (k : nat)
        (u : Instance.t) (args0 args1 : list term) (arg1 : term),
          All2 (pred1_extra Γ) args0 args1 ->
          All2 (P Γ) args0 args1 ->
          nth_error args1 (pars + narg) = Some arg1 ->
          P Γ (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1
      ) ->
      (forall (Γ : context) (na : name) (M M' N N' : term),
          pred1_extra Γ M M' -> P Γ M M' ->
          pred1_extra (Γ,, vass na M) N N' ->
          P (Γ,, vass na M) N N' ->
          P Γ (tLambda na M N) (tLambda na M' N')
      ) ->
      (forall (Γ : context) (M0 M1 N0 N1 : term),
          pred1_extra Γ M0 M1 ->
          P Γ M0 M1 ->
          pred1_extra Γ N0 N1 ->
          P Γ N0 N1 ->
          P Γ (tApp M0 N0) (tApp M1 N1)
      ) ->
      (forall (Γ : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1_extra Γ d0 d1 ->
          P Γ d0 d1 ->
          pred1_extra Γ t0 t1 ->
          P Γ t0 t1 ->
          pred1_extra (Γ,, vdef na d0 t0) b0 b1 ->
          P (Γ,, vdef na d0 t0) b0 b1 ->
          P Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)
      ) ->
      (forall (Γ : context) (ind : inductive * nat) (p0 p1 c0 c1 : term)
        (brs0 brs1 : list (nat * term)),
          pred1_extra Γ p0 p1 ->
          P Γ p0 p1 ->
          pred1_extra Γ c0 c1 ->
          P Γ c0 c1 ->
          All2 (on_Trel_eq (P' Γ) snd fst) brs0 brs1 ->
          P Γ (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)
      ) ->
      (forall (Γ : context) (p : projection) (c c' : term),
          pred1_extra Γ c c' ->
          P Γ c c' ->
          P Γ (tProj p c) (tProj p c')
      ) ->
      (forall (Γ : context) (mfix0 : mfixpoint term) (mfix1 : list (def term))
        (idx : nat),
          All2 (fun x y =>
            P' Γ x.(dtype) y.(dtype) ×
            P' (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
            (dname x, rarg x) = (dname y, rarg y)
          ) mfix0 mfix1 ->
          P Γ (tFix mfix0 idx) (tFix mfix1 idx)
      ) ->
      (forall (Γ : context) (mfix0 : mfixpoint term) (mfix1 : list (def term))
        (idx : nat),
          All2 (fun x y =>
            P' Γ x.(dtype) y.(dtype) ×
            P' (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
            (dname x, rarg x) = (dname y, rarg y)
          ) mfix0 mfix1 ->
          P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)
      ) ->
      (forall (Γ : context) (na : name) (M0 M1 N0 N1 : term),
          pred1_extra Γ M0 M1 ->
          P Γ M0 M1 ->
          pred1_extra (Γ,, vass na M0) N0 N1 ->
          P (Γ,, vass na M0) N0 N1 ->
          P Γ (tProd na M0 N0) (tProd na M1 N1)
      ) ->
      (forall (Γ : context) (ev : nat) (l l' : list term),
          All2 (P' Γ) l l' ->
          P Γ (tEvar ev l) (tEvar ev l')
      ) ->
      (forall (Γ : context) (t : term),
          pred_atom t ->
          P Γ t t
      ) ->
      forall (Γ : context) (t t0 : term), pred1_extra Γ t t0 -> P Γ t t0.
  Proof.
    intros P P'.
    intros X X0 X1 X2 X3 X4 X5 X6 X7 Xrw Xprw Xxrw X8 X9 X10 X11 X12 X13 X14 X15 X16
      X17 X18 X19 X20 Γ t t0 X21.
    revert Γ t t0 X21.
    fix aux 4. intros Γ t t'.
    move aux at top.
    destruct 1; match goal with
                | |- P _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | |- P _ (tRel _) _ => idtac
                | |- P _ (tSymb _ _ _) _ => idtac
                | |- P _ (tConst _ _) _ => idtac
                | lhs := _, rhs := _ |- _ => idtac
                | H : _ |- _ => eapply H; eauto
                end.
    - apply X1. auto.
    - apply X2.
    - eapply All2_impl_def. 1: exact a.
      intros. split. 1: auto.
      apply (aux _ _ _ X21).
    - eapply All2_impl_def. 1: eauto.
      intros [? ?] [? ?]. cbn. intros [? ?].
      split. 2: auto.
      split. 1: auto.
      eapply aux. auto.
    - eapply X4. all: eauto.
      + eapply All2_impl_def. 1: eauto.
        intros [? ? ?] [? ? ?]. cbn. intros [? [? ?]].
        intuition eauto.
        * split. 1: auto.
          eapply aux. auto.
        * split. 1: auto.
          eapply aux. auto.
      + eapply All2_impl_def. 1: eauto.
        intros. split. 1: auto.
        eapply aux. auto.
    - eapply X5. all: eauto.
      + eapply All2_impl_def. 1: eauto.
        intros [? ? ?] [? ? ?]. cbn. intros [? [? ?]].
        intuition eauto.
        * split. 1: auto.
          eapply aux. auto.
        * split. 1: auto.
          eapply aux. auto.
      + eapply All2_impl_def. 1: eauto.
        intros. split. 1: auto.
        eapply aux. auto.
      + eapply All2_impl_def. 1: eauto.
        intros [] []. cbn. intros [].
        intuition auto.
        split. 1: auto.
        eapply aux. auto.
    - eapply X6. all: eauto.
      + eapply All2_impl_def. 1: eauto.
        intros [? ? ?] [? ? ?]. cbn. intros [? [? ?]].
        intuition auto.
        * split. 1: auto.
          eapply aux. auto.
        * split. 1: auto.
          eapply aux. auto.
      + eapply All2_impl_def. 1: eauto.
        intros. split. 1: auto.
        eapply aux. auto.
    - eapply X7.
    - eapply Xrw. all: eauto.
      eapply All2_impl_def. 1: eauto.
      intros. split. 1: auto.
      eapply aux. auto.
    - eapply Xprw. all: eauto.
      eapply All2_impl_def. 1: eauto.
      intros. split. 1: auto.
      eapply aux. auto.
    - eapply Xxrw. all: eauto.
      eapply All2_impl_def. 1: eauto.
      intros. split. 1: auto.
      eapply aux. auto.
    - eapply X8. all: eauto.
    - eapply X9; eauto.
    - eapply All2_impl_def. 1: eauto.
      intros.
      eapply aux. auto.
    - eapply All2_impl_def. 1: eauto.
      intros [] []. cbn. intros [].
      split. 2: auto.
      split. 1: auto.
      eapply aux. auto.
    - eapply X16.
      eapply All2_impl_def. 1: eauto.
      intros [] []. cbn. intros [? [? ?]].
      intuition auto.
      + split. 1: auto.
        eapply aux. auto.
      + split. 1: auto.
        eapply aux. auto.
    - eapply X17.
      eapply All2_impl_def. 1: eauto.
      intros [] []. cbn. intros [? [? ?]].
      intuition auto.
      + split. 1: auto.
        eapply aux. auto.
      + split. 1: auto.
        eapply aux. auto.
    - eapply All2_impl_def. 1: eauto.
      intros.
      split. 1: auto.
      eapply aux. auto.
  Defined.

End ParallelReductionExtra.

(* Notation pred1_extra_ctx Σ e Γ Γ' :=
  (All2_local_env (on_decl (pred1_extra Σ e)) Γ Γ'). *)

(* Since we only have one context, it is not true
  So we have to trust it's a good definition.
  Examples will help see it is alright.
*)
(* Lemma pred1_pred1_extra :
  ∀ Σ Γ Δ u v e,
    pred1 Σ Γ Δ u v →
    pred1_extra Σ e Γ Δ u v.
Proof.
  intros Σ Γ Δ u v e h.
  set (Pctx :=
    fun Γ Δ =>
      pred1_extra_ctx Σ e Γ Δ
  ).
  revert Γ Δ u v h.
  refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: try solve [ auto ].
  all: try solve [ econstructor ; eauto ].
  all: try solve [
    intros ;
    econstructor ; eauto ;
    solve [ eapply All2_impl ; intuition eauto ; intuition eauto ]
  ].
  (* all: try solve [
    intros ;
    econstructor ; eauto ;
    unfold on_Trel in * ;
    solve [ eapply All2_impl ; intuition eauto ; intuition eauto ]
  ]. *)
  all: intros.
  - econstructor. all: eauto.
    + eapply All2_impl. 1: eauto.
      intros ? ? [? [[? ?] ?]]. intuition eauto.
      unfold on_Trel in *. intuition eauto.
    + eapply All2_impl. 1: eauto.
      intros ? ? [? ?]. auto.
  - econstructor. all: eauto.
    + eapply All2_impl. 1: eauto.
      intros ? ? [[? ?] [[? ?] ?]]. unfold on_Trel.
      intuition eauto.
    + eapply All2_impl. 1: eauto.
      intros ? ? [? ?]. auto.
    + eapply All2_impl. 1: eauto.
      intros ? ? [[? ?] ?]. intuition auto.
  - econstructor. all: eauto.
    + eapply All2_impl. 1: eauto.
      intros ? ? [[? ?] [[? ?] ?]]. unfold on_Trel.
      intuition eauto.
    + eapply All2_impl. 1: eauto.
      intros ? ? [? ?]. auto.
  - econstructor. all: eauto.
    eapply All2_impl. 1: eauto.
    intros ? ? [[? ?] [[? ?] ?]]. unfold on_Trel.
    intuition eauto.
  - econstructor. all: eauto.
    eapply All2_impl. 1: eauto.
    intros ? ? [[? ?] [[? ?] ?]]. unfold on_Trel.
    intuition eauto.
Qed. *)

Lemma weakening_pred1_pred1_eq :
  ∀ (cf : checker_flags) Σ Γ Δ Γ' Δ' u v k1 k2,
    wf Σ →
    All2_local_env_over (pred1 Σ) Γ Δ Γ' Δ' →
    pred1 Σ Γ Δ u v →
    k1 = #|Γ'| →
    k2 = #|Δ'| →
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') (lift0 k1 u) (lift0 k2 v).
Proof.
  intros. subst.
  eapply weakening_pred1_pred1. all: auto.
Qed.

Lemma pred1_extra_pred1_fix_context `{cf : checker_flags} :
  ∀ Σ e Γ Δ mfix0 mfix1,
    wf Σ →
    pred1_ctx Σ Γ Δ →
    All2 (λ x y,
      (pred1_extra Σ e Γ (dtype x) (dtype y) ×
      (∀ Δ, pred1_ctx Σ Γ Δ → pred1 Σ Γ Δ (dtype x) (dtype y))) ×
      (pred1_extra Σ e (Γ ,,, fix_context mfix0) (dbody x) (dbody y) ×
      (∀ Δ,
        pred1_ctx Σ (Γ ,,, fix_context mfix0) Δ →
        pred1 Σ (Γ ,,, fix_context mfix0) Δ (dbody x) (dbody y))
      ) ×
      (dname x, rarg x) = (dname y, rarg y)
    ) mfix0 mfix1 →
    All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ Δ))
      (fix_context mfix0) (fix_context mfix1).
Proof.
  intros Σ e Γ Δ mfix0 mfix1 hΣ hctx h.
  rewrite 2!PCUICPosition.fix_context_fix_context_alt.
  unfold PCUICPosition.fix_context_alt.
  apply All2_rev in h.
  rewrite 2!rev_mapi.
  rewrite <- 2!map_rev.
  assert (e0 : #|List.rev mfix0| = #|mfix0| - 0).
  { rewrite List.rev_length. lia. }
  assert (e1 : #|List.rev mfix1| = #|mfix1| - 0).
  { rewrite List.rev_length. lia. }
  revert e0 e1 h.
  generalize (List.rev mfix0). generalize (List.rev mfix1).
  intros m1 m0 e0 e1 h.
  unfold mapi.
  revert e0 e1.
  generalize 0 at 1 2 4 6.
  intros n e0 e1.
  induction h as [| ? ? ? ? [[? hp] ?] h ih] in n, e0, e1 |- *.
  1: constructor.
  cbn. cbn in e0, e1.
  constructor.
  - eapply ih. all: lia.
  - cbn. unfold on_decl_over.
    eapply weakening_pred1_pred1_eq.
    1: auto.
    3,4: rewrite mapi_rec_length.
    3,4: rewrite !map_length.
    3,4: lia.
    + eapply ih. all: lia.
    + eapply hp. auto.
Qed.

Lemma pred1_extra_pred1 `{cf : checker_flags} :
  ∀ Σ Γ Δ u v e,
    wf Σ →
    on_Some (fun '(k, rd) =>
      lookup_env Σ k = Some (RewriteDecl rd)
    ) e →
    pred1_extra Σ e Γ u v →
    pred1_ctx Σ Γ Δ →
    pred1 Σ Γ Δ u v.
Proof.
  intros Σ Γ Δ u v e hΣ he h hctx.
  revert Γ u v h Δ hctx.
  refine (pred1_extra_ind_all_ctx Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: try solve [ econstructor ; eauto ].
  all: try solve [
    intros ;
    econstructor ; eauto ;
    solve [ eapply All2_impl ; intuition eauto ; intuition eauto ]
  ].
  all: try solve [
    intros ;
    econstructor ; eauto ;
    try solve [ eapply All2_impl ; intuition eauto ; intuition eauto ] ;
    match goal with
    | h : ∀ Δ, pred1_ctx _ _ _ → pred1 _ _ _ ?u ?v |-
      pred1 _ _ _ ?u ?v =>
      eapply h
    end ;
    econstructor ; [
      auto
    | cbn ; eauto
    ]
  ].
  all: intros.
  - econstructor. 1: auto.
    (* NEED extra constructor for pred1 *)
    give_up.
  - econstructor. all: eauto.
    + eapply pred1_extra_pred1_fix_context. all: eauto.
    + unfold All2_prop2_eq. eapply All2_impl. 1: eauto.
      cbn. intros [] []. cbn. intros [[? ?] [[? h] ?]].
      unfold on_Trel. cbn.
      intuition auto.
      eapply h.
      eapply pred1_extra_pred1_fix_context in X. 2,3: eauto.
      clear - X hctx. induction X.
      * auto.
      * cbn. constructor. all: auto.
      * cbn. constructor. all: auto.
    + eapply All2_impl. 1: eauto.
      cbn. intuition auto.
  - econstructor. all: eauto.
    + admit.
    + admit.
    + eapply All2_impl. 1: eauto.
      cbn. intuition auto.
    + eapply All2_impl. 1: eauto.
      cbn. intuition auto.
  - econstructor. all: eauto.
    + admit.
    + admit.
    + eapply All2_impl. 1: eauto.
      cbn. intuition auto.
  - subst. cbn in he.
    match goal with
    | h : nth_error (all_rewrite_rules _) _ = _ |- _ =>
      unfold all_rewrite_rules in h ;
      eapply nth_error_app_dec in h as [[? ?] | [? ?]]
    end.
    + eapply pred_par_rewrite_rule. all: eauto.
      eapply All2_impl. 1: eauto.
      intros ? ? [? ?]. auto.
    + eapply pred_rewrite_rule. all: eauto.
      eapply All2_impl. 1: eauto.
      intros ? ? [? ?]. auto.
  - econstructor. 1: auto.
    + admit.
    + admit.
  - econstructor. 1: auto.
    + admit.
    + admit.
Admitted.

Lemma weakening_env_pred1_extra :
  ∀ `{cf : checker_flags} Σ Σ' e Γ u v,
    wf Σ' →
    PCUICWeakeningEnv.extends Σ Σ' →
    pred1_extra Σ e Γ u v →
    pred1_extra Σ' e Γ u v.
Proof.
  intros cf Σ Σ' e Γ u v hΣ hx h.
  revert Γ u v h.
  refine (pred1_extra_ind_all_ctx Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: try solve [ econstructor ; eauto ].
  all: try solve [
    intros ;
    econstructor ; eauto ;
    solve [ eapply All2_impl ; intuition eauto ; intuition eauto ]
  ].
  - intros. eapply predx_rewrite_rule. all: eauto.
    + eapply PCUICWeakeningEnv.extends_lookup. all: eauto.
    + eapply All2_impl. 1: eauto.
      intros ? ? [? ?]. intuition eauto.
  - intros. eapply predx_par_rewrite_rule. all: eauto.
    + eapply PCUICWeakeningEnv.extends_lookup. all: eauto.
    + eapply All2_impl. 1: eauto.
      intros ? ? [? ?]. intuition eauto.
  - intros. econstructor. all: eauto.
    eapply PCUICWeakeningEnv.extends_lookup. all: eauto.
Qed.
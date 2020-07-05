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

  Inductive pred1_extra (Γ Γ' : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | predx_beta na t0 t1 b0 b1 a0 a1 :
      pred1_extra Γ Γ' t0 t1 ->
      pred1_extra (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> pred1_extra Γ Γ' a0 a1 ->
      pred1_extra Γ Γ' (tApp (tLambda na t0 b0) a0) (subst10 a1 b1)

  (** Let *)
  | predx_zeta na d0 d1 t0 t1 b0 b1 :
      pred1_extra Γ Γ' t0 t1 ->
      pred1_extra Γ Γ' d0 d1 -> pred1_extra (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1_extra Γ Γ' (tLetIn na d0 t0 b0) (subst10 d1 b1)

  (** Local variables *)
  | predx_rel_def_unfold i body :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      option_map decl_body (nth_error Γ' i) = Some (Some body) ->
      pred1_extra Γ Γ' (tRel i) (lift0 (S i) body)

  | predx_rel_refl i :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      pred1_extra Γ Γ' (tRel i)  (tRel i)

  (** Case *)
  | predx_iota ind pars c u args0 args1 p brs0 brs1 :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      All2 (pred1_extra Γ Γ') args0 args1 ->
      All2 (on_Trel_eq (pred1_extra Γ Γ') snd fst) brs0 brs1 ->
      pred1_extra Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0)
            (iota_red pars c args1 brs1)

  (** Fix unfolding, with guard *)
  | predx_fix mfix0 mfix1 idx args0 args1 narg fn :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1_extra mfix0 mfix1 ->
      unfold_fix mfix1 idx = Some (narg, fn) ->
      is_constructor narg args0 = true ->
      All2 (pred1_extra Γ Γ') args0 args1 ->
      pred1_extra Γ Γ' (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)

  (** CoFix-case unfolding *)
  | predx_cofix_case ip p0 p1 mfix0 mfix1 idx args0 args1 narg fn brs0 brs1 :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1_extra mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1_extra Γ Γ') args0 args1 ->
      pred1_extra Γ Γ' p0 p1 ->
      All2 (on_Trel_eq (pred1_extra Γ Γ') snd fst) brs0 brs1 ->
      pred1_extra Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix0 idx) args0) brs0)
            (tCase ip p1 (mkApps fn args1) brs1)

  (** CoFix-proj unfolding *)
  | predx_cofix_proj p mfix0 mfix1 idx args0 args1 narg fn :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1_extra mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1_extra Γ Γ') args0 args1 ->
      pred1_extra Γ Γ' (tProj p (mkApps (tCoFix mfix0 idx) args0))
            (tProj p (mkApps fn args1))

  (** Symbols and rewrite rules  *)

  | predx_symb k n u :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      pred1_extra Γ Γ' (tSymb k n u) (tSymb k n u)

  | predx_rewrite_rule k ui decl n r s s' :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      declared_symbol Σ k decl ->
      nth_error decl.(rules) n = Some r ->
      All2 (pred1_extra Γ Γ') s s' ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let lhs := subst0 s (subst ss #|s| (lhs r)) in
      let rhs := subst0 s' (subst ss #|s| (rhs r)) in
      pred1_extra Γ Γ' lhs rhs

  | predx_par_rewrite_rule k ui decl n r s s' :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      declared_symbol Σ k decl ->
      nth_error decl.(prules) n = Some r ->
      All2 (pred1_extra Γ Γ') s s' ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let lhs := subst0 s (subst ss #|s| (lhs r)) in
      let rhs := subst0 s' (subst ss #|s| (rhs r)) in
      pred1_extra Γ Γ' lhs rhs

  | predx_extra_rewrite_rule k ui decl n r s s' :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      extra = Some (k, decl) →
      nth_error (all_rewrite_rules decl) n = Some r ->
      All2 (pred1_extra Γ Γ') s s' ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let lhs := subst0 s (subst ss #|s| (lhs r)) in
      let rhs := subst0 s' (subst ss #|s| (rhs r)) in
      pred1_extra Γ Γ' lhs rhs

  (** Constant unfolding *)

  | predx_delta c decl body (isdecl : declared_constant Σ c decl) u :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      decl.(cst_body) = Some body ->
      pred1_extra Γ Γ' (tConst c u) (subst_instance_constr u body)

  | predx_const c u :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      pred1_extra Γ Γ' (tConst c u) (tConst c u)

  (** Proj *)
  | predx_proj i pars narg k u args0 args1 arg1 :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      All2 (pred1_extra Γ Γ') args0 args1 ->
      nth_error args1 (pars + narg) = Some arg1 ->
      pred1_extra Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1

  (** Congruences *)
  | predx_abs na M M' N N' : pred1_extra Γ Γ' M M' -> pred1_extra (Γ ,, vass na M) (Γ' ,, vass na M') N N' ->
                            pred1_extra Γ Γ' (tLambda na M N) (tLambda na M' N')
  | predx_app M0 M1 N0 N1 :
      pred1_extra Γ Γ' M0 M1 ->
      pred1_extra Γ Γ' N0 N1 ->
      pred1_extra Γ Γ' (tApp M0 N0) (tApp M1 N1)
            (* do not handle mkApps yet *)

  | predx_letin na d0 d1 t0 t1 b0 b1 :
      pred1_extra Γ Γ' d0 d1 -> pred1_extra Γ Γ' t0 t1 -> pred1_extra (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1_extra Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)

  | predx_case ind p0 p1 c0 c1 brs0 brs1 :
      pred1_extra Γ Γ' p0 p1 ->
      pred1_extra Γ Γ' c0 c1 ->
      All2 (on_Trel_eq (pred1_extra Γ Γ') snd fst) brs0 brs1 ->
      pred1_extra Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)

  | predx_proj_congr p c c' :
      pred1_extra Γ Γ' c c' -> pred1_extra Γ Γ' (tProj p c) (tProj p c')

  | predx_fix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1_extra mfix0 mfix1 ->
      pred1_extra Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)

  | predx_cofix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1_extra mfix0 mfix1 ->
      pred1_extra Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)

  | predx_prod na M0 M1 N0 N1 : pred1_extra Γ Γ' M0 M1 -> pred1_extra (Γ ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
                               pred1_extra Γ Γ' (tProd na M0 N0) (tProd na M1 N1)

  | evar_pred ev l l' :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      All2 (pred1_extra Γ Γ') l l' -> pred1_extra Γ Γ' (tEvar ev l) (tEvar ev l')

  | predx_atom_refl t :
      All2_local_env (on_decl pred1_extra) Γ Γ' ->
      pred_atom t -> pred1_extra Γ Γ' t t.

  Lemma pred1_extra_ind_all_ctx :
    forall (P : forall (Γ Γ' : context) (t t0 : term), Type)
           (Pctx : forall (Γ Γ' : context), Type),
      let P' Γ Γ' x y := ((pred1_extra Γ Γ' x y) * P Γ Γ' x y)%type in
      (forall Γ Γ', All2_local_env (on_decl pred1_extra) Γ Γ' -> All2_local_env (on_decl P) Γ Γ' -> Pctx Γ Γ') ->
      (forall (Γ Γ' : context) (na : name) (t0 t1 b0 b1 a0 a1 : term),
          pred1_extra (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> P (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 ->
          pred1_extra Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1_extra Γ Γ' a0 a1 -> P Γ Γ' a0 a1 -> P Γ Γ' (tApp (tLambda na t0 b0) a0) (b1 {0 := a1})) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1_extra Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1_extra Γ Γ' d0 d1 -> P Γ Γ' d0 d1 ->
          pred1_extra (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
          P (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (b1 {0 := d1})) ->
      (forall (Γ Γ' : context) (i : nat) (body : term),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          option_map decl_body (nth_error Γ' i) = Some (Some body) ->
          P Γ Γ' (tRel i) (lift0 (S i) body)) ->
      (forall (Γ Γ' : context) (i : nat),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tRel i) (tRel i)) ->
      (forall (Γ Γ' : context) (ind : inductive) (pars c : nat) (u : Instance.t) (args0 args1 : list term)
              (p : term) (brs0 brs1 : list (nat * term)),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') args0 args1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0) (iota_red pars c args1 brs1)) ->
      (forall (Γ Γ' : context) (mfix0 mfix1 : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn : term),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_fix mfix1 idx = Some (narg, fn) ->
          is_constructor narg args0 = true ->
          All2 (P' Γ Γ') args0 args1 ->
          P Γ Γ' (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)) ->
      (forall (Γ Γ' : context) (ip : inductive * nat) (p0 p1 : term) (mfix0 mfix1 : mfixpoint term) (idx : nat)
              (args0 args1 : list term) (narg : nat) (fn : term) (brs0 brs1 : list (nat * term)),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ Γ') args0 args1 ->
          pred1_extra Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix0 idx) args0) brs0) (tCase ip p1 (mkApps fn args1) brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (mfix0 mfix1 : mfixpoint term)
         (idx : nat) (args0 args1 : list term)
         (narg : nat) (fn : term),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ Γ') args0 args1 ->
          P Γ Γ' (tProj p (mkApps (tCoFix mfix0 idx) args0)) (tProj p (mkApps fn args1))) ->
      (forall (Γ Γ' : context) (c : kername) (n : nat) (u : Instance.t),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tSymb c n u) (tSymb c n u)) ->
      (forall (Γ Γ' : context) k ui decl n r s s',
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          declared_symbol Σ k decl ->
          nth_error decl.(rules) n = Some r ->
          All2 (P' Γ Γ') s s' ->
          let ss := symbols_subst k 0 ui #|decl.(symbols)| in
          untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
          let lhs := subst0 s (subst ss #|s| (lhs r)) in
          let rhs := subst0 s' (subst ss #|s| (rhs r)) in
          P Γ Γ' lhs rhs
      ) ->
      (forall (Γ Γ' : context) k ui decl n r s s',
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          declared_symbol Σ k decl ->
          nth_error decl.(prules) n = Some r ->
          All2 (P' Γ Γ') s s' ->
          let ss := symbols_subst k 0 ui #|decl.(symbols)| in
          untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
          let lhs := subst0 s (subst ss #|s| (lhs r)) in
          let rhs := subst0 s' (subst ss #|s| (rhs r)) in
          P Γ Γ' lhs rhs
      ) ->
      (forall (Γ Γ' : context) k ui decl n r s s',
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          extra = Some (k, decl) →
          nth_error (all_rewrite_rules decl) n = Some r ->
          All2 (P' Γ Γ') s s' ->
          let ss := symbols_subst k 0 ui #|decl.(symbols)| in
          untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
          let lhs := subst0 s (subst ss #|s| (lhs r)) in
          let rhs := subst0 s' (subst ss #|s| (rhs r)) in
          P Γ Γ' lhs rhs
      ) ->
      (forall (Γ Γ' : context) (c : kername) (decl : constant_body) (body : term),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          declared_constant Σ c decl ->
          forall u : Instance.t, cst_body decl = Some body ->
                                        P Γ Γ' (tConst c u) (subst_instance_constr u body)) ->
      (forall (Γ Γ' : context) c (u : Instance.t),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tConst c u) (tConst c u)) ->
      (forall (Γ Γ' : context) (i : inductive) (pars narg : nat) (k : nat) (u : Instance.t)
              (args0 args1 : list term) (arg1 : term),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (pred1_extra Γ Γ') args0 args1 ->
          All2 (P Γ Γ') args0 args1 ->
          nth_error args1 (pars + narg) = Some arg1 ->
          P Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1) ->
      (forall (Γ Γ' : context) (na : name) (M M' N N' : term),
          pred1_extra Γ Γ' M M' ->
          P Γ Γ' M M' -> pred1_extra (Γ,, vass na M) (Γ' ,, vass na M') N N' ->
          P (Γ,, vass na M) (Γ' ,, vass na M') N N' -> P Γ Γ' (tLambda na M N) (tLambda na M' N')) ->
      (forall (Γ Γ' : context) (M0 M1 N0 N1 : term),
          pred1_extra Γ Γ' M0 M1 -> P Γ Γ' M0 M1 -> pred1_extra Γ Γ' N0 N1 ->
          P Γ Γ' N0 N1 -> P Γ Γ' (tApp M0 N0) (tApp M1 N1)) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1_extra Γ Γ' d0 d1 ->
          P Γ Γ' d0 d1 ->
          pred1_extra Γ Γ' t0 t1 ->
          P Γ Γ' t0 t1 ->
          pred1_extra (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 ->
          P (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) ->
      (forall (Γ Γ' : context) (ind : inductive * nat) (p0 p1 c0 c1 : term) (brs0 brs1 : list (nat * term)),
          pred1_extra Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          pred1_extra Γ Γ' c0 c1 ->
          P Γ Γ' c0 c1 -> All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (c c' : term), pred1_extra Γ Γ' c c' -> P Γ Γ' c c' -> P Γ Γ' (tProj p c) (tProj p c')) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                        dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1_extra Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
      (forall (Γ Γ' : context) (na : name) (M0 M1 N0 N1 : term),
          pred1_extra Γ Γ' M0 M1 ->
          P Γ Γ' M0 M1 -> pred1_extra (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
          P (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> P Γ Γ' (tProd na M0 N0) (tProd na M1 N1)) ->
      (forall (Γ Γ' : context) (ev : nat) (l l' : list term),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') l l' -> P Γ Γ' (tEvar ev l) (tEvar ev l')) ->
      (forall (Γ Γ' : context) (t : term),
          All2_local_env (on_decl pred1_extra) Γ Γ' ->
          Pctx Γ Γ' ->
          pred_atom t -> P Γ Γ' t t) ->
      forall (Γ Γ' : context) (t t0 : term), pred1_extra Γ Γ' t t0 -> P Γ Γ' t t0.
  Proof.
    intros P Pctx P' Hctx.
    intros X X0 X1 X2 X3 X4 X5 X6 X7 Xrw Xprw Xxrw X8 X9 X10 X11 X12 X13 X14 X15 X16
      X17 X18 X19 X20 Γ Γ' t t0 X21.
    revert Γ Γ' t t0 X21.
    fix aux 5. intros Γ Γ' t t'.
    move aux at top.
    destruct 1; match goal with
                | |- P _ _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | |- P _ _ (tRel _) _ => idtac
                | |- P _ _ (tSymb _ _ _) _ => idtac
                | |- P _ _ (tConst _ _) _ => idtac
                | lhs := _, rhs := _ |- _ => idtac
                | H : _ |- _ => eapply H; eauto
                end.
    - simpl. apply X1; auto. apply Hctx.
      + apply (All2_local_env_impl a). intros. eapply X21.
      + apply (All2_local_env_impl a). intros. eapply (aux _ _ _ _ X21).
    - simpl. apply X2; auto.
      apply Hctx, (All2_local_env_impl a).
      + exact a.
      + intros. apply (aux _ _ _ _ X21).
    - apply Hctx, (All2_local_env_impl a). 1: exact a.
      intros. apply (aux _ _ _ _ X21).
    - eapply (All2_All2_prop (P:=pred1_extra) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply (All2_All2_prop_eq (P:=pred1_extra) (Q:=P') (f:=snd) (g:=fst) a1 (extendP aux Γ Γ')).
    - eapply X4; eauto.
      + apply Hctx, (All2_local_env_impl a). 1: exact a.
        intros. apply (aux _ _ _ _ X21).
      + eapply (All2_local_env_impl a0). intros. red. red in X21.
        apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      + eapply (All2_All2_prop (P:=pred1_extra) (Q:=P') a2 (extendP aux Γ Γ')).
    - eapply X5; eauto.
      + apply Hctx, (All2_local_env_impl a). 1: exact a.
        intros. apply (aux _ _ _ _ X22).
      + eapply (All2_local_env_impl a0). intros. red. red in X22.
        apply (aux _ _ _ _ X22).
      + eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      + eapply (All2_All2_prop (P:=pred1_extra) (Q:=P') a2 (extendP aux Γ Γ')).
      + eapply (All2_All2_prop_eq (P:=pred1_extra) (Q:=P') (f:=snd) a3 (extendP aux Γ Γ')).
    - eapply X6; eauto.
      + apply Hctx, (All2_local_env_impl a). 1: exact a.
        intros. apply (aux _ _ _ _ X21).
      + eapply (All2_local_env_impl a0). intros. red. red in X21. apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      + eapply (All2_All2_prop (P:=pred1_extra) (Q:=P') a2 (extendP aux Γ Γ')).
    - eapply X7. 1: assumption.
      apply Hctx, (All2_local_env_impl a).
      + intros. exact a.
      + intros. apply (aux _ _ _ _ X21).
    - eapply Xrw. all: eauto.
      + apply Hctx. 1: auto.
        apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop (P:=pred1_extra) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply Xprw. all: eauto.
      + apply Hctx. 1: auto.
        apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop (P:=pred1_extra) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply Xxrw. all: eauto.
      + apply Hctx. 1: auto.
        apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop (P:=pred1_extra) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply X8; eauto.
      apply Hctx, (All2_local_env_impl a).
      + intros. exact a.
      + intros. apply (aux _ _ _ _ X21).
    - eapply X9; eauto.
      apply Hctx, (All2_local_env_impl a). 1: exact a.
      intros. apply (aux _ _ _ _ X21).
    - apply Hctx, (All2_local_env_impl a). 1: exact a.
      intros. apply (aux _ _ _ _ X21).
    - eapply (All2_All2_prop (P:=pred1_extra) (Q:=P) a0). intros. apply (aux _ _ _ _ X21).
    - eapply (All2_All2_prop_eq (P:=pred1_extra) (Q:=P') (f:=snd) a (extendP aux Γ Γ')).
    - eapply X16.
      + eapply (All2_local_env_impl a). intros. apply X21.
      + eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
      + eapply (All2_local_env_impl a0). intros. red. exact X21.
      + eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply X17.
      + eapply (All2_local_env_impl a). intros. apply X21.
      + eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
      + eapply (All2_local_env_impl a0). intros. red. exact X21.
      + eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
    - eapply (All2_All2_prop (P:=pred1_extra) (Q:=P') a0 (extendP aux Γ Γ')).
    - eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
  Defined.

End ParallelReductionExtra.

Notation pred1_extra_ctx Σ e Γ Γ' :=
  (All2_local_env (on_decl (pred1_extra Σ e)) Γ Γ').

Lemma pred1_pred1_extra :
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
Qed.

Lemma pred1_extra_pred1 :
  ∀ Σ Γ Δ u v e,
    on_Some (fun '(k, rd) =>
      lookup_env Σ k = Some (RewriteDecl rd)
    ) e →
    pred1_extra Σ e Γ Δ u v →
    pred1 Σ Γ Δ u v.
Proof.
  intros Σ Γ Δ u v e he h.
  set (Pctx :=
    fun Γ Δ =>
      pred1_ctx Σ Γ Δ
  ).
  revert Γ Δ u v h.
  refine (pred1_extra_ind_all_ctx Σ _ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: try solve [ auto ].
  all: try solve [ econstructor ; eauto ].
  all: try solve [
    intros ;
    econstructor ; eauto ;
    solve [ eapply All2_impl ; intuition eauto ; intuition eauto ]
  ].
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
  - econstructor. all: eauto.
    eapply All2_impl. 1: eauto.
    intros ? ? [[? ?] [[? ?] ?]]. unfold on_Trel.
    intuition eauto.
  - econstructor. all: eauto.
    eapply All2_impl. 1: eauto.
    intros ? ? [[? ?] [[? ?] ?]]. unfold on_Trel.
    intuition eauto.
Qed.

Lemma weakening_env_pred1_extra :
  ∀ `{cf : checker_flags} Σ Σ' e Γ Δ u v,
    wf Σ' →
    PCUICWeakeningEnv.extends Σ Σ' →
    pred1_extra Σ e Γ Δ u v →
    pred1_extra Σ' e Γ Δ u v.
Proof.
  intros cf Σ Σ' e Γ Δ u v hΣ hx h.
  set (Pctx :=
    fun Γ Δ =>
      pred1_extra_ctx Σ' e Γ Δ
  ).
  revert Γ Δ u v h.
  refine (pred1_extra_ind_all_ctx Σ _ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: try solve [ auto ].
  all: try solve [ econstructor ; eauto ].
  all: try solve [
    intros ;
    econstructor ; eauto ;
    solve [ eapply All2_impl ; intuition eauto ; intuition eauto ]
  ].
  all: try solve [
    intros ;
    unfold on_Trel in * ;
    econstructor ; eauto ;
    unfold on_Trel in * ;
    solve [
      eapply All2_impl ;
      intuition eauto ;
      unfold on_Trel in * ;
      intuition eauto
    ]
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
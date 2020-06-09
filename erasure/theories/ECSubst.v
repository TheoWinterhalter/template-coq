(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List Program Lia Arith.
From MetaCoq.Template Require Import utils.
From MetaCoq.Erasure Require Import EAst EInduction ELiftSubst.

Set Warnings "-notation-overridden".

Require Import ssreflect ssrbool.

From Equations Require Import Equations.

Local Ltac inv H := inversion H; subst.

(** Closed single substitution: no lifting involved and one term at a time. *)

Fixpoint csubst t k u :=
  match u with
  | tBox => tBox
  | tRel n =>
     match Nat.compare k n with
    | Datatypes.Eq => t
    | Gt => tRel n
    | Lt => tRel (Nat.pred n)
    end
  | tEvar ev args => tEvar ev (List.map (csubst t k) args)
  | tLambda na M => tLambda na (csubst t (S k) M)
  | tApp u v => tApp (csubst t k u) (csubst t k v)
  | tLetIn na b b' => tLetIn na (csubst t k b) (csubst t (S k) b')
  | tCase ind c brs =>
    let brs' := List.map (on_snd (csubst t k)) brs in
    tCase ind (csubst t k c) brs'
  | tProj p c => tProj p (csubst t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

(** It is equivalent to general substitution on closed terms. *)  
Lemma closed_subst t k u : closed t ->
    csubst t k u = subst [t] k u.
Proof.
  revert k; induction u using term_forall_list_ind; intros k Hs; 
    simpl; try f_equal; eauto; solve_all.
  - destruct (PeanoNat.Nat.compare_spec k n).
    + subst k.
      rewrite PeanoNat.Nat.leb_refl minus_diag /=.
      now rewrite lift_closed.
    + destruct (leb_spec_Set k n); try lia.
      destruct (nth_error_spec [t] (n - k) ).
      simpl in l0; lia.
      now rewrite Nat.sub_1_r.
    + now destruct (Nat.leb_spec k n); try lia.
Qed.

(*
Lemma closedn_subst s k k' t :
  forallb (closedn k) s -> closedn (k + k' + #|s|) t ->
  closedn (k + k') (subst s k' t).
Proof.
  intros Hs. solve_all. revert H.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    simpl closed in *; try change_Sk; repeat (rtoProp; solve_all);
    unfold compose, test_def, on_snd, test_snd in *; simpl in *; eauto with all.

  - elim (Nat.leb_spec k' n); intros. simpl.
    apply Nat.ltb_lt in H.
    destruct nth_error eqn:Heq.
    -- eapply closedn_lift.
       now eapply nth_error_all in Heq; simpl; eauto; simpl in *.
    -- simpl. elim (Nat.ltb_spec); auto. intros.
       apply nth_error_None in Heq. lia.
    -- simpl. apply Nat.ltb_lt in H0.
       apply Nat.ltb_lt. apply Nat.ltb_lt in H0. lia.

  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt3 (S k')).
    rewrite <- Nat.add_succ_comm in IHt3. eauto.
  - rtoProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (b0 (#|m| + k')). unfold is_true. rewrite <- b0. f_equal. lia.
    unfold is_true. rewrite <- H0. f_equal. lia.
  - rtoProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (b0 (#|m| + k')). unfold is_true. rewrite <- b0. f_equal. lia.
    unfold is_true. rewrite <- H0. f_equal. lia.
Qed.

Lemma closedn_subst0 s k t :
  forallb (closedn k) s -> closedn (k + #|s|) t ->
  closedn k (subst0 s t).
Proof.
  intros.
  generalize (closedn_subst s k 0 t H).
  rewrite Nat.add_0_r. eauto.
Qed.



Lemma closed_csubst t k u : closed t -> closedn (S k) u -> closedn k (csubst t 0 u).
Proof.
  intros.
  rewrite closed_subst; auto.
  eapply closedn_subst0. simpl. erewrite closed_upwards; eauto. lia.
  simpl. now rewrite Nat.add_1_r.
Qed.
*)
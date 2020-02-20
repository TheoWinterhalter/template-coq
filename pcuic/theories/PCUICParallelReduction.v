(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
From MetaCoq Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec String Lia.
From MetaCoq.Template Require Import config monad_utils utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICSize PCUICPattern PCUICLiftSubst PCUICUnivSubst PCUICTyping
  PCUICReduction PCUICWeakening PCUICSubstitution PCUICReflect.

Import MonadNotation.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Local Set Keyed Unification.
Set Asymmetric Patterns.

Require Import Equations.Prop.DepElim.

Set Default Goal Selector "!".

Derive NoConfusion for term.
Derive Subterm for term.
Derive Signature NoConfusion for All All2.

Lemma size_lift n k t : size (lift n k t) = size t.
Proof.
  revert n k t.
  fix size_list 3.
  destruct t; simpl; rewrite ?list_size_map_hom; try lia.
  - elim leb_spec_Set; simpl; auto.
  - intros. auto.
  - now rewrite !size_list.
  - now rewrite !size_list.
  - now rewrite !size_list.
  - now rewrite !size_list.
  - intros.
    destruct x. simpl. now rewrite size_list.
  - now rewrite !size_list.
  - now rewrite !size_list.
  - unfold mfixpoint_size.
    rewrite list_size_map_hom.
    + intros.
      simpl. destruct x. simpl. unfold def_size. simpl.
      now rewrite !size_list.
    + reflexivity.
  - unfold mfixpoint_size.
    rewrite list_size_map_hom.
    + intros.
      simpl. destruct x. unfold def_size; simpl.
      now rewrite !size_list.
    + reflexivity.
Qed.

Require Import RelationClasses Arith.

Arguments All {A} P%type _.

Lemma All_pair {A} (P Q : A -> Type) l :
  All (fun x => P x * Q x)%type l <~> (All P l * All Q l).
Proof.
  split.
  - induction 1; intuition auto.
  - move=> [] Hl Hl'. induction Hl; depelim Hl'; intuition auto.
Qed.

Definition on_local_decl (P : context -> term -> Type)
           (Γ : context) (t : term) (T : option term) :=
  match T with
  | Some T => (P Γ t * P Γ T)%type
  | None => P Γ t
  end.

(* TODO: remove List.rev *)
Lemma list_size_rev {A} size (l : list A)
  : list_size size (List.rev l) = list_size size l.
Proof.
  induction l; simpl. 1: reflexivity.
  rewrite list_size_app IHl; cbn; lia.
Qed.

Lemma term_forall_ctx_list_ind :
  forall (P : context -> term -> Type),

    (forall Γ (n : nat), P Γ (tRel n)) ->
    (forall Γ (i : ident), P Γ (tVar i)) ->
    (forall Γ (n : nat) (l : list term), All (P Γ) l -> P Γ (tEvar n l)) ->
    (forall Γ s, P Γ (tSort s)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tProd n t t0)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tLambda n t t0)) ->
    (forall Γ (n : name) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall t1 : term, P (vdef n t t0 :: Γ) t1 -> P Γ (tLetIn n t t0 t1)) ->
    (forall Γ (t u : term), P Γ t -> P Γ u -> P Γ (tApp t u)) ->
    (forall Γ (s : String.string) (n : nat) (u : list Level.t), P Γ (tSymb s n u)) ->
    (forall Γ (s : String.string) (u : list Level.t), P Γ (tConst s u)) ->
    (forall Γ (i : inductive) (u : list Level.t), P Γ (tInd i u)) ->
    (forall Γ (i : inductive) (n : nat) (u : list Level.t), P Γ (tConstruct i n u)) ->
    (forall Γ (p : inductive * nat) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall l : list (nat * term),
            tCaseBrsProp (P Γ) l -> P Γ (tCase p t t0 l)) ->
    (forall Γ (s : projection) (t : term), P Γ t -> P Γ (tProj s t)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tFix m n)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tCoFix m n)) ->
    forall Γ (t : term), P Γ t.
Proof.
  intros.
  revert Γ t. set(foo:=Tactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt size). simpl. clear H1.
  assert (auxl : forall Γ {A} (l : list A) (f : A -> term), list_size (fun x => size (f x)) l < size pr0 ->
                                                            All (fun x => P Γ (f x)) l).
  { induction l; constructor.
    - eapply aux. red. simpl in H. lia.
    - apply IHl. simpl in H. lia.
  }
  assert (forall mfix, context_size size (fix_context mfix) <= mfixpoint_size size mfix).
  { induction mfix.
    - simpl. auto.
    - simpl. unfold fix_context.
      unfold context_size.
      rewrite list_size_rev /=. cbn.
      rewrite size_lift. unfold context_size in IHmfix.
      epose (list_size_mapi_rec_le (def_size size) (decl_size size) mfix
                                 (fun (i : nat) (d : def term) => vass (dname d) ((lift0 i) (dtype d))) 1).
      forward l.
      { intros. destruct x; cbn; rewrite size_lift. lia. }
      unfold def_size, mfixpoint_size. lia.
  }
  assert (auxl' : forall Γ mfix,
             mfixpoint_size size mfix < size pr0 ->
             All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context mfix)).
  { move=> Γ mfix H0.
    move: (fix_context mfix) {H0} (le_lt_trans _ _ _ (H mfix) H0).
    induction fix_context; cbn.
    - constructor.
    - case: a => [na [b|] ty] /=; rewrite {1}/decl_size /context_size /= => Hlt; constructor; auto.
      + eapply IHfix_context. unfold context_size. lia.
      + simpl. apply aux. red. lia.
      + simpl. split.
        * apply aux. red. lia.
        * apply aux; red; lia.
      + apply IHfix_context; unfold context_size; lia.
      + apply aux. red. lia.
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

  move aux at top. move auxl at top. move auxl' at top.

  !destruct pr0; eauto;
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); red; simpl; try lia]
        end.

  - eapply X13; try (apply aux; red; simpl; lia).
    + apply auxl'. simpl. lia.
    + red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X14; try (apply aux; red; simpl; lia).
    + apply auxl'. simpl. lia.
    + red. apply All_pair. split; apply auxl; simpl; auto.
Defined.

Lemma simpl_subst' :
  forall N M n p k, k = List.length N -> p <= n -> subst N p (lift0 (k + n) M) = lift0 n M.
Proof.
  intros. subst k. rewrite simpl_subst_rec; auto. 2: lia.
  now rewrite Nat.add_0_r.
Qed.

(** All2 lemmas *)

(* Duplicate *)
Lemma All2_app {A} {P : A -> A -> Type} {l l' r r'} :
  All2 P l l' -> All2 P r r' ->
  All2 P (l ++ r) (l' ++ r').
Proof. induction 1; simpl; auto. Qed.

Definition All2_prop_eq Γ Γ' {A B} (f : A -> term) (g : A -> B) (rel : forall (Γ Γ' : context) (t t' : term), Type) :=
  All2 (on_Trel_eq (rel Γ Γ') f g).

Definition All2_prop Γ (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (rel Γ).

(* Scheme pred1_ind_all_first := Minimality for pred1 Sort Type. *)

Lemma All2_All2_prop {P Q : context -> context -> term -> term -> Type} {par par'} {l l' : list term} :
  All2 (P par par') l l' ->
  (forall x y, P par par' x y -> Q par par' x y) ->
  All2 (Q par par') l l'.
Proof.
  intros H aux.
  induction H; constructor.
  - unfold on_Trel in *.
    apply aux; apply r.
  - apply IHAll2.
Defined.

Lemma All2_All2_prop_eq {A B} {P Q : context -> context -> term -> term -> Type} {par par'}
      {f : A -> term} {g : A -> B} {l l' : list A} :
  All2 (on_Trel_eq (P par par') f g) l l' ->
  (forall x y, P par par' x y -> Q par par' x y) ->
  All2_prop_eq par par' f g Q l l'.
Proof.
  intros H aux.
  induction H; constructor.
  - unfold on_Trel in *.
    split.
    + apply aux; apply r.
    + apply r.
  - apply IHAll2.
Defined.

Definition All2_prop2_eq Γ Γ' Γ2 Γ2' {A B} (f g : A -> term) (h : A -> B)
           (rel : forall (Γ Γ' : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ Γ') f x y * on_Trel_eq (rel Γ2 Γ2') g h x y)%type.

Definition All2_prop2 Γ Γ' {A} (f g : A -> term)
           (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ) f x y * on_Trel (rel Γ') g x y)%type.

Lemma All2_All2_prop2_eq {A B} {P Q : context -> context -> term -> term -> Type} {par par' par2 par2'}
      {f g : A -> term} {h : A -> B} {l l' : list A} :
  All2_prop2_eq par par' par2 par2' f g h P l l' ->
  (forall par par' x y, P par par' x y -> Q par par' x y) ->
  All2_prop2_eq par par' par2 par2' f g h Q l l'.
Proof.
  intros H aux.
  induction H; constructor.
  - unfold on_Trel in *. split.
    + apply aux. destruct r. apply p.
    + split.
      * apply aux. apply r.
      * apply r.
  - apply IHAll2.
Defined.

(* Lemma All2_All2_prop2 {A} {P Q : context -> term -> term -> Type} {par par'} *)
(*       {f g : A -> term} {l l' : list A} : *)
(*   All2_prop2 par par' f g P l l' -> *)
(*   (forall par x y, P par x y -> Q par x y) -> *)
(*   All2_prop2 par par' f g Q l l'. *)
(* Proof. *)
(*   intros H aux. *)
(*   induction H; constructor. unfold on_Trel in *. split. *)
(*   apply aux. destruct r. apply p. apply aux. apply r. apply IHAll2. *)
(* Defined. *)

Section All2_local_env.

  Definition on_decl (P : context -> context -> term -> term -> Type)
             (Γ Γ' : context) (b : option (term * term)) (t t' : term) :=
    match b with
    | Some (b, b') => (P Γ Γ' b b' * P Γ Γ' t t')%type
    | None => P Γ Γ' t t'
    end.

  Definition on_decls (P : term -> term -> Type) (d d' : context_decl) :=
    match d.(decl_body), d'.(decl_body) with
    | Some b, Some b' => (P b b' * P d.(decl_type) d'.(decl_type))%type
    | None, None => P d.(decl_type) d'.(decl_type)
    | _, _ => False
    end.

  Section All_local_2.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).

    Inductive All2_local_env : context -> context -> Type :=
    | localenv2_nil : All2_local_env [] []
    | localenv2_cons_abs Γ Γ' na na' t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' None t t' ->
        All2_local_env (Γ ,, vass na t) (Γ' ,, vass na' t')
    | localenv2_cons_def Γ Γ' na na' b b' t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' (Some (b, b')) t t' ->
        All2_local_env (Γ ,, vdef na b t) (Γ' ,, vdef na' b' t').
  End All_local_2.

  Definition on_decl_over (P : context -> context -> term -> term -> Type) Γ Γ' :=
    fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ').

  Definition All2_local_env_over P Γ Γ' := All2_local_env (on_decl (on_decl_over P Γ Γ')).

  Lemma All2_local_env_impl {P Q : context -> context -> term -> term -> Type} {par par'} :
    All2_local_env (on_decl P) par par' ->
    (forall par par' x y, P par par' x y -> Q par par' x y) ->
    All2_local_env (on_decl Q) par par'.
  Proof.
    intros H aux.
    induction H; constructor.
    - auto.
    - red in p. apply aux, p.
    - apply IHAll2_local_env.
    - red. split.
      + apply aux. apply p.
      + apply aux. apply p.
  Defined.

  Lemma All2_local_env_app_inv :
    forall P (Γ Γ' Γl Γr : context),
      All2_local_env (on_decl P) Γ Γl ->
      All2_local_env (on_decl (on_decl_over P Γ Γl)) Γ' Γr ->
      All2_local_env (on_decl P) (Γ ,,, Γ') (Γl ,,, Γr).
  Proof.
    induction 2; auto.
    - simpl. constructor; auto.
    - simpl. constructor; auto.
  Qed.

  Lemma All2_local_env_length {P l l'} : @All2_local_env P l l' -> #|l| = #|l'|.
  Proof. induction 1; simpl; auto. Qed.

  Hint Extern 20 (#|?X| = #|?Y|) =>
    match goal with
      [ H : All2_local_env _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
    | [ H : All2_local_env _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
    | [ H : All2_local_env_over _ _ _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
    | [ H : All2_local_env_over _ _ _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
    end : pcuic.

  Ltac pcuic := eauto with pcuic.

  Derive Signature for All2_local_env.

  Lemma All2_local_env_app':
    forall P (Γ Γ' Γ'' : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') Γ'' ->
      ∑ Γl Γr, (Γ'' = Γl ,,, Γr) /\ #|Γ'| = #|Γr| /\ #|Γ| = #|Γl|.
  Proof.
    intros *.
    revert Γ''. induction Γ'.
    - simpl. intros.
      exists Γ'', []. intuition auto. eapply (All2_local_env_length X).
    - intros. unfold app_context in X. depelim X.
      + destruct (IHΓ' _ X) as [Γl [Γr [Heq HeqΓ]]]. subst Γ'0.
        eexists Γl, (Γr,, vass _ t'). simpl. intuition eauto.
      + destruct (IHΓ' _ X) as [Γl [Γr [Heq HeqΓ]]]. subst Γ'0.
        eexists Γl, (Γr,, vdef _ b' t'). simpl. intuition eauto.
  Qed.

  Lemma app_inj_length_r {A} (l l' r r' : list A) :
    app l r = app l' r' -> #|r| = #|r'| -> l = l' /\ r = r'.
  Proof.
    induction r in l, l', r' |- *.
    - destruct r'; intros; simpl in *; intuition auto; try discriminate.
      now rewrite !app_nil_r in H.
    - intros. destruct r'; try discriminate.
      simpl in H.
      change (l ++ a :: r) with (l ++ [a] ++ r) in H.
      change (l' ++ a0 :: r') with (l' ++ [a0] ++ r') in H.
      rewrite !app_assoc in H. destruct (IHr _ _ _ H).
      + now noconf H0.
      + subst. now apply app_inj_tail in H1 as [-> ->].
  Qed.

  Lemma app_inj_length_l {A} (l l' r r' : list A) :
    app l r = app l' r' -> #|l| = #|l'| -> l = l' /\ r = r'.
  Proof.
    induction l in r, r', l' |- *.
    - destruct l'; intros; simpl in *; intuition auto; try discriminate.
    - intros. destruct l'; try discriminate. simpl in *. noconf H.
      specialize (IHl _ _ _ H). forward IHl; intuition congruence.
  Qed.

  Lemma All2_local_env_app_ex:
    forall P (Γ Γ' Γ'' : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') Γ'' ->
      ∑ Γl Γr, (Γ'' = Γl ,,, Γr) *
      All2_local_env
        (on_decl P)
        Γ Γl * All2_local_env (on_decl (fun Δ Δ' => P (Γ ,,, Δ) (Γl ,,, Δ'))) Γ' Γr.
  Proof.
    intros *.
    revert Γ''. induction Γ'.
    - simpl. intros.
      exists Γ'', []. intuition auto. constructor.
    - intros. unfold app_context in X. depelim X.
      + destruct (IHΓ' _ X) as [Γl [Γr [[HeqΓ H2] H3]]]. subst.
        eexists _, _. intuition eauto.
        * unfold snoc, app_context.
          now rewrite app_comm_cons.
        * constructor. all: auto.
      + destruct (IHΓ' _ X) as [Γl [Γr [[HeqΓ H2] H3]]]. subst.
        eexists _, _. intuition eauto.
        * unfold snoc, app_context.
          now rewrite app_comm_cons.
        * constructor. all: auto.
  Qed.

  Lemma All2_local_env_app :
    forall P (Γ Γ' Γl Γr : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') (Γl ,,, Γr) ->
      #|Γ| = #|Γl| ->
      All2_local_env (on_decl P) Γ Γl * All2_local_env (on_decl (fun Δ Δ' => P (Γ ,,, Δ) (Γl ,,, Δ'))) Γ' Γr.
  Proof.
    intros *.
    intros. pose proof X as X'.
    apply All2_local_env_app' in X as [Γl' [Γr' ?]].
    destruct a as [? [? ?]].
    apply All2_local_env_app_ex in X' as [Γl2' [Γr2' [[? ?] ?]]].
    subst; rename_all_hyps.
    unfold app_context in heq_app_context.
    eapply app_inj_length_r in heq_app_context; try lia. destruct heq_app_context. subst.
    unfold app_context in heq_app_context0.
    eapply app_inj_length_r in heq_app_context0; try lia.
    - intuition subst; auto.
    - pose proof (All2_local_env_length a). lia.
  Qed.

  Lemma nth_error_pred1_ctx {P} {Γ Δ} i body' :
    All2_local_env (on_decl P) Γ Δ ->
    option_map decl_body (nth_error Δ i) = Some (Some body') ->
    { body & (option_map decl_body (nth_error Γ i) = Some (Some body)) *
             P (skipn (S i) Γ) (skipn (S i) Δ) body body' }%type.
  Proof.
    intros Hpred. revert i body'.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    - simpl in heq_option_map.
      specialize (IHHpred _ _ heq_option_map) as [body [Heq Hpred']].
      intuition eauto.
    - noconf heq_option_map. exists b. intuition eauto. cbv. apply p.
    - simpl in heq_option_map.
      specialize (IHHpred _ _ heq_option_map) as [body [Heq Hpred']].
      intuition eauto.
  Qed.

  Lemma nth_error_pred1_ctx_l {P} {Γ Δ} i body :
    All2_local_env (on_decl P) Γ Δ ->
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    { body' & (option_map decl_body (nth_error Δ i) = Some (Some body')) *
             P (skipn (S i) Γ) (skipn (S i) Δ) body body' }%type.
  Proof.
    intros Hpred. revert i body.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    - simpl in heq_option_map.
      specialize (IHHpred _ _ heq_option_map) as [body' [Heq Hpred']].
      intuition eauto.
    - noconf heq_option_map. exists b'. intuition eauto. cbv. apply p.
    - simpl in heq_option_map.
      specialize (IHHpred _ _ heq_option_map) as [body' [Heq Hpred']].
      intuition eauto.
  Qed.

  Lemma All2_local_env_over_app P {Γ0 Δ Γ'' Δ''} :
    All2_local_env (on_decl P) Γ0 Δ ->
    All2_local_env_over P Γ0 Δ Γ'' Δ'' ->
    All2_local_env (on_decl P) (Γ0 ,,, Γ'') (Δ ,,, Δ'').
  Proof.
    intros. induction X0; pcuic; constructor; pcuic.
  Qed.

  Lemma All2_local_env_app_left {P Γ Γ' Δ Δ'} :
    All2_local_env (on_decl P) (Γ ,,, Δ) (Γ' ,,, Δ') -> #|Γ| = #|Γ'| ->
    All2_local_env (on_decl P) Γ Γ'.
  Proof.
    intros. eapply All2_local_env_app in X; intuition auto.
  Qed.

End All2_local_env.

Section ParallelReduction.
  Context (Σ : global_env).

  Definition pred_atom t :=
    match t with
    | tVar _
    | tSort _
    | tInd _ _
    | tConstruct _ _ _ => true
    | _ => false
    end.

  Inductive pred1 (Γ Γ' : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | pred_beta na t0 t1 b0 b1 a0 a1 :
      pred1 Γ Γ' t0 t1 ->
      pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> pred1 Γ Γ' a0 a1 ->
      pred1 Γ Γ' (tApp (tLambda na t0 b0) a0) (subst10 a1 b1)

  (** Let *)
  | pred_zeta na d0 d1 t0 t1 b0 b1 :
      pred1 Γ Γ' t0 t1 ->
      pred1 Γ Γ' d0 d1 -> pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1 Γ Γ' (tLetIn na d0 t0 b0) (subst10 d1 b1)

  (** Local variables *)
  | pred_rel_def_unfold i body :
      All2_local_env (on_decl pred1) Γ Γ' ->
      option_map decl_body (nth_error Γ' i) = Some (Some body) ->
      pred1 Γ Γ' (tRel i) (lift0 (S i) body)

  | pred_rel_refl i :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred1 Γ Γ' (tRel i)  (tRel i)

  (** Case *)
  | pred_iota ind pars c u args0 args1 p brs0 brs1 :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2 (pred1 Γ Γ') args0 args1 ->
      All2 (on_Trel_eq (pred1 Γ Γ') snd fst) brs0 brs1 ->
      pred1 Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0)
            (iota_red pars c args1 brs1)

  (** Fix unfolding, with guard *)
  | pred_fix mfix0 mfix1 idx args0 args1 narg fn :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      unfold_fix mfix1 idx = Some (narg, fn) ->
      is_constructor narg args1 = true ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)

  (** CoFix-case unfolding *)
  | pred_cofix_case ip p0 p1 mfix0 mfix1 idx args0 args1 narg fn brs0 brs1 :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' p0 p1 ->
      All2 (on_Trel_eq (pred1 Γ Γ') snd fst) brs0 brs1 ->
      pred1 Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix0 idx) args0) brs0)
            (tCase ip p1 (mkApps fn args1) brs1)

  (** CoFix-proj unfolding *)
  | pred_cofix_proj p mfix0 mfix1 idx args0 args1 narg fn :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' (tProj p (mkApps (tCoFix mfix0 idx) args0))
            (tProj p (mkApps fn args1))

  (** Symbols and rewrite rules  *)

  | pred_symb k n u :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred1 Γ Γ' (tSymb k n u) (tSymb k n u)

  | pred_rewrite_rule k ui decl n r s s' :
      All2_local_env (on_decl pred1) Γ Γ' ->
      declared_symbol Σ k decl ->
      nth_error decl.(rules) n = Some r ->
      All2 (pred1 Γ Γ') s s' ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let lhs := subst0 s (subst ss #|s| (lhs r)) in
      let rhs := subst0 s' (subst ss #|s| (rhs r)) in
      pred1 Γ Γ' lhs rhs

  | pred_par_rewrite_rule k ui decl n r s s' :
      All2_local_env (on_decl pred1) Γ Γ' ->
      declared_symbol Σ k decl ->
      nth_error decl.(prules) n = Some r ->
      All2 (pred1 Γ Γ') s s' ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let lhs := subst0 s (subst ss #|s| (lhs r)) in
      let rhs := subst0 s' (subst ss #|s| (rhs r)) in
      pred1 Γ Γ' lhs rhs

  (** Constant unfolding *)

  | pred_delta c decl body (isdecl : declared_constant Σ c decl) u :
      All2_local_env (on_decl pred1) Γ Γ' ->
      decl.(cst_body) = Some body ->
      pred1 Γ Γ' (tConst c u) (subst_instance_constr u body)

  | pred_const c u :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred1 Γ Γ' (tConst c u) (tConst c u)

  (** Proj *)
  | pred_proj i pars narg k u args0 args1 arg1 :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2 (pred1 Γ Γ') args0 args1 ->
      nth_error args1 (pars + narg) = Some arg1 ->
      pred1 Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1

  (** Congruences *)
  | pred_abs na M M' N N' : pred1 Γ Γ' M M' -> pred1 (Γ ,, vass na M) (Γ' ,, vass na M') N N' ->
                            pred1 Γ Γ' (tLambda na M N) (tLambda na M' N')
  | pred_app M0 M1 N0 N1 :
      pred1 Γ Γ' M0 M1 ->
      pred1 Γ Γ' N0 N1 ->
      pred1 Γ Γ' (tApp M0 N0) (tApp M1 N1)
            (* do not handle mkApps yet *)

  | pred_letin na d0 d1 t0 t1 b0 b1 :
      pred1 Γ Γ' d0 d1 -> pred1 Γ Γ' t0 t1 -> pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1 Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)

  | pred_case ind p0 p1 c0 c1 brs0 brs1 :
      pred1 Γ Γ' p0 p1 ->
      pred1 Γ Γ' c0 c1 ->
      All2 (on_Trel_eq (pred1 Γ Γ') snd fst) brs0 brs1 ->
      pred1 Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)

  | pred_proj_congr p c c' :
      pred1 Γ Γ' c c' -> pred1 Γ Γ' (tProj p c) (tProj p c')

  | pred_fix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)

  | pred_cofix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)

  | pred_prod na M0 M1 N0 N1 : pred1 Γ Γ' M0 M1 -> pred1 (Γ ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
                               pred1 Γ Γ' (tProd na M0 N0) (tProd na M1 N1)

  | evar_pred ev l l' :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2 (pred1 Γ Γ') l l' -> pred1 Γ Γ' (tEvar ev l) (tEvar ev l')

  | pred_atom_refl t :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred_atom t -> pred1 Γ Γ' t t.

  Notation pred1_ctx Γ Γ' := (All2_local_env (on_decl pred1) Γ Γ').

  Ltac my_rename_hyp h th :=
    match th with
    | pred1_ctx _ _ ?G => fresh "pred" G
    | _ => PCUICWeakeningEnv.my_rename_hyp h th
    end.

  Ltac rename_hyp h ht ::= my_rename_hyp h ht.

  Definition extendP {P Q: context -> context -> term -> term -> Type}
             (aux : forall Γ Γ' t t', P Γ Γ' t t' -> Q Γ Γ' t t') :
    (forall Γ Γ' t t', P Γ Γ' t t' -> (P Γ Γ' t t' * Q Γ Γ' t t')).
  Proof.
    intros. split.
    - apply X.
    - apply aux. apply X.
  Defined.

  (* Lemma pred1_ind_all : *)
  (*   forall P : forall (Γ Γ' : context) (t t0 : term), Type, *)
  (*     let P' Γ Γ' x y := ((pred1 Γ Γ' x y) * P Γ Γ' x y)%type in *)
  (*     (forall (Γ Γ' : context) (na : name) (t0 t1 b0 b1 a0 a1 : term), *)
  (*         pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> P (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> *)
  (*         pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 -> *)
  (*         pred1 Γ Γ' a0 a1 -> P Γ Γ' a0 a1 -> P Γ Γ' (tApp (tLambda na t0 b0) a0) (b1 {0 := a1})) -> *)
  (*     (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term), *)
  (*         pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 -> *)
  (*         pred1 Γ Γ' d0 d1 -> P Γ Γ' d0 d1 -> *)
  (*         pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> *)
  (*         P (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (b1 {0 := d1})) -> *)
  (*     (forall (Γ Γ' : context) (i : nat) (body : term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         option_map decl_body (nth_error Γ' i) = Some (Some body) -> *)
  (*         P Γ Γ' (tRel i) (lift0 (S i) body)) -> *)
  (*     (forall (Γ Γ' : context) (i : nat), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         P Γ Γ' (tRel i) (tRel i)) -> *)
  (*     (forall (Γ Γ' : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args0 args1 : list term) *)
  (*             (p : term) (brs0 brs1 : list (nat * term)), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2 (P' Γ Γ') args0 args1 -> *)
  (*         All2_prop_eq Γ Γ' snd fst P' brs0 brs1 -> *)
  (*         P Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0) (iota_red pars c args1 brs1)) -> *)
  (*     (forall (Γ Γ' : context) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn0 fn1 : term), *)
  (*         unfold_fix mfix idx = Some (narg, fn0) -> *)
  (*         is_constructor narg args1 = true -> *)
  (*         All2 (P' Γ Γ') args0 args1 -> *)
  (*         pred1 Γ Γ' fn0 fn1 -> P Γ Γ' fn0 fn1 -> P Γ Γ' (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)) -> *)
  (*     (forall (Γ Γ' : context) (ip : inductive * nat) (p0 p1 : term) (mfix : mfixpoint term) (idx : nat) *)
  (*             (args0 args1 : list term) (narg : nat) (fn0 fn1 : term) (brs0 brs1 : list (nat * term)), *)
  (*         unfold_cofix mfix idx = Some (narg, fn0) -> *)
  (*         All2 (P' Γ Γ') args0 args1 -> *)
  (*         pred1 Γ Γ' fn0 fn1 -> *)
  (*         P Γ Γ' fn0 fn1 -> *)
  (*         pred1 Γ Γ' p0 p1 -> *)
  (*         P Γ Γ' p0 p1 -> *)
  (*         All2_prop_eq Γ Γ' snd fst P' brs0 brs1 -> *)
  (*         P Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0) (tCase ip p1 (mkApps fn1 args1) brs1)) -> *)
  (*     (forall (Γ Γ' : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term) *)
  (*             (narg : nat) (fn0 fn1 : term), *)
  (*         unfold_cofix mfix idx = Some (narg, fn0) -> *)
  (*         All2 (P' Γ Γ') args0 args1 -> *)
  (*         pred1 Γ Γ' fn0 fn1 -> P Γ Γ' fn0 fn1 -> *)
  (*         P Γ Γ' (tProj p (mkApps (tCoFix mfix idx) args0)) (tProj p (mkApps fn1 args1))) -> *)
  (*     (forall (Γ Γ' : context) (c : ident) (decl : constant_body) (body : term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         declared_constant Σ c decl -> *)
  (*         forall u : universe_instance, cst_body decl = Some body -> *)
  (*                                       P Γ Γ' (tConst c u) (subst_instance_constr u body)) -> *)
  (*     (forall (Γ Γ' : context) (c : ident) (u : universe_instance), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         P Γ Γ' (tConst c u) (tConst c u)) -> *)
  (*     (forall (Γ Γ' : context) (i : inductive) (pars narg : nat) (k : nat) (u : universe_instance) *)
  (*             (args0 args1 : list term) (arg1 : term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2 (pred1 Γ Γ') args0 args1 -> *)
  (*         All2 (P Γ Γ') args0 args1 -> *)
  (*         nth_error args1 (pars + narg) = Some arg1 -> *)
  (*         P Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1) -> *)
  (*     (forall (Γ Γ' : context) (na : name) (M M' N N' : term), *)
  (*         pred1 Γ Γ' M M' -> *)
  (*         P Γ Γ' M M' -> pred1 (Γ,, vass na M) (Γ' ,, vass na M') N N' -> *)
  (*         P (Γ,, vass na M) (Γ' ,, vass na M') N N' -> P Γ Γ' (tLambda na M N) (tLambda na M' N')) -> *)
  (*     (forall (Γ Γ' : context) (M0 M1 N0 N1 : term), *)
  (*         pred1 Γ Γ' M0 M1 -> P Γ Γ' M0 M1 -> pred1 Γ Γ' N0 N1 -> P Γ Γ' N0 N1 -> P Γ Γ' (tApp M0 N0) (tApp M1 N1)) -> *)
  (*     (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term), *)
  (*         pred1 Γ Γ' d0 d1 -> *)
  (*         P Γ Γ' d0 d1 -> *)
  (*         pred1 Γ Γ' t0 t1 -> *)
  (*         P Γ Γ' t0 t1 -> *)
  (*         pred1 (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> *)
  (*         P (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) -> *)
  (*     (forall (Γ Γ' : context) (ind : inductive * nat) (p0 p1 c0 c1 : term) (brs0 brs1 : list (nat * term)), *)
  (*         pred1 Γ Γ' p0 p1 -> *)
  (*         P Γ Γ' p0 p1 -> *)
  (*         pred1 Γ Γ' c0 c1 -> *)
  (*         P Γ Γ' c0 c1 -> All2_prop_eq Γ Γ' snd fst P' brs0 brs1 -> *)
  (*         P Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)) -> *)
  (*     (forall (Γ Γ' : context) (p : projection) (c c' : term), *)
  (*         pred1 Γ Γ' c c' -> P Γ Γ' c c' -> P Γ Γ' (tProj p c) (tProj p c')) -> *)

  (*     (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) -> *)
  (*         All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) -> *)
  (*         All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) *)
  (*                       dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 -> *)
  (*         P Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)) -> *)

  (*     (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) -> *)
  (*         All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) -> *)
  (*         All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 -> *)
  (*         P Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)) -> *)
  (*     (forall (Γ Γ' : context) (na : name) (M0 M1 N0 N1 : term), *)
  (*         pred1 Γ Γ' M0 M1 -> *)
  (*         P Γ Γ' M0 M1 -> pred1 (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> *)
  (*         P (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> P Γ Γ' (tProd na M0 N0) (tProd na M1 N1)) -> *)
  (*     (forall (Γ Γ' : context) (ev : nat) (l l' : list term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2 (P' Γ Γ') l l' -> P Γ Γ' (tEvar ev l) (tEvar ev l')) -> *)
  (*     (forall (Γ Γ' : context) (t : term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         pred_atom t -> P Γ Γ' t t) -> *)
  (*     forall (Γ Γ' : context) (t t0 : term), pred1 Γ Γ' t t0 -> P Γ Γ' t t0. *)
  (* Proof. *)
  (*   intros. revert Γ Γ' t t0 X20. *)
  (*   fix aux 5. intros Γ Γ' t t'. *)
  (*   move aux at top. *)
  (*   destruct 1; match goal with *)
  (*               | |- P _ _ (tFix _ _) (tFix _ _) => idtac *)
  (*               | |- P _ _ (tCoFix _ _) (tCoFix _ _) => idtac *)
  (*               | |- P _ _ (mkApps (tFix _ _) _) _ => idtac *)
  (*               | |- P _ _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac *)
  (*               | |- P _ _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac *)
  (*               | |- P _ _ (tRel _) _ => idtac *)
  (*               | |- P _ _ (tConst _ _) _ => idtac *)
  (*               | H : _ |- _ => eapply H; eauto *)
  (*               end. *)
  (*   - simpl. apply X1; auto. *)
  (*     apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - simpl. apply X2; auto. *)
  (*     apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 ((extendP aux) Γ Γ')). *)
  (*   - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) (g:=fst) a1 (extendP aux Γ Γ')). *)
  (*   - eapply X4; eauto. *)
  (*     eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')). *)
  (*   - eapply X5; eauto. *)
  (*     eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')). *)
  (*     eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a0 (extendP aux Γ Γ')). *)
  (*   - eapply X6; eauto. *)
  (*     eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')). *)
  (*   - eapply X7; eauto. *)
  (*     apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply X8; eauto. *)
  (*     apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply (All2_All2_prop (P:=pred1) (Q:=P) a0). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a (extendP aux Γ Γ')). *)
  (*   - eapply X15. *)
  (*     eapply (All2_local_env_impl a). intros. apply X20. *)
  (*     eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*     eapply (All2_local_env_impl a0). intros. red. exact X20. *)
  (*     eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20). *)
  (*     eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)). *)
  (*   - eapply X16. *)
  (*     eapply (All2_local_env_impl a). intros. apply X20. *)
  (*     eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*     eapply (All2_local_env_impl a0). intros. red. exact X20. *)
  (*     eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20). *)
  (*     eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)). *)
  (*   - eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 (extendP aux Γ Γ')). *)
  (*   - eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (* Defined. *)

  Lemma pred1_ind_all_ctx :
    forall (P : forall (Γ Γ' : context) (t t0 : term), Type)
           (Pctx : forall (Γ Γ' : context), Type),
           (* (Plist : forall {A} (f : A -> term), context -> context -> list A -> list A -> Type), *)
      let P' Γ Γ' x y := ((pred1 Γ Γ' x y) * P Γ Γ' x y)%type in
      (forall Γ Γ', All2_local_env (on_decl pred1) Γ Γ' -> All2_local_env (on_decl P) Γ Γ' -> Pctx Γ Γ') ->
      (* (forall (f : A -> term) (l l' : list A) (g : A -> B), *)
      (*     All2 (on_Trel pred1 f) l l' -> *)
      (*     All2 (on_Trel P f) l l' -> *)
      (*     All2 (on_Trel eq g) l l' -> *)
      (*     Plist f Γ Γ' l l') -> *)
      (forall (Γ Γ' : context) (na : name) (t0 t1 b0 b1 a0 a1 : term),
          pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> P (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 ->
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' a0 a1 -> P Γ Γ' a0 a1 -> P Γ Γ' (tApp (tLambda na t0 b0) a0) (b1 {0 := a1})) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' d0 d1 -> P Γ Γ' d0 d1 ->
          pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
          P (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (b1 {0 := d1})) ->
      (forall (Γ Γ' : context) (i : nat) (body : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          option_map decl_body (nth_error Γ' i) = Some (Some body) ->
          P Γ Γ' (tRel i) (lift0 (S i) body)) ->
      (forall (Γ Γ' : context) (i : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tRel i) (tRel i)) ->
      (forall (Γ Γ' : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args0 args1 : list term)
              (p : term) (brs0 brs1 : list (nat * term)),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') args0 args1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0) (iota_red pars c args1 brs1)) ->
      (forall (Γ Γ' : context) (mfix0 mfix1 : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_fix mfix1 idx = Some (narg, fn) ->
          is_constructor narg args1 = true ->
          All2 (P' Γ Γ') args0 args1 ->
          P Γ Γ' (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)) ->
      (forall (Γ Γ' : context) (ip : inductive * nat) (p0 p1 : term) (mfix0 mfix1 : mfixpoint term) (idx : nat)
              (args0 args1 : list term) (narg : nat) (fn : term) (brs0 brs1 : list (nat * term)),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ Γ') args0 args1 ->
          pred1 Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix0 idx) args0) brs0) (tCase ip p1 (mkApps fn args1) brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (mfix0 mfix1 : mfixpoint term)
         (idx : nat) (args0 args1 : list term)
         (narg : nat) (fn : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ Γ') args0 args1 ->
          P Γ Γ' (tProj p (mkApps (tCoFix mfix0 idx) args0)) (tProj p (mkApps fn args1))) ->
      (forall (Γ Γ' : context) (c : ident) (n : nat) (u : universe_instance),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tSymb c n u) (tSymb c n u)) ->
      (forall (Γ Γ' : context) k ui decl n r s s',
          All2_local_env (on_decl pred1) Γ Γ' ->
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
          All2_local_env (on_decl pred1) Γ Γ' ->
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
      (forall (Γ Γ' : context) (c : ident) (decl : constant_body) (body : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          declared_constant Σ c decl ->
          forall u : universe_instance, cst_body decl = Some body ->
                                        P Γ Γ' (tConst c u) (subst_instance_constr u body)) ->
      (forall (Γ Γ' : context) (c : ident) (u : universe_instance),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tConst c u) (tConst c u)) ->
      (forall (Γ Γ' : context) (i : inductive) (pars narg : nat) (k : nat) (u : universe_instance)
              (args0 args1 : list term) (arg1 : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (pred1 Γ Γ') args0 args1 ->
          All2 (P Γ Γ') args0 args1 ->
          nth_error args1 (pars + narg) = Some arg1 ->
          P Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1) ->
      (forall (Γ Γ' : context) (na : name) (M M' N N' : term),
          pred1 Γ Γ' M M' ->
          P Γ Γ' M M' -> pred1 (Γ,, vass na M) (Γ' ,, vass na M') N N' ->
          P (Γ,, vass na M) (Γ' ,, vass na M') N N' -> P Γ Γ' (tLambda na M N) (tLambda na M' N')) ->
      (forall (Γ Γ' : context) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 -> P Γ Γ' M0 M1 -> pred1 Γ Γ' N0 N1 ->
          P Γ Γ' N0 N1 -> P Γ Γ' (tApp M0 N0) (tApp M1 N1)) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' d0 d1 ->
          P Γ Γ' d0 d1 ->
          pred1 Γ Γ' t0 t1 ->
          P Γ Γ' t0 t1 ->
          pred1 (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 ->
          P (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) ->
      (forall (Γ Γ' : context) (ind : inductive * nat) (p0 p1 c0 c1 : term) (brs0 brs1 : list (nat * term)),
          pred1 Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          pred1 Γ Γ' c0 c1 ->
          P Γ Γ' c0 c1 -> All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (c c' : term), pred1 Γ Γ' c c' -> P Γ Γ' c c' -> P Γ Γ' (tProj p c) (tProj p c')) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                        dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
      (forall (Γ Γ' : context) (na : name) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 ->
          P Γ Γ' M0 M1 -> pred1 (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
          P (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> P Γ Γ' (tProd na M0 N0) (tProd na M1 N1)) ->
      (forall (Γ Γ' : context) (ev : nat) (l l' : list term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') l l' -> P Γ Γ' (tEvar ev l) (tEvar ev l')) ->
      (forall (Γ Γ' : context) (t : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          pred_atom t -> P Γ Γ' t t) ->
      forall (Γ Γ' : context) (t t0 : term), pred1 Γ Γ' t t0 -> P Γ Γ' t t0.
  Proof.
    intros P Pctx P' Hctx.
    intros X X0 X1 X2 X3 X4 X5 X6 X7 Xrw Xprw X8 X9 X10 X11 X12 X13 X14 X15 X16
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
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) (g:=fst) a1 (extendP aux Γ Γ')).
    - eapply X4; eauto.
      + apply Hctx, (All2_local_env_impl a). 1: exact a.
        intros. apply (aux _ _ _ _ X21).
      + eapply (All2_local_env_impl a0). intros. red. red in X21.
        apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      + eapply (All2_All2_prop (P:=pred1) (Q:=P') a2 (extendP aux Γ Γ')).
    - eapply X5; eauto.
      + apply Hctx, (All2_local_env_impl a). 1: exact a.
        intros. apply (aux _ _ _ _ X22).
      + eapply (All2_local_env_impl a0). intros. red. red in X22.
        apply (aux _ _ _ _ X22).
      + eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      + eapply (All2_All2_prop (P:=pred1) (Q:=P') a2 (extendP aux Γ Γ')).
      + eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a3 (extendP aux Γ Γ')).
    - eapply X6; eauto.
      + apply Hctx, (All2_local_env_impl a). 1: exact a.
        intros. apply (aux _ _ _ _ X21).
      + eapply (All2_local_env_impl a0). intros. red. red in X21. apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      + eapply (All2_All2_prop (P:=pred1) (Q:=P') a2 (extendP aux Γ Γ')).
    - eapply X7. 1: assumption.
      apply Hctx, (All2_local_env_impl a).
      + intros. exact a.
      + intros. apply (aux _ _ _ _ X21).
    - eapply Xrw. all: eauto.
      + apply Hctx. 1: auto.
        apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply Xprw. all: eauto.
      + apply Hctx. 1: auto.
        apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
      + eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply X8; eauto.
      apply Hctx, (All2_local_env_impl a).
      + intros. exact a.
      + intros. apply (aux _ _ _ _ X21).
    - eapply X9; eauto.
      apply Hctx, (All2_local_env_impl a). 1: exact a.
      intros. apply (aux _ _ _ _ X21).
    - apply Hctx, (All2_local_env_impl a). 1: exact a.
      intros. apply (aux _ _ _ _ X21).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P) a0). intros. apply (aux _ _ _ _ X21).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a (extendP aux Γ Γ')).
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
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 (extendP aux Γ Γ')).
    - eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X21).
  Defined.

  Lemma pred1_refl_gen Γ Γ' t : pred1_ctx Γ Γ' -> pred1 Γ Γ' t t.
  Proof.
    revert Γ'.
    unshelve einduction Γ, t using term_forall_ctx_list_ind;
    intros;
      try solve [(apply pred_atom; reflexivity) || constructor; auto];
      try solve [try red in X; constructor; unfold All2_prop2_eq, All2_prop2, on_Trel in *; solve_all];
      intros.
    - constructor; eauto. eapply IHt0_2.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply IHt0_2.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply IHt0_3.
      constructor; try red; eauto with pcuic.
    - assert (All2_local_env (on_decl (fun Δ Δ' : context => pred1 (Γ0 ,,, Δ) (Γ' ,,, Δ')))
                             (fix_context m) (fix_context m)).
      { revert X. clear -X1. generalize (fix_context m).
        intros c H1. induction H1; constructor; auto.
        - red in t0. red. eapply t0. eapply All2_local_env_app_inv; auto.
        - red in t1. red. split.
          + eapply t1. eapply All2_local_env_app_inv; auto.
          + eapply t1. eapply All2_local_env_app_inv; auto.
      }
      constructor; auto. red.
      unfold All2_prop_eq, on_Trel in *.
      eapply All_All2; eauto. simpl; intros.
      split; eauto. 1: eapply X3; auto.
      split. 2: auto.
      eapply X3. eapply All2_local_env_app_inv; auto.
    - assert (All2_local_env (on_decl (fun Δ Δ' : context => pred1 (Γ0 ,,, Δ) (Γ' ,,, Δ')))
                             (fix_context m) (fix_context m)).
      { revert X. clear -X1. generalize (fix_context m).
        intros c H1. induction H1; constructor; auto.
        - red in t0. red. eapply t0. eapply All2_local_env_app_inv; auto.
        - red in t1. red. split.
          + eapply t1. eapply All2_local_env_app_inv; auto.
          + eapply t1. eapply All2_local_env_app_inv; auto.
      }
      constructor; auto. red.
      eapply All_All2; eauto. simpl; intros.
      split; eauto. 1: eapply X3; auto.
      split. 2: auto.
      eapply X3. eapply All2_local_env_app_inv; auto.
  Qed.

  Lemma pred1_ctx_refl Γ : pred1_ctx Γ Γ.
  Proof.
    induction Γ. 1: constructor.
    destruct a as [na [b|] ty]; constructor; try red; simpl; auto with pcuic.
    - split; now apply pred1_refl_gen.
    - apply pred1_refl_gen, IHΓ.
  Qed.
  Hint Resolve pred1_ctx_refl : pcuic.

  Lemma pred1_refl Γ t : pred1 Γ Γ t t.
  Proof. apply pred1_refl_gen, pred1_ctx_refl. Qed.

  Lemma pred1_pred1_ctx {Γ Δ t u} : pred1 Γ Δ t u -> pred1_ctx Γ Δ.
  Proof.
    intros H; revert Γ Δ t u H.
    refine (pred1_ind_all_ctx _ (fun Γ Γ' => pred1_ctx Γ Γ') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [eexists; split; constructor; eauto].
  Qed.

  Lemma pred1_ctx_over_refl Γ Δ : All2_local_env (on_decl (on_decl_over pred1 Γ Γ)) Δ Δ.
  Proof.
    induction Δ as [|[na [b|] ty] Δ]; constructor; auto.
    - red. split; red; apply pred1_refl.
    - red. apply pred1_refl.
  Qed.

End ParallelReduction.

Hint Constructors pred1 : pcuic.
Hint Unfold All2_prop2_eq All2_prop2 on_decl on_decl_over on_rel on_Trel snd on_snd : pcuic.
Hint Resolve All2_same: pcuic.
Hint Constructors All2_local_env : pcuic.

Hint Resolve pred1_ctx_refl : pcuic.

Ltac pcuic_simplify :=
  simpl || split || destruct_conjs || red.

Hint Extern 10 => progress pcuic_simplify : pcuic.

Notation pred1_ctx Σ Γ Γ' := (All2_local_env (on_decl (pred1 Σ)) Γ Γ').

Hint Extern 4 (pred1 _ _ _ ?t _) => tryif is_evar t then fail 1 else eapply pred1_refl_gen : pcuic.
Hint Extern 4 (pred1 _ _ _ ?t _) => tryif is_evar t then fail 1 else eapply pred1_refl : pcuic.

Hint Extern 20 (#|?X| = #|?Y|) =>
match goal with
  [ H : All2_local_env _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
| [ H : All2_local_env _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
| [ H : All2_local_env_over _ _ _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
| [ H : All2_local_env_over _ _ _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
end : pcuic.

Hint Extern 4 (pred1_ctx ?Σ ?Γ ?Γ') =>
  match goal with
  | [ H : pred1_ctx Σ (Γ ,,, _) (Γ' ,,, _) |- _ ] => apply (All2_local_env_app_left H)
  | [ H : pred1 Σ Γ Γ' _ _ |- _ ] => apply (pred1_pred1_ctx _ H)
  end : pcuic.

Ltac pcuic := try repeat red; cbn in *; try solve [intuition auto; eauto with pcuic || ltac:(try (lia || congruence))].

Ltac my_rename_hyp h th :=
  match th with
  | pred1_ctx _ _ ?G => fresh "pred" G
  | _ => PCUICWeakeningEnv.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma All2_local_env_over_refl {Σ Γ Δ Γ'} :
  pred1_ctx Σ Γ Δ -> All2_local_env_over (pred1 Σ) Γ Δ Γ' Γ'.
Proof.
  intros X0.
  red. induction Γ'. 1: constructor.
  pose proof IHΓ'. apply All2_local_env_over_app in IHΓ'; auto.
  destruct a as [na [b|] ty]; constructor; pcuic.
Qed.

Hint Extern 4 (All2_local_env_over _ _ _ ?X) =>
  tryif is_evar X then fail 1 else eapply All2_local_env_over_refl : pcuic.

Section ParallelWeakening.
  Context {cf : checker_flags}.
  (* Lemma All2_local_env_over_app_inv {Σ Γ0 Δ Γ'' Δ''} : *)
  (*   pred1_ctx Σ (Γ0 ,,, Γ'') (Δ ,,, Δ'') -> *)
  (*   pred1_ctx Σ Γ0 Δ -> *)
  (*   All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' -> *)

  (* Proof. *)
  (*   intros. induction X0; pcuic; constructor; pcuic. *)
  (* Qed. *)

  Lemma All2_local_env_weaken_pred_ctx {Σ Γ0 Γ'0 Δ Δ' Γ'' Δ''} :
      #|Γ0| = #|Δ| ->
  pred1_ctx Σ Γ0 Δ ->
  All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' ->
  All2_local_env
    (on_decl
       (fun (Γ Γ' : context) (t t0 : term) =>
        forall Γ1 Γ'1 : context,
        Γ = Γ1 ,,, Γ'1 ->
        forall Δ0 Δ'0 : context,
        Γ' = Δ0 ,,, Δ'0 ->
        #|Γ1| = #|Δ0| ->
        forall Γ''0 Δ''0 : context,
        All2_local_env_over (pred1 Σ) Γ1 Δ0 Γ''0 Δ''0 ->
        pred1 Σ (Γ1 ,,, Γ''0 ,,, lift_context #|Γ''0| 0 Γ'1) (Δ0 ,,, Δ''0 ,,, lift_context #|Δ''0| 0 Δ'0)
          (lift #|Γ''0| #|Γ'1| t) (lift #|Δ''0| #|Δ'0| t0))) (Γ0 ,,, Γ'0) (Δ ,,, Δ') ->

  pred1_ctx Σ (Γ0 ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'0) (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ').
  Proof.
    intros.
    pose proof (All2_local_env_length X0).
    eapply All2_local_env_app in X1 as [Xl Xr]; auto.
    induction Xr; simpl; auto.
    - apply All2_local_env_over_app; pcuic.
    - rewrite !lift_context_snoc. simpl. constructor. 1: auto.
      red in p. specialize (p _ _ eq_refl _ _ eq_refl).
      forward p by auto.
      red. rewrite !Nat.add_0_r. simpl. specialize (p Γ'' Δ'').
      forward p. 1: auto.
      pose proof (All2_local_env_length X0).
      rewrite H0 in p. congruence.
    - destruct p.
      specialize (p _ _ eq_refl _ _ eq_refl H _ _ X0).
      specialize (p0 _ _ eq_refl _ _ eq_refl H _ _ X0).
      rewrite !lift_context_snoc. simpl. constructor; auto.
      red. split; auto.
      + rewrite !Nat.add_0_r. rewrite H0 in p. simpl. congruence.
      + rewrite !Nat.add_0_r. rewrite H0 in p0. simpl. congruence.
  Qed.

  Lemma All2_local_env_weaken_pred_ctx' {Σ Γ0 Γ'0 Δ Δ' Γ'' Δ''} ctx ctx' :
      #|Γ0| = #|Δ| -> #|Γ0 ,,, Γ'0| = #|Δ ,,, Δ'| ->
  pred1_ctx Σ Γ0 Δ ->
  All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' ->
  All2_local_env
    (on_decl
       (on_decl_over
          (fun (Γ Γ' : context) (t t0 : term) =>
           forall Γ1 Γ'1 : context,
           Γ = Γ1 ,,, Γ'1 ->
           forall Δ0 Δ'0 : context,
           Γ' = Δ0 ,,, Δ'0 ->
           #|Γ1| = #|Δ0| ->
           forall Γ''0 Δ''0 : context,
           All2_local_env_over (pred1 Σ) Γ1 Δ0 Γ''0 Δ''0 ->
           pred1 Σ (Γ1 ,,, Γ''0 ,,, lift_context #|Γ''0| 0 Γ'1) (Δ0 ,,, Δ''0 ,,, lift_context #|Δ''0| 0 Δ'0)
             (lift #|Γ''0| #|Γ'1| t) (lift #|Δ''0| #|Δ'0| t0)) (Γ0 ,,, Γ'0) (Δ ,,, Δ')))
    ctx ctx' ->
  All2_local_env
    (on_decl
       (on_decl_over (pred1 Σ) (Γ0 ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'0) (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')))
    (lift_context #|Γ''| #|Γ'0| ctx) (lift_context #|Δ''| #|Δ'| ctx').
  Proof.
    intros.
    pose proof (All2_local_env_length X0).
    induction X1; simpl; rewrite ?lift_context_snoc0; constructor; auto.
    - red in p. red in p. red. red. simpl.
      specialize (p Γ0 (Γ'0,,, Γ)).
      rewrite app_context_assoc in p. forward p by auto.
      specialize (p Δ (Δ',,, Γ')).
      rewrite app_context_assoc in p. forward p by auto.
      specialize (p H _ _ X0).
      rewrite !app_context_length !lift_context_app !app_context_assoc !Nat.add_0_r in p.
      congruence.
    - destruct p.
      specialize (o Γ0 (Γ'0,,, Γ) ltac:(now rewrite app_context_assoc) Δ (Δ',,, Γ')
                                  ltac:(now rewrite app_context_assoc) H _ _ X0).
      rewrite !app_context_length !lift_context_app !app_context_assoc !Nat.add_0_r in o.
      specialize (o0 Γ0 (Γ'0,,, Γ) ltac:(now rewrite app_context_assoc) Δ (Δ',,, Γ')
                                  ltac:(now rewrite app_context_assoc) H _ _ X0).
      rewrite !app_context_length !lift_context_app !app_context_assoc !Nat.add_0_r in o0.
      red. split; auto.
  Qed.

  Lemma map_cofix_subst f mfix :
    (forall n, tCoFix (map (map_def (f 0) (f #|mfix|)) mfix) n = f 0 (tCoFix mfix n)) ->
    cofix_subst (map (map_def (f 0) (f #|mfix|)) mfix) =
    map (f 0) (cofix_subst mfix).
  Proof.
    unfold cofix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 2 3.
    induction n. 1: reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma map_fix_subst f mfix :
    (forall n, tFix (map (map_def (f 0) (f #|mfix|)) mfix) n = f 0 (tFix mfix n)) ->
    fix_subst (map (map_def (f 0) (f #|mfix|)) mfix) =
    map (f 0) (fix_subst mfix).
  Proof.
    unfold fix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 2 3.
    induction n. 1: reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma weakening_pred1 Σ Γ Γ' Γ'' Δ Δ' Δ'' M N : wf Σ ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') M N ->
    #|Γ| = #|Δ| ->
    All2_local_env_over (pred1 Σ) Γ Δ Γ'' Δ'' ->
    pred1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
          (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')
          (lift #|Γ''| #|Γ'| M) (lift #|Δ''| #|Δ'| N).
  Proof.
    intros wfΣ H.

    remember (Γ ,,, Γ') as Γ0.
    remember (Δ ,,, Δ') as Δ0.
    intros HΓ.
    revert Γ Γ' HeqΓ0 Δ Δ' HeqΔ0 HΓ Γ'' Δ''.
    revert Γ0 Δ0 M N H.

    set (Pctx :=
           fun (Γ0 Δ0 : context) =>
             forall Γ Γ' : context,
               Γ0 = Γ ,,, Γ' ->
               forall Δ Δ' : context,
                 Δ0 = Δ ,,, Δ' ->
                 #|Γ| = #|Δ| ->
           forall Γ'' Δ'' : context,
             All2_local_env_over (pred1 Σ) Γ Δ Γ'' Δ'' ->
             pred1_ctx Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')).

    refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; intros; subst Pctx;
      rename_all_hyps; try subst Γ Γ'; simplify_IH_hyps; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try specialize (forall_Γ _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try specialize (forall_Γ0 _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try pose proof (All2_local_env_length X0);
      try specialize (X0 _ _ eq_refl _ _ eq_refl heq_length _ _ ltac:(eauto));
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel, id in *.

    - (* Contexts *)
      intros. subst.
      eapply All2_local_env_over_app.
      + eapply All2_local_env_over_app; pcuic.
      + eapply All2_local_env_app in X0; auto.
        destruct X0.
        induction a0; rewrite ?lift_context_snoc0; cbn; constructor; pcuic.
        * apply IHa0.
          -- depelim predΓ'.
             ++ hnf in H, H0. noconf H. noconf H0. assumption.
             ++ hnf in H, H0. noconf H.
          -- unfold ",,,". lia.
        * now rewrite !Nat.add_0_r.
        * apply IHa0; auto. depelim predΓ'.
          all: hnf in H, H0. all: noconf H. noconf H0. assumption.
        * split; red; now rewrite !Nat.add_0_r.

    - (* Beta *)
      specialize (forall_Γ _ (Γ'0,, vass na t0) eq_refl _ (Δ' ,, vass na t1) eq_refl heq_length _ _ X5).
      specialize (forall_Γ1 _ _ eq_refl _ _ eq_refl heq_length _ _ X5).
      econstructor; now rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ1 _ (Γ'0,, vdef na d0 t0) eq_refl _ (Δ',, vdef na d1 t1)
                            eq_refl heq_length _ _ X5).
      simpl. econstructor; eauto.
      now rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ1.

    - (* Rel unfold *)
      assert(#|Γ''| = #|Δ''|).
      { red in X1. pcuic. }
      elim (leb_spec_Set); intros Hn.
      + destruct nth_error eqn:Heq; noconf heq_option_map.
        pose proof (nth_error_Some_length Heq).
        rewrite !app_context_length in H1.
        assert (#|Γ'0| = #|Δ'|).
        { pcuic. eapply All2_local_env_app in X0 as [? ?].
          - eapply All2_local_env_length in a0.
            now rewrite !lift_context_length in a0.
          - rewrite !app_context_length; eauto.
        }
        rewrite simpl_lift; try lia.
        rewrite - {2}H0.
        assert (#|Γ''| + S i = S (#|Γ''| + i)) as -> by lia.
        econstructor; auto.
        rewrite H0. rewrite <- weaken_nth_error_ge; auto. 2: lia.
        rewrite Heq.
        simpl in H. simpl. f_equal. auto.

      + (* Local variable *)
        pose proof (All2_local_env_length predΓ').
        rewrite !app_context_length in H0.
        rewrite <- lift_simpl; pcuic.
        econstructor; auto.
        rewrite (weaken_nth_error_lt); try lia.
        now rewrite option_map_decl_body_map_decl heq_option_map.

    - (* Rel refl *)
      pose proof (All2_local_env_length X0).
      assert(#|Γ''| = #|Δ''|).
      { red in X1. pcuic. }
      rewrite !app_context_length !lift_context_length in H.
      assert (#|Γ'0| = #|Δ'|) by lia.
      rewrite H1.
      elim (leb_spec_Set); intros Hn.
      + rewrite H0. now econstructor.
      + now constructor.

    - assert(#|Γ''| = #|Δ''|).
      { red in X3; pcuic. }
      pose proof (All2_local_env_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      rewrite lift_iota_red.
      autorewrite with lift.
      constructor; auto.
      + apply All2_map. solve_all.
      + apply All2_map. solve_all.

    - assert(#|Γ''| = #|Δ''|) by pcuic.
      pose proof (All2_local_env_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      unfold unfold_fix in heq_unfold_fix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_fix. simpl.
      econstructor; pcuic.
      + rewrite !lift_fix_context.
        erewrite lift_fix_context.
        eapply All2_local_env_weaken_pred_ctx'; pcuic.
      + apply All2_map. clear X4. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ ltac:(eauto)).
        rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
        now rewrite !lift_fix_context.
      + unfold unfold_fix. rewrite nth_error_map. rewrite Hnth. simpl.
        destruct (isLambda (dbody d)) eqn:isl; noconf heq_unfold_fix.
        rewrite isLambda_lift //.
        f_equal. f_equal.
        rewrite distr_lift_subst. rewrite fix_subst_length. f_equal.
        now rewrite (map_fix_subst (fun k => lift #|Δ''| (k + #|Δ'|))).
      + eapply All2_map. solve_all.

    - assert(#|Γ''| = #|Δ''|) by pcuic.
      pose proof (All2_local_env_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor; pcuic.
      + rewrite !lift_fix_context.
        erewrite lift_fix_context.
        eapply All2_local_env_weaken_pred_ctx'; pcuic.
      + apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ1 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ1 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ ltac:(eauto)).
        rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ1.
        now rewrite !lift_fix_context.
      + unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
        f_equal. f_equal.
        rewrite distr_lift_subst. rewrite cofix_subst_length. f_equal.
        now rewrite (map_cofix_subst (fun k => lift #|Δ''| (k + #|Δ'|))).
      + eapply All2_map. solve_all.
      + eapply All2_map. solve_all.

    - assert(#|Γ''| = #|Δ''|) by pcuic.
      pose proof (All2_local_env_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor ; pcuic.
      + rewrite !lift_fix_context.
        erewrite lift_fix_context.
        eapply All2_local_env_weaken_pred_ctx'; pcuic.
      + apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ ltac:(eauto)).
        rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
        now rewrite !lift_fix_context.
      + unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
        f_equal. f_equal.
        rewrite distr_lift_subst. rewrite cofix_subst_length. f_equal.
        now rewrite (map_cofix_subst (fun k => lift #|Δ''| (k + #|Δ'|))).
      + eapply All2_map. solve_all.

    - assert (es : #|s| = #|s'|).
      { eapply All2_length. eassumption. }
      rewrite <- es.
      rewrite 2!distr_lift_subst_rec.
      assert (e : forall i j, map (lift i j) ss = ss).
      { intros i j. subst ss. unfold symbols_subst.
        rewrite list_make_map. simpl. reflexivity.
      }
      rewrite 2!e.
      rewrite lift_closed.
      1:{ eapply closed_upwards. 1: eapply PCUICClosed.closed_rule_lhs.
          all: eauto.
          subst ss. rewrite symbols_subst_length.
          eapply untyped_subslet_length in H1.
          rewrite subst_context_length in H1.
          lia.
      }
      rewrite lift_closed.
      1:{ eapply closed_upwards. 1: eapply PCUICClosed.closed_rule_rhs.
          all: eauto.
          subst ss. rewrite symbols_subst_length.
          eapply untyped_subslet_length in H1.
          rewrite subst_context_length in H1.
          lia.
      }
      replace #|s| with #|map (lift #|Γ''| #|Γ'0|) s|
        by (now rewrite map_length).
      eapply pred_rewrite_rule. all: eauto.
      + apply All2_map. eapply All2_impl. 1: eassumption.
        cbn. intros ? ? [? ih].
        apply ih. all: auto.
      + eapply untyped_subslet_lift with (Γ2 := Γ'') in H1 as h.
        eapply PCUICClosed.closed_declared_symbol_pat_context in H as hcl.
        2-3: eassumption.
        rewrite -> (closed_ctx_lift _ #|Γ'0|) in h.
        1: assumption.
        eapply closedn_ctx_subst_context0.
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

    - assert (es : #|s| = #|s'|).
      { eapply All2_length. eassumption. }
      rewrite <- es.
      rewrite 2!distr_lift_subst_rec.
      assert (e : forall i j, map (lift i j) ss = ss).
      { intros i j. subst ss. unfold symbols_subst.
        rewrite list_make_map. simpl. reflexivity.
      }
      rewrite 2!e.
      rewrite lift_closed.
      1:{ eapply closed_upwards. 1: eapply PCUICClosed.closed_prule_lhs.
          all: eauto.
          subst ss. rewrite symbols_subst_length.
          eapply untyped_subslet_length in H1.
          rewrite subst_context_length in H1.
          lia.
      }
      rewrite lift_closed.
      1:{ eapply closed_upwards. 1: eapply PCUICClosed.closed_prule_rhs.
          all: eauto.
          subst ss. rewrite symbols_subst_length.
          eapply untyped_subslet_length in H1.
          rewrite subst_context_length in H1.
          lia.
      }
      replace #|s| with #|map (lift #|Γ''| #|Γ'0|) s|
        by (now rewrite map_length).
      eapply pred_par_rewrite_rule. all: eauto.
      + apply All2_map. eapply All2_impl. 1: eassumption.
        cbn. intros ? ? [? ih].
        apply ih. all: auto.
      + eapply untyped_subslet_lift with (Γ2 := Γ'') in H1 as h.
        eapply PCUICClosed.closed_declared_symbol_par_pat_context in H as hcl.
        2-3: eassumption.
        rewrite -> (closed_ctx_lift _ #|Γ'0|) in h.
        1: assumption.
        eapply closedn_ctx_subst_context0.
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

    - assert(Hlen:#|Γ''| = #|Δ''|).
      { eapply All2_local_env_length in X1; pcuic. }
      pose proof (lift_declared_constant _ _ _ #|Δ''| #|Δ'| wfΣ H).
      econstructor; eauto.
      rewrite H0.
      now rewrite - !map_cst_body heq_cst_body.

    - simpl. eapply pred_proj with (map (lift #|Δ''| #|Δ'|) args1).
      + auto.
      + eapply All2_map; solve_all.
      + now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 Γ0 (_ ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X3).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 Γ0 (_ ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X5).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ1.
      econstructor; eauto.

    - econstructor; pcuic.
      + rewrite !lift_fix_context. revert X2.
        eapply All2_local_env_weaken_pred_ctx'; pcuic.
      + apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ _ _ eq_refl _ _ eq_refl heq_length _ _ X4).
        specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ X4).
        rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
        now rewrite !lift_fix_context.

    - econstructor; pcuic.
      + rewrite !lift_fix_context. revert X2.
        eapply All2_local_env_weaken_pred_ctx'; pcuic.
      + apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ _ _ eq_refl _ _ eq_refl heq_length _ _ X4).
        specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ X4).
        rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
        now rewrite !lift_fix_context.

    - specialize (forall_Γ0 Γ0 (Γ'0 ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X3).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Lemma weakening_pred1_pred1 Σ Γ Δ Γ' Δ' M N : wf Σ ->
    All2_local_env_over (pred1 Σ) Γ Δ Γ' Δ' ->
    pred1 Σ Γ Δ M N ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') (lift0 #|Γ'| M) (lift0 #|Δ'| N).
  Proof.
    intros; apply (weakening_pred1 Σ Γ [] Γ' Δ [] Δ' M N); eauto.
    eapply pred1_pred1_ctx in X1. pcuic.
  Qed.

  Lemma weakening_pred1_0 Σ Γ Δ Γ' M N : wf Σ ->
    pred1 Σ Γ Δ M N ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Γ') (lift0 #|Γ'| M) (lift0 #|Γ'| N).
  Proof.
    intros; apply (weakening_pred1 Σ Γ [] Γ' Δ [] Γ' M N); eauto.
    - eapply pred1_pred1_ctx in X0. pcuic.
    - eapply pred1_pred1_ctx in X0.
      apply All2_local_env_over_refl; auto.
  Qed.

  Lemma All2_local_env_over_pred1_ctx Σ Γ Γ' Δ Δ' :
    #|Δ| = #|Δ'| ->
    pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ') ->
    All2_local_env
      (on_decl (on_decl_over (pred1 Σ) Γ Γ')) Δ Δ'.
  Proof.
    intros. pose proof (All2_local_env_length X).
    apply All2_local_env_app in X.
    - intuition.
    - auto. rewrite !app_context_length in H0. pcuic.
  Qed.
  Hint Resolve All2_local_env_over_pred1_ctx : pcuic.

  Lemma nth_error_pred1_ctx_all_defs {P} {Γ Δ} :
    All2_local_env (on_decl P) Γ Δ ->
    forall i body body', option_map decl_body (nth_error Γ i) = Some (Some body) ->
              option_map decl_body (nth_error Δ i) = Some (Some body') ->
              P (skipn (S i) Γ) (skipn (S i) Δ) body body'.
  Proof.
    induction 1; destruct i; simpl; try discriminate.
    - intros. apply IHX; auto.
    - intros ? ? [= ->] [= ->]. apply p.
    - intros ? ? ? ?. apply IHX; auto.
  Qed.

  Lemma All2_local_env_over_firstn_skipn:
    forall (Σ : global_env) (i : nat) (Δ' R : context),
      pred1_ctx Σ Δ' R ->
      All2_local_env_over (pred1 Σ) (skipn i Δ') (skipn i R) (firstn i Δ') (firstn i R).
  Proof.
    intros Σ i Δ' R redr.
    induction redr in i |- *; simpl.
    - destruct i; constructor; pcuic.
    - destruct i; simpl; constructor; pcuic.
      + apply IHredr.
      + repeat red. now rewrite /app_context !firstn_skipn.
    - repeat red. red in p.
      destruct i; simpl; constructor; pcuic.
      + apply IHredr.
      + repeat red. destruct p.
        split; red; now rewrite /app_context !firstn_skipn.
  Qed.

End ParallelWeakening.

Hint Resolve pred1_pred1_ctx : pcuic.

Section ParallelSubstitution.
  Context {cf : checker_flags}.

  Inductive psubst Σ (Γ Γ' : context) : list term -> list term -> context -> context -> Type :=
  | psubst_empty : psubst Σ Γ Γ' [] [] [] []
  | psubst_vass Δ Δ' s s' na na' t t' T T' :
      psubst Σ Γ Γ' s s' Δ Δ' ->
      pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') T T' ->
      pred1 Σ Γ Γ' t t' ->
      psubst Σ Γ Γ' (t :: s) (t' :: s') (Δ ,, vass na T) (Δ' ,, vass na' T')
  | psubst_vdef Δ Δ' s s' na na' t t' T T' :
      psubst Σ Γ Γ' s s' Δ Δ' ->
      pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') T T' ->
      pred1 Σ Γ Γ' (subst0 s t) (subst0 s' t') ->
      psubst Σ Γ Γ' (subst0 s t :: s) (subst0 s' t' :: s') (Δ ,, vdef na t T) (Δ' ,, vdef na' t' T').

  Lemma psubst_length {Σ Γ Δ Γ' Δ' s s'} : psubst Σ Γ Δ s s' Γ' Δ' ->
                                           #|s| = #|Γ'| /\ #|s'| = #|Δ'| /\ #|s| = #|s'|.
  Proof.
    induction 1; simpl; intuition auto with arith.
  Qed.

  Lemma psubst_length' {Σ Γ Δ Γ' Δ' s s'} : psubst Σ Γ Δ s s' Γ' Δ' -> #|s'| = #|Γ'|.
  Proof.
    induction 1; simpl; auto with arith.
  Qed.

  Lemma psubst_nth_error Σ Γ Δ Γ' Δ' s s' n t :
    psubst Σ Γ Δ s s' Γ' Δ' ->
    nth_error s n = Some t ->
    ∑ decl decl' t',
      (nth_error Γ' n = Some decl) *
      (nth_error Δ' n = Some decl') *
      (nth_error s' n = Some t') *
    match decl_body decl, decl_body decl' with
    | Some d, Some d' =>
        let s2 := (skipn (S n) s) in
        let s2' := (skipn (S n) s') in
      let b := subst0 s2 d in
      let b' := subst0 s2' d' in
      psubst Σ Γ Δ s2 s2' (skipn (S n) Γ') (skipn (S n) Δ') *
      (t = b) * (t' = b') * pred1 Σ Γ Δ t t'
    | None, None => pred1 Σ Γ Δ t t'
    | _, _ => False
    end.
  Proof.
    induction 1 in n, t |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists (vass na T), (vass na' T'), t'. intuition auto.
    - intros.
      specialize (IHX _ _ H). intuition eauto.
    - intros [= <-]. exists (vdef na t0 T), (vdef na' t' T'), (subst0 s' t'). intuition auto.
      simpl. intuition simpl; auto.
    - apply IHX.
  Qed.

  Lemma psubst_nth_error' Σ Γ Δ Γ' Δ' s s' n t :
    psubst Σ Γ Δ s s' Γ' Δ' ->
    nth_error s n = Some t ->
    ∑ t',
      (nth_error s' n = Some t') *
      pred1 Σ Γ Δ t t'.
  Proof.
    induction 1 in n, t |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists t'; intuition auto.
    - intros.
      specialize (IHX _ _ H). intuition eauto.
    - intros [= <-]. exists (subst0 s' t'). intuition auto.
    - apply IHX.
  Qed.

  Lemma psubst_nth_error_None Σ Γ Δ Γ' Δ' s s' n :
    psubst Σ Γ Δ s s' Γ' Δ' ->
    nth_error s n = None ->
    (nth_error Γ' n = None) * (nth_error Δ' n = None)* (nth_error s' n = None).
  Proof.
    induction 1 in n |- *; simpl; auto; destruct n; simpl; intros; intuition try congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
  Qed.

  Lemma subst_skipn' n s k t : k < n -> (n - k) <= #|s| ->
    lift0 k (subst0 (skipn (n - k) s) t) = subst s k (lift0 n t).
  Proof.
    intros Hk Hn.
    assert (#|firstn (n - k) s| = n - k) by (rewrite firstn_length_le; lia).
    assert (k + (n - k) = n) by lia.
    assert (n - k + k = n) by lia.
    rewrite <- (firstn_skipn (n - k) s) at 2.
    rewrite subst_app_simpl. rewrite H H0.
    rewrite <- (commut_lift_subst_rec t _ n 0 0); try lia.
    generalize (subst0 (skipn (n - k) s) t). intros.
    erewrite <- (simpl_subst_rec _ (firstn (n - k) s) _ k); try lia.
    now rewrite H H1.
  Qed.

  Lemma split_app3 {A} (l l' l'' : list A) (l1 l1' l1'' : list A) :
    #|l| = #|l1| -> #|l'| = #|l1'| ->
        l ++ l' ++ l'' = l1 ++ l1' ++ l1'' ->
        l = l1 /\ l' = l1' /\ l'' = l1''.
  Proof.
    intros.
    eapply app_inj_length_l in H1 as [Hl Hr]; auto.
    eapply app_inj_length_l in Hr as [Hl' Hr]; auto.
  Qed.

  Lemma All2_local_env_subst_ctx :
    forall (Σ : global_env) c c0 (Γ0 Δ : context)
    (Γ'0 : list context_decl) (Γ1 Δ1 : context) (Γ'1 : list context_decl) (s s' : list term),
      psubst Σ Γ0 Γ1 s s' Δ Δ1 ->
      #|Γ'0| = #|Γ'1| ->
      #|Γ0| = #|Γ1| ->
      All2_local_env_over (pred1 Σ) Γ0 Γ1 Δ Δ1 ->
     All2_local_env
      (on_decl
       (on_decl_over
          (fun (Γ Γ' : context) (t t0 : term) =>
           forall (Γ2 Δ0 : context) (Γ'2 : list context_decl),
           Γ = Γ2 ,,, Δ0 ,,, Γ'2 ->
           forall (Γ3 Δ2 : context) (Γ'3 : list context_decl) (s0 s'0 : list term),
           psubst Σ Γ2 Γ3 s0 s'0 Δ0 Δ2 ->
           Γ' = Γ3 ,,, Δ2 ,,, Γ'3 ->
           #|Γ2| = #|Γ3| ->
           #|Γ'2| = #|Γ'3| ->
           All2_local_env_over (pred1 Σ) Γ2 Γ3 Δ0 Δ2 ->
           pred1 Σ (Γ2 ,,, subst_context s0 0 Γ'2) (Γ3 ,,, subst_context s'0 0 Γ'3) (subst s0 #|Γ'2| t)
             (subst s'0 #|Γ'3| t0)) (Γ0 ,,, Δ ,,, Γ'0) (Γ1 ,,, Δ1 ,,, Γ'1))) c c0 ->
  All2_local_env (on_decl (on_decl_over (pred1 Σ) (Γ0 ,,, subst_context s 0 Γ'0) (Γ1 ,,, subst_context s' 0 Γ'1)))
    (subst_context s #|Γ'0| c) (subst_context s' #|Γ'1| c0).
  Proof.
    intros.
    pose proof (All2_local_env_length X1).
    induction X1; simpl; rewrite ?subst_context_snoc; constructor; auto; rename_all_hyps.
    - red in p. red in p. rename_all_hyps.
      specialize (forall_Γ2 _ _ (Γ'0 ,,, Γ)
                 ltac:(now rewrite app_context_assoc) _ _ (Γ'1,,, Γ') _ _ X
                 ltac:(now rewrite app_context_assoc) heq_length0
                 ltac:(now rewrite !app_context_length; auto) X0).
      simpl in *.
      rewrite !subst_context_app !app_context_length !app_context_assoc !Nat.add_0_r in forall_Γ2.
      simpl. red.
      congruence.
    - destruct p. red in o, o0.
      specialize (o _ _ (Γ'0 ,,, Γ)
                 ltac:(now rewrite app_context_assoc) _ _ (Γ'1,,, Γ') _ _ X
                 ltac:(now rewrite app_context_assoc) heq_length0
                 ltac:(now rewrite !app_context_length; auto) X0).
      specialize (o0 _ _ (Γ'0 ,,, Γ)
                 ltac:(now rewrite app_context_assoc) _ _ (Γ'1,,, Γ') _ _ X
                 ltac:(now rewrite app_context_assoc) heq_length0
                 ltac:(now rewrite !app_context_length; auto) X0).
      simpl in *.
      unfold on_decl_over.
      rewrite !subst_context_app !app_context_length !app_context_assoc !Nat.add_0_r in o, o0.
      simpl in *. split; congruence.
  Qed.

  Lemma psubst_untyped_subslet :
    forall Σ Γ Δ s Γ' Δ' s',
      psubst Σ Γ Γ' s s' Δ Δ' ->
      untyped_subslet Γ s Δ.
  Proof.
    intros Σ Γ Δ s Γ' Δ' s' h.
    induction h.
    - constructor.
    - constructor. assumption.
    - constructor. assumption.
  Qed.

  (** Parallel reduction is substitutive. *)
  Lemma substitution_let_pred1 Σ Γ Δ Γ' Γ1 Δ1 Γ'1 s s' M N :
    wf Σ ->
    psubst Σ Γ Γ1 s s' Δ Δ1 ->
    #|Γ| = #|Γ1| ->
    #|Γ'| = #|Γ'1| ->
    All2_local_env_over (pred1 Σ) Γ Γ1 Δ Δ1 ->
    pred1 Σ (Γ ,,, Δ ,,, Γ') (Γ1 ,,, Δ1 ,,, Γ'1) M N ->
    pred1 Σ
      (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1)
      (subst s #|Γ'| M) (subst s' #|Γ'1| N).
  Proof.
    intros wfΣ Hs.
    remember (Γ ,,, Δ ,,, Γ') as Γl.
    remember (Γ1 ,,, Δ1 ,,, Γ'1) as Γr.
    intros Hlen Hlen' HΔ HΓ.
    revert HeqΓl Γ1 Δ1 Γ'1 s s' Hs HeqΓr Hlen Hlen' HΔ.
    revert Γ Δ Γ'.
    revert Γl Γr M N HΓ.
    set(P' :=
          fun (Γl Γr : context) =>
            forall (Γ Δ : context) (Γ' : list context_decl),
              Γl = Γ ,,, Δ ,,, Γ' ->
              forall (Γ1 : list context_decl) (Δ1 : context) (Γ'1 : list context_decl) (s s' : list term),
                psubst Σ Γ Γ1 s s' Δ Δ1 ->
                Γr = Γ1 ,,, Δ1 ,,, Γ'1 ->
                #|Γ| = #|Γ1| ->
               All2_local_env_over (pred1 Σ) Γ Γ1 Δ Δ1 ->
               pred1_ctx Σ (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1)).
    refine (pred1_ind_all_ctx Σ _ P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; !intros;
      try subst Γ Γ'; simplify_IH_hyps; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try specialize (forall_Γ _ _ _ eq_refl _ _ _
                               _ _ Hs eq_refl heq_length heq_length0 HΔ);
    try specialize (forall_Γ0 _ _ _ eq_refl _ _ _
                              _ _ Hs eq_refl heq_length heq_length0 HΔ);
    try specialize (forall_Γ1 _ _ _ eq_refl _ _ _
                           _ _ Hs eq_refl heq_length heq_length0 HΔ);
      try pose proof (All2_local_env_length X0);
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel, id in *.

    - (* Contexts *)
      red. intros. subst.
      pose proof (All2_local_env_length X1).
      rewrite !app_context_length in H |- *.
      assert (#|Γ'0| = #|Γ'1|) by lia.
      eapply All2_local_env_over_app.
      + eapply All2_local_env_app in predΓ'.
        * subst P'. intuition auto. typeclasses eauto with pcuic.
        * now rewrite !app_context_length.
      + eapply All2_local_env_app in X0 as [Xl Xr].
        2:{ rewrite !app_context_length. lia. }
        induction Xr; rewrite ?subst_context_snoc; constructor; pcuic.
        * apply IHXr.
          -- depelim predΓ'. all: hnf in H, H0. all: noconf H.
             noconf H0. auto.
          -- depelim predΓ'. all: hnf in H, H0. all: noconf H.
             noconf H0. auto.
          -- simpl in *. lia.
        * simpl in *.
          repeat red. rewrite !Nat.add_0_r. eapply p; eauto.
        * depelim predΓ'. all: hnf in H, H0. all: noconf H.
          noconf H0. auto. simpl in *.
          repeat red. apply IHXr. 2-3: lia.
          simpl in *. pcuic.
        * depelim predΓ'. all: hnf in H, H0. all: noconf H.
          noconf H0. auto. simpl in *. destruct p.
          split; repeat red.
          -- rewrite !Nat.add_0_r. simpl. eapply p; eauto.
          -- rewrite !Nat.add_0_r. simpl. eapply p0; eauto.

    - (* Beta *)
      specialize (forall_Γ _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                           _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite distr_subst. simpl.
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ1 _ _  (_ ,, _) eq_refl _ _ (_ ,, _)
                            _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      simpl. rewrite distr_subst.
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ1.

    - (* Rel *)
      pose proof (psubst_length Hs) as Hlens.
      elim (leb_spec_Set); intros Hn.
      + red in X0.
        specialize (X0 _ _ _ eq_refl _ _ _ _ _ Hs eq_refl heq_length HΔ).
        destruct (nth_error s) eqn:Heq.
        * (* Let-bound variable in the substitution *)
          pose proof (nth_error_Some_length Heq).
          pose proof predΓ' as X.
          eapply psubst_nth_error in Heq as [decl [decl' [t' ?]]]; eauto.
          intuition; rename_all_hyps.
          destruct decl as [? [?|] ?]; destruct decl' as [? [?|] ?]; simpl in b; try contradiction.
          -- intuition subst.
             revert heq_option_map.
             rewrite -> nth_error_app_context_ge by lia.
             pose proof (nth_error_Some_length heq_nth_error1).
             rewrite -> nth_error_app_context_lt by lia.
             rewrite - heq_length0 heq_nth_error1 => [= <-].
             eapply weakening_pred1_pred1 in b0.
             2:eauto. 2:eapply All2_local_env_app. 2:eapply X0. 2: lia.
             rewrite !subst_context_length in b0.
             rewrite <- subst_skipn'; try lia.
             now replace (S i - #|Γ'0|) with (S (i - #|Γ'0|)) by lia.
          -- revert heq_option_map.
             rewrite -> nth_error_app_context_ge by lia.
             pose proof (nth_error_Some_length heq_nth_error1).
             rewrite -> nth_error_app_context_lt by lia.
             rewrite - heq_length0 heq_nth_error1. simpl. congruence.
        * pose proof (psubst_length Hs).
          assert (#|Δ1| = #|s|).
          { eapply psubst_nth_error_None in Hs; eauto. lia. }
          eapply nth_error_None in Heq.
          subst P'.
          intuition; rename_all_hyps.
          (* Rel is a let-bound variable in Γ0, only weakening needed *)
          assert(eq:S i = #|s| + (S (i - #|s|))) by lia.
          rewrite eq.
          rewrite simpl_subst'; try lia.
          econstructor. 1: eauto.
          rewrite nth_error_app_context_ge !subst_context_length /=; try lia.
          rewrite <- heq_option_map. f_equal.
          rewrite nth_error_app_context_ge /=; try lia.
          rewrite nth_error_app_context_ge /=; try lia.
          f_equal. lia.
      + (* Local variable from Γ'0 *)
        assert(eq: #|Γ'1| = #|Γ'1| - S i + S i) by lia.
        rewrite eq.
        rewrite <- (commut_lift_subst_rec body s' (S i) (#|Γ'1| - S i) 0); try lia.
        econstructor. 1: eauto.
        rewrite nth_error_app_context_lt /= in heq_option_map.
        1: autorewrite with wf; lia.
        rewrite nth_error_app_context_lt; try (autorewrite with wf; lia).
        rewrite nth_error_subst_context.
        rewrite option_map_decl_body_map_decl heq_option_map.
        simpl. do 3 f_equal. lia.

    - specialize (X0 _ _ _ eq_refl _ _ _ _ _ Hs eq_refl heq_length HΔ).
      rewrite {1}heq_length0. elim (leb_spec_Set); intros Hn.
      + subst P'. intuition; subst; rename_all_hyps.
        pose proof (psubst_length Hs).
        destruct nth_error eqn:Heq.
        * eapply psubst_nth_error' in Heq as [t' [? ?]]; eauto.
          rewrite - heq_length0 e.
          rewrite - {1}(subst_context_length s 0 Γ'0).
          rewrite {1}heq_length0 -(subst_context_length s' 0 Γ'1).
          eapply weakening_pred1_pred1; auto.
          eapply All2_local_env_over_pred1_ctx.
          -- now rewrite !subst_context_length.
          -- auto.
        * eapply psubst_nth_error_None in Heq; eauto.
          intuition; rename_all_hyps.
          rewrite - heq_length0 heq_nth_error.
          eapply psubst_length' in Hs.
          assert(#|s| = #|s'|) as -> by lia.
          eauto with pcuic.
      + constructor. auto.

    - rewrite subst_iota_red.
      autorewrite with subst.
      econstructor.
      + eauto.
      + apply All2_map. solve_all.
      + unfold on_Trel. solve_all.

    - autorewrite with subst. simpl.
      unfold unfold_fix in heq_unfold_fix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_fix.
      destruct (isLambda (dbody d)) eqn:isl; noconf heq_unfold_fix.
      econstructor; auto with pcuic.
      + eapply X0; eauto with pcuic.
      + rewrite !subst_fix_context.
        erewrite subst_fix_context.
        eapply All2_local_env_subst_ctx; pcuic.
      + apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ0 _ _ (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 _ _ (Γ'1 ,,, fix_context mfix1) _ _ Hs
                            ltac:(now rewrite app_context_assoc) heq_length).
        rewrite !app_context_length in forall_Γ0.
        pose proof (All2_local_env_length X1).
        forward forall_Γ0 by lia.
        specialize (forall_Γ0 HΔ).
        rewrite !subst_fix_context.
        now rewrite !fix_context_length !subst_context_app
          !Nat.add_0_r !app_context_assoc in forall_Γ0.
      + unfold unfold_fix. rewrite nth_error_map. rewrite Hnth. simpl.
        rewrite isLambda_subst //.
        f_equal. f_equal.
        rewrite (map_fix_subst (fun k => subst s' (k + #|Γ'1|))).
        * intros. reflexivity.
        * simpl. now rewrite (distr_subst_rec _ _ _ _ 0) fix_subst_length.
      + apply subst_is_constructor; auto.
      + eapply All2_map. solve_all.

    - autorewrite with subst. simpl.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor; pcuic.
      + rewrite !subst_fix_context.
        erewrite subst_fix_context.
        eapply All2_local_env_subst_ctx; pcuic.
      + apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ1 _ _ (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ1 _ _ (Γ'1 ,,, fix_context mfix1) _ _ Hs
                            ltac:(now rewrite app_context_assoc) heq_length).
        rewrite !app_context_length in forall_Γ1.
        pose proof (All2_local_env_length X1).
        forward forall_Γ1 by lia.
        specialize (forall_Γ1 HΔ).
        rewrite !subst_fix_context.
        now rewrite !fix_context_length !subst_context_app
          !Nat.add_0_r !app_context_assoc in forall_Γ1.
      + unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
        f_equal. f_equal.
        rewrite (map_cofix_subst (fun k => subst s' (k + #|Γ'1|))).
        * intros. reflexivity.
        * simpl. now rewrite (distr_subst_rec _ _ _ _ 0) cofix_subst_length.
      + eapply All2_map. solve_all.
      + eapply All2_map. solve_all.

    - autorewrite with subst. simpl.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor.
      + red in X0. eauto 1 with pcuic. unshelve eapply X0.
        * shelve.
        * shelve.
        * eauto.
        * eauto.
        * eauto.
        * eauto.
        * eauto.
      + pcuic.
        rewrite !subst_fix_context.
        erewrite subst_fix_context.
        eapply All2_local_env_subst_ctx.
        * eapply Hs.
        * auto.
        * auto.
        * auto.
        * eapply X2.
      + apply All2_map. clear X2. red in X3.
        unfold on_Trel, id in *.
        solve_all. rename_all_hyps.
        specialize (forall_Γ0 _ _ (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
        specialize (forall_Γ0 _ _ (Γ'1 ,,, fix_context mfix1) _ _ Hs
                            ltac:(now rewrite app_context_assoc) heq_length).
        rewrite !app_context_length in forall_Γ0.
        pose proof (All2_local_env_length X1).
        forward forall_Γ0 by lia.
        specialize (forall_Γ0 HΔ).
        rewrite !subst_fix_context.
        now rewrite !fix_context_length !subst_context_app
          !Nat.add_0_r !app_context_assoc in forall_Γ0.
      + unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
        f_equal. f_equal.
        rewrite (map_cofix_subst (fun k => subst s' (k + #|Γ'1|))).
        * intros. reflexivity.
        * simpl. now rewrite (distr_subst_rec _ _ _ _ 0) cofix_subst_length.
      + eapply All2_map. solve_all.

    - (* Rewrite rules *)
      subst lhs rhs.
      apply psubst_length in Hs as es. destruct es as [? [? ?]].
      apply All2_length in X1 as es.
      rewrite 2!distr_subst. rewrite <- es.
      rewrite 2!distr_subst_rec.
      rewrite (PCUICClosed.subst_closedn _ _ (lhs r)).
      1:{
        eapply closed_upwards. 1: eapply PCUICClosed.closed_rule_lhs.
        all: eauto.
        subst ss. rewrite symbols_subst_length.
        apply untyped_subslet_length in H1.
        rewrite subst_context_length in H1.
        lia.
      }
      rewrite (PCUICClosed.subst_closedn _ _ (rhs r)).
      1:{
        eapply closed_upwards. 1: eapply PCUICClosed.closed_rule_rhs.
        all: eauto.
        subst ss. rewrite symbols_subst_length.
        apply untyped_subslet_length in H1.
        rewrite subst_context_length in H1.
        lia.
      }
      assert (e : forall s n, map (subst s n) ss = ss).
      { intros. subst ss. unfold symbols_subst.
        rewrite list_make_map. simpl. reflexivity.
      }
      rewrite 2!e.
      replace #|s| with #|map (subst s0 #|Γ'0|) s|
        by (now rewrite map_length).
      eapply pred_rewrite_rule.
      all: try eassumption.
      + eapply X0. all: eauto.
      + apply All2_map. eapply All2_impl. 1: eassumption.
        cbn. intros x y [? ih]. eapply ih. all: eauto.
      + eapply untyped_subslet_subst with (s' := s0) in H1 as h.
        2:{ eapply psubst_untyped_subslet. eassumption. }
        eapply PCUICClosed.closed_declared_symbol_pat_context in H as hcl.
        2-3: eassumption.
        rewrite -> (closed_ctx_subst _ #|Γ'0|) in h.
        1: exact h.
        eapply closedn_ctx_subst_context0.
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
      apply psubst_length in Hs as es. destruct es as [? [? ?]].
      apply All2_length in X1 as es.
      rewrite 2!distr_subst. rewrite <- es.
      rewrite 2!distr_subst_rec.
      rewrite (PCUICClosed.subst_closedn _ _ (lhs r)).
      1:{
        eapply closed_upwards. 1: eapply PCUICClosed.closed_prule_lhs.
        all: eauto.
        subst ss. rewrite symbols_subst_length.
        apply untyped_subslet_length in H1.
        rewrite subst_context_length in H1.
        lia.
      }
      rewrite (PCUICClosed.subst_closedn _ _ (rhs r)).
      1:{
        eapply closed_upwards. 1: eapply PCUICClosed.closed_prule_rhs.
        all: eauto.
        subst ss. rewrite symbols_subst_length.
        apply untyped_subslet_length in H1.
        rewrite subst_context_length in H1.
        lia.
      }
      assert (e : forall s n, map (subst s n) ss = ss).
      { intros. subst ss. unfold symbols_subst.
        rewrite list_make_map. simpl. reflexivity.
      }
      rewrite 2!e.
      replace #|s| with #|map (subst s0 #|Γ'0|) s|
        by (now rewrite map_length).
      eapply pred_par_rewrite_rule.
      all: try eassumption.
      + eapply X0. all: eauto.
      + apply All2_map. eapply All2_impl. 1: eassumption.
        cbn. intros x y [? ih]. eapply ih. all: eauto.
      + eapply untyped_subslet_subst with (s' := s0) in H1 as h.
        2:{ eapply psubst_untyped_subslet. eassumption. }
        eapply PCUICClosed.closed_declared_symbol_par_pat_context in H as hcl.
        2-3: eassumption.
        rewrite -> (closed_ctx_subst _ #|Γ'0|) in h.
        1: exact h.
        eapply closedn_ctx_subst_context0.
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

    - pose proof (subst_declared_constant _ _ _ s' #|Γ'0| u wfΣ H).
      apply (f_equal cst_body) in H0.
      rewrite <- !map_cst_body in H0. rewrite heq_cst_body in H0. simpl in H0.
      noconf H0. simpl in H0. rewrite heq_length0 in H0. rewrite H0.
      econstructor; eauto.

    - autorewrite with subst. simpl.
      econstructor; eauto.
      + eapply All2_map. solve_all.
      + now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                           _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite !subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                           _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite !subst_context_snoc0 in forall_Γ1.
      econstructor; eauto.

    - econstructor; eauto.
      { rewrite !subst_fix_context. eapply All2_local_env_subst_ctx; eauto. }
      apply All2_map. red in X0. unfold on_Trel, id in *.
      pose proof (All2_length _ _ X3).
      eapply All2_impl; eauto. simpl. intros.
      destruct X. destruct o, p. destruct p. rename_all_hyps.
      specialize (forall_Γ1 _ _ (_ ,,, fix_context mfix0) ltac:(now rewrite - app_context_assoc)
      _ _ (_ ,,, fix_context mfix1) _ _ Hs ltac:(now rewrite - app_context_assoc) heq_length).
      rewrite !app_context_length !fix_context_length in forall_Γ1. forward forall_Γ1 by lia.
      specialize (forall_Γ1 HΔ).
      specialize (forall_Γ0 _ _ _ eq_refl _ _ _
                            _ _ Hs eq_refl heq_length heq_length0 HΔ).
      rewrite subst_context_app Nat.add_0_r ?app_context_length ?fix_context_length
              ?app_context_assoc in forall_Γ1. auto.
      split; eauto.
      rewrite !subst_fix_context. split; eauto.
      rewrite subst_context_app Nat.add_0_r
              app_context_assoc in forall_Γ1. auto.

    - econstructor; eauto.
      { rewrite !subst_fix_context. eapply All2_local_env_subst_ctx; eauto. }
      apply All2_map. red in X0. unfold on_Trel, id in *.
      pose proof (All2_length _ _ X3).
      eapply All2_impl; eauto. simpl. intros.
      destruct X. destruct o, p. destruct p. rename_all_hyps.
      specialize (forall_Γ1 _ _ (_ ,,, fix_context mfix0) ltac:(now rewrite - app_context_assoc)
      _ _ (_ ,,, fix_context mfix1) _ _ Hs ltac:(now rewrite - app_context_assoc) heq_length).
      rewrite !app_context_length !fix_context_length in forall_Γ1. forward forall_Γ1 by lia.
      specialize (forall_Γ1 HΔ).
      specialize (forall_Γ0 _ _ _ eq_refl _ _ _
                            _ _ Hs eq_refl heq_length heq_length0 HΔ).
      rewrite subst_context_app Nat.add_0_r ?app_context_length ?fix_context_length
              ?app_context_assoc in forall_Γ1. auto.
      split; eauto.
      rewrite !subst_fix_context. split; eauto.
      rewrite subst_context_app Nat.add_0_r
              app_context_assoc in forall_Γ1. auto.

    - specialize (forall_Γ0 _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                              _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite !subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Hint Constructors psubst : pcuic.
  Hint Transparent vass vdef : pcuic.

  Lemma substitution0_pred1 {Σ : global_env} {Γ Δ M M' na na' A A' N N'} :
    wf Σ ->
    pred1 Σ Γ Δ M M' ->
    pred1 Σ (Γ ,, vass na A) (Δ ,, vass na' A') N N' ->
    pred1 Σ Γ Δ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redM redN.
    pose proof (substitution_let_pred1 Σ Γ [vass na A] [] Δ [vass na' A'] [] [M] [M'] N N' wfΣ) as H.
    forward H.
    - constructor; auto with pcuic.
      forward H by pcuic.
      + constructor; pcuic. apply pred1_pred1_ctx in redN.
        depelim redN. all: hnf in H, H0. all: noconf H.
        noconf H0. pcuic.
      + simpl in H |- *. apply pred1_pred1_ctx in redN; pcuic.
        depelim redN. all: hnf in H, H0. all: noconf H.
        noconf H0. pcuic.
    - pose proof (pred1_pred1_ctx _ redN). depelim X.
      all: hnf in H0, H1. all: noconf H0.
      noconf H1.
      apply H; pcuic. auto. constructor; pcuic.
  Qed.

  Lemma substitution0_let_pred1 {Σ Γ Δ na na' M M' A A' N N'} : wf Σ ->
    pred1 Σ Γ Δ M M' ->
    pred1 Σ (Γ ,, vdef na M A) (Δ ,, vdef na' M' A') N N' ->
    pred1 Σ Γ Δ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redM redN.
    pose proof (substitution_let_pred1 Σ Γ [vdef na M A] [] Δ [vdef na' M' A'] [] [M] [M'] N N' wfΣ) as H.
    pose proof (pred1_pred1_ctx _ redN). depelim X.
    all: hnf in H0, H1. all: noconf H0.
    noconf H1.
    simpl in o.
    forward H.
    - pose proof (psubst_vdef Σ Γ Δ [] [] [] [] na na' M M' A A').
      rewrite !subst_empty in X0. apply X0; pcuic.
    - apply H; pcuic.
      econstructor; auto with pcuic.
  Qed.

  (* TODO Find a more suitable place for these *)
  Fixpoint isElimSymb (t : term) :=
    match t with
    | tSymb k n u => true
    | tApp u v => isElimSymb u
    | tCase ind p c brs => isElimSymb c
    | tProj p u => isElimSymb u
    | _ => false
    end.

  Lemma isElimSymb_mkElims :
    forall t l,
      isElimSymb (mkElims t l) = isElimSymb t.
  Proof.
    intros t l.
    induction l in t |- * using list_ind_rev. 1: reflexivity.
    unfold mkElims. rewrite fold_left_app. cbn.
    destruct a. all: cbn. all: apply IHl.
  Qed.

  Lemma isElimSymb_mkApps :
    forall t l,
      isElimSymb (mkApps t l) = isElimSymb t.
  Proof.
    intros t l.
    induction l in t |- * using list_ind_rev. 1: reflexivity.
    rewrite <- mkApps_nested. cbn. apply IHl.
  Qed.

  Lemma isElimSymb_subst :
    forall t s k,
      isElimSymb t ->
      isElimSymb (subst s k t).
  Proof.
    intros t s k h.
    induction t. all: try discriminate.
    - cbn in *. eapply IHt1. assumption.
    - cbn. reflexivity.
    - cbn in *. eapply IHt2. assumption.
    - cbn in *. eapply IHt. assumption.
  Qed.

  Definition subst_elim s k e :=
    match e with
    | eApp u => eApp (subst s k u)
    | eProj p => eProj p
    | eCase ind p brs => eCase ind (subst s k p) (map (on_snd (subst s k)) brs)
    end.

  Lemma mkElim_subst :
    forall s k t e,
      subst s k (mkElim t e) = mkElim (subst s k t) (subst_elim s k e).
  Proof.
    intros s k t e. destruct e.
    - cbn. reflexivity.
    - cbn. reflexivity.
    - cbn. reflexivity.
  Qed.

  Lemma mkElims_subst :
    forall s k t l,
      subst s k (mkElims t l) = mkElims (subst s k t) (map (subst_elim s k) l).
  Proof.
    intros s k t l. induction l in s, k, t |- * using list_ind_rev.
    - cbn. reflexivity.
    - unfold mkElims. rewrite fold_left_app. cbn.
      rewrite map_app. rewrite fold_left_app. cbn.
      rewrite mkElim_subst. f_equal. apply IHl.
  Qed.

  Lemma isElimSymb_lift :
    forall n k t,
      isElimSymb t ->
      isElimSymb (lift n k t).
  Proof.
    intros n k t h.
    induction t. all: try discriminate.
    all: cbn. all: eauto.
  Qed.

  Lemma isElimSymb_lhs :
    forall kn n ui r,
      n > r.(head) ->
      let ss := symbols_subst kn 0 ui n in
      isElimSymb (subst ss #|r.(pat_context)| (PCUICAst.lhs r)).
  Proof.
    intros kn n ui r h. unfold PCUICAst.lhs.
    rewrite mkElims_subst.
    rewrite isElimSymb_mkElims. cbn.
    destruct (Nat.leb_spec #|pat_context r| (#|pat_context r| + head r)).
    2: lia.
    replace (#|pat_context r| + head r - #|pat_context r|)
    with (head r) by lia.
    destruct nth_error eqn:e.
    - apply isElimSymb_lift.
      unfold symbols_subst in e. revert e.
      replace (n - 0) with n by lia.
      generalize 0. generalize (head r). clear.
      intros m k e. induction n in m, k, t, e |- *.
      + cbn in e. destruct m. all: discriminate.
      + destruct m.
        * cbn in e. apply some_inj in e. subst. reflexivity.
        * cbn in e. eapply IHn. eassumption.
    - apply nth_error_None in e. rewrite symbols_subst_length in e.
      lia.
  Qed.

  Lemma isElimSymb_pre_lhs :
    forall kn n ui r m,
      n > r.(head) ->
      let ss := symbols_subst kn 0 ui n in
      let prelhs :=
        mkElims (tRel (#|r.(pat_context)| + r.(head))) (firstn m r.(elims))
      in
      isElimSymb (subst ss #|r.(pat_context)| prelhs).
  Proof.
    intros kn n ui r m h. cbn.
    rewrite mkElims_subst.
    rewrite isElimSymb_mkElims. cbn.
    destruct (Nat.leb_spec #|pat_context r| (#|pat_context r| + head r)).
    2: lia.
    replace (#|pat_context r| + head r - #|pat_context r|)
    with (head r) by lia.
    destruct nth_error eqn:e.
    - apply isElimSymb_lift.
      unfold symbols_subst in e. revert e.
      replace (n - 0) with n by lia.
      generalize 0. generalize (head r). clear.
      intros m k e. induction n in m, k, t, e |- *.
      + cbn in e. destruct m. all: discriminate.
      + destruct m.
        * cbn in e. apply some_inj in e. subst. reflexivity.
        * cbn in e. eapply IHn. eassumption.
    - apply nth_error_None in e. rewrite symbols_subst_length in e.
      lia.
  Qed.

  Lemma declared_symbol_head `{checker_flags} :
    forall Σ k n decl r,
      wf Σ ->
      declared_symbol Σ k decl ->
      nth_error decl.(rules) n = Some r ->
      r.(head) < #|decl.(symbols)|.
  Proof.
    intros Σ k n decl r hΣ h e.
    unfold declared_symbol in h.
    eapply lookup_on_global_env in h. 2: eauto.
    destruct h as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    destruct decl' as [hctx [hr [hpr hprr]]].
    eapply All_nth_error in hr. 2: eassumption.
    destruct hr as [T hl hr hh he].
    rewrite map_length in hh. assumption.
  Qed.

  Lemma declared_symbol_par_head `{checker_flags} :
    forall Σ k n decl r,
      wf Σ ->
      declared_symbol Σ k decl ->
      nth_error decl.(prules) n = Some r ->
      r.(head) < #|decl.(symbols)|.
  Proof.
    intros Σ k n decl r hΣ h e.
    unfold declared_symbol in h.
    eapply lookup_on_global_env in h. 2: eauto.
    destruct h as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    destruct decl' as [hctx [hr [hpr hprr]]].
    eapply All_nth_error in hpr. 2: eassumption.
    destruct hpr as [T hl hpr hh he].
    rewrite map_length in hh. assumption.
  Qed.

  Definition is_rewrite_rule Σ k decl r :=
    declared_symbol Σ k decl ×
    ((∑ n, nth_error decl.(rules) n = Some r) +
     (∑ n, nth_error decl.(prules) n = Some r)).

  Lemma is_rewrite_rule_head :
    forall Σ k decl r,
      wf Σ ->
      is_rewrite_rule Σ k decl r ->
      r.(head) < #|decl.(symbols)|.
  Proof.
    intros Σ k decl r hΣ hr.
    destruct hr as [h [[n e]|[n e]]].
    - eapply declared_symbol_head. all: eassumption.
    - eapply declared_symbol_par_head. all: eassumption.
  Qed.

  Lemma mkElims_app :
    forall t l1 l2,
      mkElims t (l1 ++ l2) = mkElims (mkElims t l1) l2.
  Proof.
    intros t l1 l2.
    unfold mkElims. apply fold_left_app.
  Qed.

  (* TODO MOVE *)
  Lemma list_make_nth_error :
    forall A f i n m x,
      nth_error (@list_make A f i n) m = Some x ->
      x = f (m + i).
  Proof.
    intros A f i n m x e.
    induction n in i, m, x, e |- *.
    - cbn in e. destruct m. all: discriminate.
    - cbn in e. destruct m.
      + cbn in e. apply some_inj in e. subst. reflexivity.
      + cbn in e. cbn. apply IHn in e. subst. f_equal. lia.
  Qed.

  Lemma symbols_subst_nth_error :
    forall k n ui m t i,
      nth_error (symbols_subst k n ui m) i = Some t ->
      t = tSymb k (i + n) ui.
  Proof.
    intros k n ui m t i e. unfold symbols_subst in e.
    apply list_make_nth_error in e. assumption.
  Qed.

  Fixpoint getSymb (t : term) :=
    match t with
    | tSymb k n ui => Some (k, n, ui)
    | tApp u v => getSymb u
    | tProj p u => getSymb u
    | tCase ind p c brs => getSymb c
    | _ => None
    end.

  Lemma getSymb_mkElim :
    forall t e,
      getSymb (mkElim t e) = getSymb t.
  Proof.
    intros t []. all: simpl. all: reflexivity.
  Qed.

  Lemma getSymb_mkElims :
    forall t l,
      getSymb (mkElims t l) = getSymb t.
  Proof.
    intros t l. induction l in t |- * using list_ind_rev.
    - cbn. reflexivity.
    - rewrite mkElims_app. cbn. rewrite getSymb_mkElim.
      apply IHl.
  Qed.

  Inductive pred1_elim Σ Γ Δ : elimination -> elimination -> Type :=
  | pred1_eApp :
      forall u u',
        pred1 Σ Γ Δ u u' ->
        pred1_elim Σ Γ Δ (eApp u) (eApp u')

  | pred1_eCase :
      forall ind p brs p' brs',
        pred1 Σ Γ Δ p p' ->
        All2 (on_Trel_eq (pred1 Σ Γ Δ) snd fst) brs brs' ->
        pred1_elim Σ Γ Δ (eCase ind p brs) (eCase ind p' brs')

  | pred1_eProj :
      forall p,
        (* pred1_ctx Σ Γ Δ -> *)
        pred1_elim Σ Γ Δ (eProj p) (eProj p).

  Lemma pred1_mkElim :
    forall Σ Γ Δ t t' e e',
      pred1 Σ Γ Δ t t' ->
      pred1_elim Σ Γ Δ e e' ->
      pred1 Σ Γ Δ (mkElim t e) (mkElim t' e').
  Proof.
    intros Σ Γ Δ t t' e e' ht he.
    destruct he.
    - cbn. constructor. all: assumption.
    - cbn. constructor. all: assumption.
    - cbn. constructor. all: assumption.
  Qed.

  Lemma pred1_mkElims :
    forall Σ Γ Δ t t' e e',
        pred1 Σ Γ Δ t t' ->
        All2 (pred1_elim Σ Γ Δ) e e' ->
        pred1 Σ Γ Δ (mkElims t e) (mkElims t' e').
  Proof.
    intros Σ Γ Δ t t' e e' ht he.
    apply All2_rev in he.
    rewrite <- (rev_involutive e).
    rewrite <- (rev_involutive e').
    revert he. generalize (List.rev e) (List.rev e'). clear e e'.
    intros e e' he. induction he in t, t', ht |- *.
    - assumption.
    - simpl. rewrite 2!mkElims_app. cbn.
      apply pred1_mkElim. 2: assumption.
      apply IHhe. assumption.
  Qed.

  Lemma skipn_app :
    forall A (l1 l2 : list A) n,
      skipn n (l1 ++ l2) = skipn n l1 ++ skipn (n - #|l1|) l2.
  Proof.
    intros A l1 l2 n.
    destruct (Nat.leb_spec #|l1| n) as [h|h].
    - rewrite -> (skipn_all2 l1) by auto. cbn.
      replace n with (#|l1| + (n - #|l1|)) at 1 by lia.
      rewrite skipn_skipn. rewrite skipn_all_app. reflexivity.
    - replace (n - #|l1|) with 0 by lia.
      change (skipn 0 l2) with l2.
      induction n in l1, l2, h |- *.
      + unfold skipn. reflexivity.
      + destruct l1. 1: cbn in * ; lia.
        cbn in h. cbn. rewrite 2!skipn_S.
        apply IHn. lia.
  Qed.

  Lemma pred1_elim_refl_gen :
    forall Σ Γ Δ e,
      pred1_ctx Σ Γ Δ ->
      pred1_elim Σ Γ Δ e e.
  Proof.
    intros Σ Γ Δ [] h.
    - constructor. apply pred1_refl_gen. assumption.
    - constructor.
      + apply pred1_refl_gen. assumption.
      + apply All2_same. intros [? ?]. cbn. intuition auto.
        apply pred1_refl_gen. assumption.
    - constructor.
  Qed.

  (* TODO Have a lemma lhs_prefix_reducts
    which is basically the same but conclude on any prefix (firstn on elims)
    of a lhs. Maybe a lemma besides to conclude about the reducts of a pattern
    (namely that there are none besides the pattern itself).

    We want to say that either
    - nothing happend
    - a prefix of (the prefix of) the lhs matches another lhs and for that
      we use a pattern substitution (All pattern s) to factorise the original
      substitution so we can talk about reducing the terms outside the prefix
    - the rule itself applied

    Or more probably
    - a rewrite rule applied (of the system, possibly the same)
    - only congruence applied so the substitution reduced (possibly with
      reflexivity)

    In both cases we need linearity of pattern variables.

    We want to say subst_elim s e reducing means some filter of s reduces to
    s' and the whole to subst_elim s' e.
    Then linearity should allow us to combine the separate infos.
    We will want to prove the earlier goal:
    (∑ s', All2 (pred1 Σ Γ Δ) s s' × t = subst0 s' (subst ss #|s| prelhs0)).
  *)
  Lemma lhs_prefix_reducts :
    forall Σ k ui decl r Γ Δ s t n,
      wf Σ ->
      is_rewrite_rule Σ k decl r ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let prelhs0 :=
        mkElims (tRel (#|r.(pat_context)| + r.(head))) (firstn n r.(elims))
      in
      let prelhs := subst0 s (subst ss #|s| prelhs0) in
      pred1 Σ Γ Δ prelhs t ->
      (∑ r' θ θ' m el,
        is_rewrite_rule Σ k decl r' ×
        untyped_subslet Γ θ (subst_context ss 0 r'.(pat_context)) ×
        r.(head) = r'.(head) ×
        m <= n ×
        All2 (pred1 Σ Γ Δ) θ θ' ×
        let prelhs1 :=
          mkElims
            (tRel (#|r.(pat_context)| + r.(head)))
            (firstn m r.(elims))
        in
        let prelhs2 := subst0 s (subst ss #|s| prelhs1) in
        prelhs2 = subst0 θ (subst ss #|θ| (lhs r')) ×
        All2
          (pred1_elim Σ Γ Δ)
          (skipn
            m
            (firstn
              n
              (map (subst_elim s 0) (map (subst_elim ss #|s|) r.(elims)))))
           el ×
        t = mkElims (subst0 θ' (subst ss #|θ| r'.(rhs))) el
      ) +
      (∑ el,
        All2
          (pred1_elim Σ Γ Δ)
          (map
            (subst_elim s 0)
            (map (subst_elim ss #|s|) (firstn n r.(elims)))
          )
          el ×
        t = mkElims (subst ss #|s| (tRel (#|r.(pat_context)| + r.(head)))) el
      ).
  Proof.
    intros Σ k ui decl r Γ Δ s t n hΣ hr ss hs prelhs0 prelhs h.
    assert (e0 :
      prelhs0 =
      mkElims (tRel (#|r.(pat_context)| + r.(head))) (firstn n r.(elims))
    ) by reflexivity. clearbody prelhs0.
    assert (e : prelhs = subst0 s (subst ss #|s| prelhs0)) by reflexivity.
    clearbody prelhs.
    induction h in r, hr, s, hs, prelhs0, e0, e, n |- *.
    all: try solve [
      exfalso ; rewrite ?e0 in e ;
      apply (f_equal isElimSymb) in e ; cbn in e ;
      rewrite ?isElimSymb_mkApps in e ; cbn in e ;
      eapply diff_false_true ; rewrite e ;
      eapply isElimSymb_subst ; apply untyped_subslet_length in hs ;
      rewrite subst_context_length in hs ; rewrite hs ;
      eapply isElimSymb_pre_lhs ;
      eapply is_rewrite_rule_head in hr ; eauto
    ].
    - right. eexists. split.
      + apply All2_same. intro. apply pred1_elim_refl_gen. assumption.
      + rewrite e0 in e. rewrite 2!mkElims_subst in e.
        rewrite e. f_equal. cbn.
        destruct (Nat.leb_spec #|s| (#|r.(pat_context)| + r.(head))).
        2:{
          apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs. lia.
        }
        destruct nth_error eqn:er.
        2:{
          apply nth_error_None in er. subst ss.
          rewrite symbols_subst_length in er.
          apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs.
          apply is_rewrite_rule_head in hr. 2: auto.
          lia.
        }
        apply symbols_subst_nth_error in er as ?. subst.
        cbn. reflexivity.
    - (* Rewrite rule *)
      left.
      assert (k0 = k /\ ui0 = ui /\ r.(head) = r0.(head)) as [? [? ehead]].
      { subst. subst lhs. unfold lhs in e.
        rewrite -> 4!mkElims_subst in e.
        cbn in e.
        apply untyped_subslet_length in hs.
        apply untyped_subslet_length in u.
        rewrite subst_context_length in hs.
        rewrite subst_context_length in u.
        destruct (Nat.leb_spec #|s0| (#|pat_context r0| + head r0)). 2: lia.
        destruct (Nat.leb_spec #|s| (#|pat_context r| + head r)). 2: lia.
        eapply is_rewrite_rule_head in hr. 2: auto.
        eapply declared_symbol_head in e1. all: eauto.
        destruct nth_error eqn:e2.
        2:{
          eapply nth_error_None in e2. subst ss0.
          rewrite symbols_subst_length in e2. lia.
        }
        destruct (nth_error ss) eqn:e3.
        2:{
          eapply nth_error_None in e3. subst ss.
          rewrite symbols_subst_length in e3. lia.
        }
        apply symbols_subst_nth_error in e2.
        apply symbols_subst_nth_error in e3. subst.
        cbn in e.
        apply (f_equal getSymb) in e.
        rewrite 2!getSymb_mkElims in e. cbn in e.
        inversion e.
        intuition auto. lia.
      } subst.
      assert (decl0 = decl).
      { unfold declared_symbol in d.
        destruct hr as [hd _]. unfold declared_symbol in hd.
        rewrite d in hd. inversion hd. reflexivity.
      } subst.
      change ss0 with ss in *. clear ss0.
      exists r0, s0, s', n, []. cbn.
      repeat match goal with
      | |- _ × _ => split
      end. all: auto.
      + split. 1: assumption.
        left. eexists. eassumption.
      + rewrite skipn_all2. 2: constructor.
        apply firstn_le_length.
    - (* Parallel rewrite rule *)
      left.
      assert (k0 = k /\ ui0 = ui /\ r.(head) = r0.(head)) as [? [? ehead]].
      { subst. subst lhs. unfold lhs in e.
        rewrite -> 4!mkElims_subst in e.
        cbn in e.
        apply untyped_subslet_length in hs.
        apply untyped_subslet_length in u.
        rewrite subst_context_length in hs.
        rewrite subst_context_length in u.
        destruct (Nat.leb_spec #|s0| (#|pat_context r0| + head r0)). 2: lia.
        destruct (Nat.leb_spec #|s| (#|pat_context r| + head r)). 2: lia.
        eapply is_rewrite_rule_head in hr. 2: auto.
        eapply declared_symbol_par_head in e1. all: eauto.
        destruct nth_error eqn:e2.
        2:{
          eapply nth_error_None in e2. subst ss0.
          rewrite symbols_subst_length in e2. lia.
        }
        destruct (nth_error ss) eqn:e3.
        2:{
          eapply nth_error_None in e3. subst ss.
          rewrite symbols_subst_length in e3. lia.
        }
        apply symbols_subst_nth_error in e2.
        apply symbols_subst_nth_error in e3. subst.
        cbn in e.
        apply (f_equal getSymb) in e.
        rewrite 2!getSymb_mkElims in e. cbn in e.
        inversion e.
        intuition auto. lia.
      } subst.
      assert (decl0 = decl).
      { unfold declared_symbol in d.
        destruct hr as [hd _]. unfold declared_symbol in hd.
        rewrite d in hd. inversion hd. reflexivity.
      } subst.
      change ss0 with ss in *. clear ss0.
      exists r0, s0, s', n, []. cbn.
      repeat match goal with
      | |- _ × _ => split
      end. all: auto.
      + split. 1: assumption.
        right. eexists. eassumption.
      + rewrite skipn_all2. 2: constructor.
        apply firstn_le_length.
    - (* Application *)
      rewrite e0 in e.
      destruct (firstn n r.(elims)) eqn:ee using list_rect_rev.
      1:{
        exfalso.
        simpl in e.
        destruct (Nat.leb_spec #|s| (#|pat_context r| + head r)).
        2:{
          apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs. lia.
        }
        destruct nth_error eqn:en.
        - revert en e. generalize (#|pat_context r| + head r - #|s|). clear.
          subst ss. unfold symbols_subst. generalize (#|symbols decl| - 0).
          generalize 0. clear.
          intros i n m en e.
          assert (∑ i, t = tSymb k i ui) as [j et].
          { induction n in i, m, en |- *.
            - cbn in en. destruct m. all: discriminate.
            - cbn in en. destruct m.
              + cbn in en. apply some_inj in en. subst.
                eexists. reflexivity.
              + cbn in en. eapply IHn. eassumption.
          }
          subst. cbn in e. discriminate.
        - apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs.
          apply nth_error_None in en. subst ss.
          rewrite symbols_subst_length in en.
          apply is_rewrite_rule_head in hr. 2: eassumption.
          lia.
      }
      rewrite mkElims_app in e. cbn in e.
      destruct a. all: try discriminate.
      cbn in e. inversion e. subst. clear e.
      clear IHl IHh2.
      specialize (IHh1 _ _ #|l| hr hs _ eq_refl).
      forward IHh1.
      { f_equal. f_equal. f_equal. clear - ee.
        apply (f_equal (firstn #|l|)) in ee as e.
        rewrite firstn_app in e. replace (#|l| - #|l|) with 0 in e by lia.
        cbn in e. rewrite app_nil_r in e.
        rewrite firstn_all in e.
        apply (f_equal (@List.length _)) in ee as h.
        rewrite app_length in h. cbn in h.
        pose proof (firstn_le_length n r.(elims)) as h'.
        rewrite h in h'.
        rewrite firstn_firstn in e.
        replace (Init.Nat.min #|l| n) with #|l| in e by lia.
        auto.
      }
      destruct IHh1 as [
        [r' [θ [θ' [m [el [hr' [uθ [ehr [hm [hθ [epre [hrest h]]]]]]]]]]]]
      | [el [hel h]]
      ].
      + left. subst.
        eexists r', θ, θ', m, (el ++ [ eApp N1 ]). cbn.
        repeat match goal with
        | |- _ × _ => split
        end. all: auto.
        * apply (f_equal (@List.length _)) in ee as h.
          rewrite app_length in h. cbn in h.
          pose proof (firstn_le_length n r.(elims)) as h'.
          rewrite h in h'. lia.
        * rewrite 2!firstn_map. rewrite ee.
          rewrite <- 2!map_skipn. rewrite skipn_app.
          replace (m - #|l|) with 0 by lia.
          unfold skipn at 2.
          rewrite 2!map_app. cbn.
          eapply All2_app.
          -- rewrite 2!firstn_map in hrest.
             replace (firstn #|l| r.(elims))
             with l in hrest.
             2:{
              apply (f_equal (@List.length _)) in ee as h.
              rewrite app_length in h. cbn in h.
              pose proof (firstn_le_length n r.(elims)) as h'.
              rewrite h in h'.
              replace #|l| with (Init.Nat.min #|l| n) by lia.
              rewrite <- firstn_firstn. rewrite ee.
              replace #|l| with (#|l| + 0) by lia.
              rewrite firstn_app_2.
              cbn. rewrite app_nil_r. reflexivity.
             }
             rewrite 2!map_skipn. assumption.
          -- constructor. 2: constructor.
             constructor. assumption.
        * rewrite mkElims_app. cbn. reflexivity.
      + right. subst. eexists (el ++ [ eApp N1 ]). split.
        * rewrite 2!map_app. cbn. eapply All2_app.
          2:{ constructor. 2: constructor. constructor. assumption. }
          replace (firstn #|l| r.(elims))
          with l in hel.
          2:{
            apply (f_equal (@List.length _)) in ee as h.
            rewrite app_length in h. cbn in h.
            pose proof (firstn_le_length n r.(elims)) as h'.
            rewrite h in h'.
            replace #|l| with (Init.Nat.min #|l| n) by lia.
            rewrite <- firstn_firstn. rewrite ee.
            replace #|l| with (#|l| + 0) by lia.
            rewrite firstn_app_2.
            cbn. rewrite app_nil_r. reflexivity.
          }
          assumption.
        * rewrite mkElims_app. cbn. reflexivity.
    - (* Case *)
      rewrite e0 in e.
      destruct (firstn n r.(elims)) eqn:ee using list_rect_rev.
      1:{
        exfalso.
        simpl in e.
        destruct (Nat.leb_spec #|s| (#|pat_context r| + head r)).
        2:{
          apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs. lia.
        }
        destruct nth_error eqn:en.
        - revert en e. generalize (#|pat_context r| + head r - #|s|). clear.
          subst ss. unfold symbols_subst. generalize (#|symbols decl| - 0).
          generalize 0. clear.
          intros i n m en e.
          assert (∑ i, t = tSymb k i ui) as [j et].
          { induction n in i, m, en |- *.
            - cbn in en. destruct m. all: discriminate.
            - cbn in en. destruct m.
              + cbn in en. apply some_inj in en. subst.
                eexists. reflexivity.
              + cbn in en. eapply IHn. eassumption.
          }
          subst. cbn in e. discriminate.
        - apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs.
          apply nth_error_None in en. subst ss.
          rewrite symbols_subst_length in en.
          apply is_rewrite_rule_head in hr. 2: eassumption.
          lia.
      }
      rewrite mkElims_app in e. cbn in e.
      destruct a0. all: try discriminate.
      cbn in e. inversion e. subst. clear e.
      clear IHl IHh1.
      specialize (IHh2 _ _ #|l| hr hs _ eq_refl).
      forward IHh2.
      { f_equal. f_equal. f_equal. clear - ee.
        apply (f_equal (firstn #|l|)) in ee as e.
        rewrite firstn_app in e. replace (#|l| - #|l|) with 0 in e by lia.
        cbn in e. rewrite app_nil_r in e.
        rewrite firstn_all in e.
        apply (f_equal (@List.length _)) in ee as h.
        rewrite app_length in h. cbn in h.
        pose proof (firstn_le_length n r.(elims)) as h'.
        rewrite h in h'.
        rewrite firstn_firstn in e.
        replace (Init.Nat.min #|l| n) with #|l| in e by lia.
        auto.
      }
      destruct IHh2 as [
        [r' [θ [θ' [m [el [hr' [uθ [ehr [hm [hθ [epre [hrest h]]]]]]]]]]]]
      | [el [hel h]]
      ].
      + left. subst.
        eexists r', θ, θ', m, (el ++ [ eCase indn p1 brs1 ]). cbn.
        repeat match goal with
        | |- _ × _ => split
        end. all: auto.
        * apply (f_equal (@List.length _)) in ee as h.
          rewrite app_length in h. cbn in h.
          pose proof (firstn_le_length n r.(elims)) as h'.
          rewrite h in h'. lia.
        * rewrite 2!firstn_map. rewrite ee.
          rewrite <- 2!map_skipn. rewrite skipn_app.
          replace (m - #|l|) with 0 by lia.
          unfold skipn at 2.
          rewrite 2!map_app. cbn.
          eapply All2_app.
          -- rewrite 2!firstn_map in hrest.
             replace (firstn #|l| r.(elims))
             with l in hrest.
             2:{
              apply (f_equal (@List.length _)) in ee as h.
              rewrite app_length in h. cbn in h.
              pose proof (firstn_le_length n r.(elims)) as h'.
              rewrite h in h'.
              replace #|l| with (Init.Nat.min #|l| n) by lia.
              rewrite <- firstn_firstn. rewrite ee.
              replace #|l| with (#|l| + 0) by lia.
              rewrite firstn_app_2.
              cbn. rewrite app_nil_r. reflexivity.
             }
             rewrite 2!map_skipn. assumption.
          -- constructor. 2: constructor.
             constructor. all: assumption.
        * rewrite mkElims_app. cbn. reflexivity.
      + right. subst. eexists (el ++ [ eCase indn p1 brs1 ]). split.
        * rewrite 2!map_app. cbn. eapply All2_app.
          2:{ constructor. 2: constructor. constructor. all: assumption. }
          replace (firstn #|l| r.(elims))
          with l in hel.
          2:{
            apply (f_equal (@List.length _)) in ee as h.
            rewrite app_length in h. cbn in h.
            pose proof (firstn_le_length n r.(elims)) as h'.
            rewrite h in h'.
            replace #|l| with (Init.Nat.min #|l| n) by lia.
            rewrite <- firstn_firstn. rewrite ee.
            replace #|l| with (#|l| + 0) by lia.
            rewrite firstn_app_2.
            cbn. rewrite app_nil_r. reflexivity.
          }
          assumption.
        * rewrite mkElims_app. cbn. reflexivity.
    - (* Proj *)
      rewrite e0 in e.
      destruct (firstn n r.(elims)) eqn:ee using list_rect_rev.
      1:{
        exfalso.
        simpl in e.
        destruct (Nat.leb_spec #|s| (#|pat_context r| + head r)).
        2:{
          apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs. lia.
        }
        destruct nth_error eqn:en.
        - revert en e. generalize (#|pat_context r| + head r - #|s|). clear.
          subst ss. unfold symbols_subst. generalize (#|symbols decl| - 0).
          generalize 0. clear.
          intros i n m en e.
          assert (∑ i, t = tSymb k i ui) as [j et].
          { induction n in i, m, en |- *.
            - cbn in en. destruct m. all: discriminate.
            - cbn in en. destruct m.
              + cbn in en. apply some_inj in en. subst.
                eexists. reflexivity.
              + cbn in en. eapply IHn. eassumption.
          }
          subst. cbn in e. discriminate.
        - apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs.
          apply nth_error_None in en. subst ss.
          rewrite symbols_subst_length in en.
          apply is_rewrite_rule_head in hr. 2: eassumption.
          lia.
      }
      rewrite mkElims_app in e. cbn in e.
      destruct a. all: try discriminate.
      cbn in e. inversion e. subst. clear e.
      clear IHl.
      specialize (IHh _ _ #|l| hr hs _ eq_refl).
      forward IHh.
      { f_equal. f_equal. f_equal. clear - ee.
        apply (f_equal (firstn #|l|)) in ee as e.
        rewrite firstn_app in e. replace (#|l| - #|l|) with 0 in e by lia.
        cbn in e. rewrite app_nil_r in e.
        rewrite firstn_all in e.
        apply (f_equal (@List.length _)) in ee as h.
        rewrite app_length in h. cbn in h.
        pose proof (firstn_le_length n r.(elims)) as h'.
        rewrite h in h'.
        rewrite firstn_firstn in e.
        replace (Init.Nat.min #|l| n) with #|l| in e by lia.
        auto.
      }
      rename h into h0.
      destruct IHh as [
        [r' [θ [θ' [m [el [hr' [uθ [ehr [hm [hθ [epre [hrest h]]]]]]]]]]]]
      | [el [hel h']]
      ].
      + left. subst.
        eexists r', θ, θ', m, (el ++ [ eProj p0 ]). cbn.
        repeat match goal with
        | |- _ × _ => split
        end. all: auto.
        * apply (f_equal (@List.length _)) in ee as h.
          rewrite app_length in h. cbn in h.
          pose proof (firstn_le_length n r.(elims)) as h'.
          rewrite h in h'. lia.
        * rewrite 2!firstn_map. rewrite ee.
          rewrite <- 2!map_skipn. rewrite skipn_app.
          replace (m - #|l|) with 0 by lia.
          unfold skipn at 2.
          rewrite 2!map_app. cbn.
          eapply All2_app.
          -- rewrite 2!firstn_map in hrest.
             replace (firstn #|l| r.(elims))
             with l in hrest.
             2:{
              apply (f_equal (@List.length _)) in ee as h.
              rewrite app_length in h. cbn in h.
              pose proof (firstn_le_length n r.(elims)) as h'.
              rewrite h in h'.
              replace #|l| with (Init.Nat.min #|l| n) by lia.
              rewrite <- firstn_firstn. rewrite ee.
              replace #|l| with (#|l| + 0) by lia.
              rewrite firstn_app_2.
              cbn. rewrite app_nil_r. reflexivity.
             }
             rewrite 2!map_skipn. assumption.
          -- constructor. 2: constructor.
             constructor. all: assumption.
        * rewrite mkElims_app. cbn. reflexivity.
      + right. subst. eexists (el ++ [ eProj p0 ]). split.
        * rewrite 2!map_app. cbn. eapply All2_app.
          2:{ constructor. 2: constructor. constructor. all: assumption. }
          replace (firstn #|l| r.(elims))
          with l in hel.
          2:{
            apply (f_equal (@List.length _)) in ee as h.
            rewrite app_length in h. cbn in h.
            pose proof (firstn_le_length n r.(elims)) as h'.
            rewrite h in h'.
            replace #|l| with (Init.Nat.min #|l| n) by lia.
            rewrite <- firstn_firstn. rewrite ee.
            replace #|l| with (#|l| + 0) by lia.
            rewrite firstn_app_2.
            cbn. rewrite app_nil_r. reflexivity.
          }
          assumption.
        * rewrite mkElims_app. cbn. reflexivity.
    - right. eexists. split.
      + apply All2_same. intro. apply pred1_elim_refl_gen. assumption.
      + rewrite e0 in e. rewrite e.
        rewrite 2!mkElims_subst. f_equal. cbn.
        destruct (Nat.leb_spec #|s| (#|r.(pat_context)| + r.(head))).
        2:{
          apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs. lia.
        }
        destruct nth_error eqn:er.
        2:{
          apply nth_error_None in er. subst ss.
          rewrite symbols_subst_length in er.
          apply untyped_subslet_length in hs.
          rewrite subst_context_length in hs.
          apply is_rewrite_rule_head in hr. 2: auto.
          lia.
        }
        apply symbols_subst_nth_error in er as ?. subst.
        cbn. reflexivity.
  Qed.

  Lemma lhs_reducts :
    forall Σ k ui decl r Γ Δ s t,
      wf Σ ->
      is_rewrite_rule Σ k decl r ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ s (subst_context ss 0 r.(pat_context)) ->
      let prelhs0 :=
        mkElims (tRel (#|r.(pat_context)| + r.(head))) r.(elims)
      in
      let prelhs := subst0 s (subst ss #|s| prelhs0) in
      pred1 Σ Γ Δ prelhs t ->
      (∑ r' θ θ' m el,
        is_rewrite_rule Σ k decl r' ×
        untyped_subslet Γ θ (subst_context ss 0 r'.(pat_context)) ×
        r.(head) = r'.(head) ×
        m <= #|r.(elims)| × (* Not necessary *)
        All2 (pred1 Σ Γ Δ) θ θ' ×
        let prelhs1 :=
          mkElims
            (tRel (#|r.(pat_context)| + r.(head)))
            (firstn m r.(elims))
        in
        let prelhs2 := subst0 s (subst ss #|s| prelhs1) in
        prelhs2 = subst0 θ (subst ss #|θ| (lhs r')) ×
        All2
          (pred1_elim Σ Γ Δ)
          (skipn
            m
            (map (subst_elim s 0) (map (subst_elim ss #|s|) r.(elims))))
           el ×
        t = mkElims (subst0 θ' (subst ss #|θ| r'.(rhs))) el
      ) +
      (∑ el,
        All2
          (pred1_elim Σ Γ Δ)
          (map
            (subst_elim s 0)
            (map (subst_elim ss #|s|) r.(elims))
          )
          el ×
        t = mkElims (subst ss #|s| (tRel (#|r.(pat_context)| + r.(head)))) el
      ).
  Proof.
    intros Σ k ui decl r Γ Δ s t hΣ hr ss hs prelhs0 prelhs ht.
    pose proof (lhs_prefix_reducts Σ k ui decl r Γ Δ s t #|r.(elims)| hΣ hr hs)
      as thm.
    rewrite firstn_all in thm. simpl in thm.
    forward thm by auto.
    destruct thm as [
      [r' [θ [θ' [m [el [hr' [uθ [ehr [hm [hθ [epre [hrest h]]]]]]]]]]]]
    | [el [hel h']]
    ].
    - left. exists r', θ, θ', m, el. cbn.
      repeat match goal with
      | |- _ × _ => split
      end. all: auto.
      rewrite 2!firstn_map in hrest.
      rewrite firstn_all in hrest.
      assumption.
    - right. exists el. split. all: auto.
  Qed.

  Inductive All2_mask_subst (P : term -> term -> Type) :
    list bool -> list term -> list (option term) -> Type :=
  | All2_mask_subst_nil : All2_mask_subst P [] [] []
  | All2_mask_subst_true :
      forall t u m l s,
        P t u ->
        All2_mask_subst P m l s ->
        All2_mask_subst P (true :: m) (t :: l) (Some u :: s)
  | All2_mask_subst_false :
      forall t m l s,
        All2_mask_subst P m l s ->
        All2_mask_subst P (false :: m) (t :: l) (None :: s).

  (* Lemma All2_mask_subst_lin_set :
    forall P n m m' t u s l,
      lin_set n m = Some m' ->
      nth_error l n = Some t ->
      nth_error s n = Some (Some u) ->
      P t u ->
      All2_mask_subst P m l s ->
      All2_mask_subst P m' l s.
  Proof.
    intros P n m m' t u s l hm hl hs h hrec.
    induction hrec in t, u, h, n, m', hm, hl, hs |- *.
    - destruct n. all: cbn in hm. all: discriminate.
    - destruct n. 1: discriminate.
      cbn in *.
      destruct lin_set eqn:e. 2: discriminate.
      apply some_inj in hm. subst.
      constructor. 1: assumption.
      eapply IHhrec. all: eauto.
    - destruct n. 1: discriminate.
      cbn in *.
      destruct lin_set eqn:e. 2: discriminate.
      apply some_inj in hm. subst.
      constructor.
      eapply IHhrec. all: eauto.
  Qed. *)

  Lemma subs_add_S_cons :
    forall n u t s s',
      subs_add (S n) u (t :: s) = Some s' ->
      ∑ s'', subs_add n u s = Some s'' /\ s' = t :: s''.
  Proof.
    intros n u t s s' e.
    unfold subs_add in *. simpl in e.
    destruct nth_error as [[]|] eqn:e1. 1,3: discriminate.
    apply some_inj in e. subst.
    eexists. intuition reflexivity.
  Qed.

  Lemma All2_mask_subst_lin_set :
    forall P n m m' t u s s' l,
      lin_set n m = Some m' ->
      nth_error l n = Some t ->
      subs_add n u s = Some s' ->
      P t u ->
      All2_mask_subst P m l s ->
      All2_mask_subst P m' l s'.
  Proof.
    intros P n m m' t u s s' l hm hl hs h hrec.
    induction hrec in t, u, h, n, m', hm, hl, s', hs |- *.
    - destruct n. all: cbn in hm. all: discriminate.
    - destruct n. 1: discriminate.
      cbn in *.
      destruct lin_set eqn:e. 2: discriminate.
      apply some_inj in hm. subst.
      apply subs_add_S_cons in hs as hs'.
      destruct hs' as [s'' [hs' ?]]. subst.
      constructor. 1: assumption.
      eapply IHhrec. all: eauto.
    - destruct n.
      + cbn in *. apply some_inj in hm. subst.
        apply some_inj in hl. subst.
        apply some_inj in hs. subst.
        rewrite skipn_S. unfold skipn.
        constructor. all: assumption.
      + cbn in *.
        destruct lin_set eqn:e. 2: discriminate.
        apply some_inj in hm. subst.
        apply subs_add_S_cons in hs as hs'.
        destruct hs' as [s'' [hs' ?]]. subst.
        constructor.
        eapply IHhrec. all: eauto.
  Qed.

  Derive Signature for All2_mask_subst.

  Lemma All2_mask_subst_lin_merge :
    forall P m1 m2 m l s1 s2,
      lin_merge m1 m2 = Some m ->
      All2_mask_subst P m1 l s1 ->
      All2_mask_subst P m2 l s2 ->
      ∑ s, subs_merge s1 s2 = Some s × All2_mask_subst P m l s.
  Proof.
    intros P m1 m2 m l s1 s2 hm h1 h2.
    induction h1 in m2, m, hm, s2, h2 |- *.
    - inversion h2. subst. cbn in hm. apply some_inj in hm. subst.
      exists []. intuition auto.
    - dependent destruction h2. 1: discriminate.
      cbn in *.
      destruct lin_merge eqn:e. 2: discriminate.
      apply some_inj in hm. subst.
      specialize IHh1 with (1 := e) (2 := h2).
      destruct IHh1 as [s1 [hs h]].
      eexists. split.
      + rewrite hs. reflexivity.
      + constructor. all: auto.
    - dependent destruction h2.
      + cbn in *.
        destruct lin_merge eqn:e. 2: discriminate.
        apply some_inj in hm. subst.
        specialize IHh1 with (1 := e) (2 := h2).
        destruct IHh1 as [s1 [hs h]].
        eexists. split.
        * rewrite hs. reflexivity.
        * constructor. all: auto.
      + cbn in *.
        destruct lin_merge eqn:e. 2: discriminate.
        apply some_inj in hm. subst.
        specialize IHh1 with (1 := e) (2 := h2).
        destruct IHh1 as [s1 [hs h]].
        eexists. split.
        * rewrite hs. reflexivity.
        * constructor. assumption.
  Qed.

  Lemma All2_mask_subst_linear_mask_init :
    forall P npat l,
      #|l| = npat ->
      All2_mask_subst P (linear_mask_init npat) l (subs_empty npat).
  Proof.
    intros P npat l el.
    unfold linear_mask_init, subs_empty.
    induction npat in l, el |- *.
    - cbn.
      destruct l. 2: discriminate.
      constructor.
    - cbn.
      destruct l. 1: discriminate.
      cbn in *. constructor.
      apply IHnpat. lia.
  Qed.

  (* Is this the right statement? Will I be able to prove it? *)
  (* Lemma pred1_lift_inv :
    forall Σ Γ Γ' Δ Δ' Ξ Ξ' u v,
      pred1 Σ
        (Γ ,,, Δ ,,, lift_context #|Δ| 0 Ξ)
        (Γ' ,,, Δ' ,,, lift_context #|Δ'| 0 Ξ')
        (lift #|Δ| #|Ξ| u) v ->
      ∑ v',
        v = lift #|Δ'| #|Ξ'| v' ×
        pred1 Σ (Γ ,,, Ξ) (Γ' ,,, Ξ') u v'.
  Proof.
  Admitted.

  Corollary pred1_lift0_inv :
    forall Σ Γ Γ' Δ Δ' u v,
      pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| u) v ->
      ∑ v',
        v = lift0 #|Δ'| v' ×
        pred1 Σ Γ Γ' u v'.
  Admitted.

  Corollary pred1_lift1_inv :
    forall Σ Γ Γ' Δ Δ' na na' A A' u v,
      pred1 Σ
        ((Γ ,,, Δ) ,, vass na (lift0 #|Δ| A))
        ((Γ' ,,, Δ') ,, vass na' (lift0 #|Δ'| A'))
        (lift #|Δ| 1 u) v ->
      ∑ v',
        v = lift #|Δ'| 1 v' ×
        pred1 Σ (Γ ,, vass na A) (Γ' ,, vass na' A') u v'.
  Admitted. *)

  Lemma list_init_length :
    forall A (x : A) n,
      #|list_init x n| = n.
  Proof.
    intros A x n. induction n. 1: reflexivity.
    cbn. f_equal. assumption.
  Qed.

  Lemma nth_error_list_init :
    forall A (x : A) n l,
      n < l ->
      nth_error (list_init x l) n = Some x.
  Proof.
    intros A x n l h.
    induction l in n, h |- *. 1: lia.
    cbn. destruct n.
    - cbn. reflexivity.
    - cbn. apply IHl. lia.
  Qed.

  Lemma firstn_list_init :
    forall A n m (x : A),
      firstn n (list_init x m) = list_init x (min n m).
  Proof.
    intros A n m x.
    induction n in m |- *. 1: reflexivity.
    destruct m. 1: reflexivity.
    cbn. f_equal. apply IHn.
  Qed.

  Lemma skipn_list_init :
    forall A n m (x : A),
      skipn n (list_init x m) = list_init x (m - n).
  Proof.
    intros A n m x.
    induction m in n |- *.
    - cbn. rewrite skipn_nil. reflexivity.
    - destruct n. 1: reflexivity.
      cbn. rewrite skipn_S. apply IHm.
  Qed.

  Lemma subs_add_empty :
    forall n t l,
      n < l ->
      subs_add n t (list_init None l) =
      Some (list_init None n ++ Some t :: list_init None (l - S n)).
  Proof.
    intros n t l h.
    unfold subs_add.
    rewrite -> nth_error_list_init by assumption.
    rewrite firstn_list_init. rewrite skipn_list_init.
    f_equal. f_equal. f_equal. lia.
  Qed.

  Ltac sig_eapply h :=
    lazymatch type of h with
    | _ -> _ => let h' := open_constr:(h _) in sig_eapply h'
    | ∑ _, _ => eapply (projT2 h)
    end.

  (* Ltac sig_eapply h :=
    match type of h with
    | _ => refine h
    | _ -> _ => let h' := open_constr:(h _) in sig_eapply h'
    | _ × _ =>
      (let h' := open_constr:(snd h) in sig_eapply h') +
      (let h' := open_constr:(fst h) in sig_eapply h')
    | ∑ _, _ => let h' := open_constr:(projT2 h) in sig_eapply h'
    end. *)

  Tactic Notation "sig" "eapply" constr(h) := sig_eapply h.

  Lemma pattern_reduct :
    forall Σ Γ Δ p σ t k ui decl r m,
      wf Σ ->
      let npat := #|r.(pat_context)| in
      pattern npat p ->
      pattern_mask npat p = Some m ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ σ (subst_context ss 0 r.(pat_context)) ->
      pred1 Σ Γ Δ (subst0 σ p) t ->
      ∑ θ,
        All2_mask_subst (pred1 Σ Γ Δ) m σ θ ×
        forall θ',
          subs_complete θ θ' ->
          t = subst0 θ' p.
  Proof.
    intros Σ Γ Δ p σ t k ui decl r m hΣ npat hp hm ss hσ h.
    remember (subst0 σ p) as u eqn:e.
    induction h in p, σ, hσ, e, hp, m, hm |- *.
    all: try solve [
      destruct p ; try discriminate ;
      try (
        inversion hp ; rewrite <- H in e ;
        rewrite subst_mkApps in e ; cbn in e ;
        apply (f_equal isAppConstruct) in e ;
        rewrite 2!isAppConstruct_mkApps in e ;
        cbn in e ; discriminate
      ) ;
      cbn in hm ;
      inversion hp ; [|
        apply (f_equal isAppRel) in H ; cbn in H ;
        rewrite isAppRel_mkApps in H ; cbn in H ; discriminate
      ] ; subst ;
      cbn ; cbn in e ;
      let e1 := fresh "e1" in
      destruct nth_error eqn:e1 ; [|
        try discriminate ;
        apply nth_error_None in e1 ;
        apply untyped_subslet_length in hσ ;
        rewrite subst_context_length in hσ ;
        exfalso ; lia
      ] ;
      rewrite lift0_id in e ; subst ;
      match type of hp with
      | pattern _ (tRel ?n) =>
        replace (n - 0) with n in e1 by lia ;
        apply untyped_subslet_length in hσ as eσ ;
        rewrite subst_context_length in eσ ;
        eexists ; split ; [
          eapply All2_mask_subst_lin_set ; eauto ; [
            apply subs_add_empty ; eassumption
          | econstructor ; eassumption
          | eapply All2_mask_subst_linear_mask_init ; assumption
          ]
        | intros θ' hθ ;
          replace (n - 0) with n by lia ;
          apply subs_complete_spec in hθ as hh ; destruct hh as [? hθ'] ;
          erewrite hθ' ; [
            rewrite lift0_id ; reflexivity
          | rewrite nth_error_app_ge ; [
              rewrite list_init_length ; auto
            | rewrite list_init_length ;
              match goal with
              | |- nth_error _ ?n = _ =>
                replace n with 0 by lia
              end ;
              cbn ; reflexivity
            ]
          ]
        ]
      end
    ].
    - destruct p.
      all: cbn in hm. all: try discriminate.
      2:{
        cbn in e. inversion e. subst.
        destruct p1. all: try discriminate.
        inversion hp.
        apply (f_equal isAppRel) in H. cbn in H.
        rewrite isAppRel_mkApps in H. cbn in H. discriminate.
      }
      clear IHh1 IHh2 IHh3.
      inversion hp.
      2:{
        apply (f_equal isAppRel) in H. cbn in H.
        rewrite isAppRel_mkApps in H. cbn in H. discriminate.
      } subst.
      cbn. cbn in e.
      destruct nth_error eqn:e1. 2: discriminate.
      rewrite lift0_id in e. subst.
      replace (n - 0) with n in e1 by lia.
      apply untyped_subslet_length in hσ as eσ.
      rewrite subst_context_length in eσ.
      eexists. split.
      + eapply All2_mask_subst_lin_set. all: eauto.
        2:{
          eapply pred_beta.
          all: eassumption.
        }
        * apply subs_add_empty. eassumption.
        * eapply All2_mask_subst_linear_mask_init. assumption.
      + intros θ' hθ.
        replace (n - 0) with n by lia.
        apply subs_complete_spec in hθ as hh. destruct hh as [? hθ'].
        erewrite hθ'.
        2:{
          rewrite nth_error_app_ge.
          1:{ rewrite list_init_length. auto. }
          rewrite list_init_length.
          match goal with
          | |- nth_error _ ?n = _ =>
          replace n with 0 by lia
          end.
          cbn. reflexivity.
        }
        rewrite lift0_id. reflexivity.
    - inversion hp.
      2:{
        subst. rewrite subst_mkApps in e. cbn in e.
        apply (f_equal isElimSymb) in e.
        rewrite isElimSymb_mkApps in e. cbn in e.
        rewrite isElimSymb_subst in e.
        { apply untyped_subslet_length in u.
          rewrite subst_context_length in u. rewrite u.
          eapply isElimSymb_lhs.
          eapply declared_symbol_head in d. all: eauto.
        }
        discriminate.
      } subst.
      cbn in hm. cbn. cbn in e.
      destruct nth_error eqn:e1.
      2:{
        apply nth_error_None in e1.
        apply untyped_subslet_length in hσ.
        rewrite subst_context_length in hσ.
        exfalso. lia.
      }
      rewrite lift0_id in e. subst.
      replace (n0 - 0) with n0 in e1 by lia.
      apply untyped_subslet_length in hσ as eσ.
      rewrite subst_context_length in eσ.
      eexists. split.
      + eapply All2_mask_subst_lin_set. all: eauto.
        * apply subs_add_empty. eassumption.
        * eapply pred_rewrite_rule. all: eassumption.
        * eapply All2_mask_subst_linear_mask_init. assumption.
      + intros θ' hθ.
        replace (n0 - 0) with n0 by lia.
        apply subs_complete_spec in hθ as hh. destruct hh as [? hθ'].
        erewrite hθ'.
        2:{
          rewrite nth_error_app_ge.
          1:{ rewrite list_init_length. auto. }
          rewrite list_init_length.
          match goal with
          | |- nth_error _ ?n = _ =>
          replace n with 0 by lia
          end.
          cbn. reflexivity.
        }
        rewrite lift0_id. reflexivity.
    - inversion hp.
      2:{
        subst. rewrite subst_mkApps in e. cbn in e.
        apply (f_equal isElimSymb) in e.
        rewrite isElimSymb_mkApps in e. cbn in e.
        rewrite isElimSymb_subst in e.
        { apply untyped_subslet_length in u.
          rewrite subst_context_length in u. rewrite u.
          eapply isElimSymb_lhs.
          eapply declared_symbol_par_head in d. all: eauto.
        }
        discriminate.
      } subst.
      cbn in hm. cbn. cbn in e.
      destruct nth_error eqn:e1.
      2:{
        apply nth_error_None in e1.
        apply untyped_subslet_length in hσ.
        rewrite subst_context_length in hσ.
        exfalso. lia.
      }
      rewrite lift0_id in e. subst.
      replace (n0 - 0) with n0 in e1 by lia.
      apply untyped_subslet_length in hσ as eσ.
      rewrite subst_context_length in eσ.
      eexists. split.
      + eapply All2_mask_subst_lin_set. all: eauto.
        * apply subs_add_empty. eassumption.
        * eapply pred_par_rewrite_rule. all: eassumption.
        * eapply All2_mask_subst_linear_mask_init. assumption.
      + intros θ' hθ.
        replace (n0 - 0) with n0 by lia.
        apply subs_complete_spec in hθ as hh. destruct hh as [? hθ'].
        erewrite hθ'.
        2:{
          rewrite nth_error_app_ge.
          1:{ rewrite list_init_length. auto. }
          rewrite list_init_length.
          match goal with
          | |- nth_error _ ?n = _ =>
          replace n with 0 by lia
          end.
          cbn. reflexivity.
        }
        rewrite lift0_id. reflexivity.
    - destruct p. all: try discriminate.
      + cbn in hm. cbn. cbn in e.
        inversion hp.
        2:{
          apply (f_equal isAppRel) in H. cbn in H.
          rewrite isAppRel_mkApps in H. cbn in H. discriminate.
        } subst.
        destruct nth_error eqn:e1. 2: discriminate.
        rewrite lift0_id in e. subst.
        replace (n - 0) with n in e1 by lia.
        apply untyped_subslet_length in hσ as eσ.
        rewrite subst_context_length in eσ.
        eexists. split.
        * eapply All2_mask_subst_lin_set. all: eauto.
          -- apply subs_add_empty. eassumption.
          -- econstructor. all: eassumption.
          -- eapply All2_mask_subst_linear_mask_init. assumption.
        * intros θ' hθ.
          replace (n - 0) with n by lia.
          apply subs_complete_spec in hθ as hh. destruct hh as [? hθ'].
          erewrite hθ'.
          2:{
            rewrite nth_error_app_ge.
            1:{ rewrite list_init_length. auto. }
            rewrite list_init_length.
            match goal with
            | |- nth_error _ ?n = _ =>
            replace n with 0 by lia
            end.
            cbn. reflexivity.
          }
          rewrite lift0_id. reflexivity.
      + cbn in e. inversion e. subst. clear e.
        inversion hp.
        destruct args as [| p args _] using list_rect_rev. 1: discriminate.
        rewrite <- mkApps_nested in H. cbn in H. inversion H. subst.
        apply All_app in H0 as [ha hp2]. inversion hp2. subst.
        cbn in hm.
        destruct pattern_mask eqn:e1. 2: discriminate.
        destruct (pattern_mask _ p2) eqn:e2. 2: discriminate.
        specialize IHh1 with (2 := e1) (4 := eq_refl).
        forward IHh1 by (constructor ; auto).
        forward IHh1 by auto.
        destruct IHh1 as [θ1 [hm1 hθ1]].
        specialize IHh2 with (2 := e2) (4 := eq_refl).
        forward IHh2 by auto.
        forward IHh2 by auto.
        destruct IHh2 as [θ2 [hm2 hθ2]].
        eapply All2_mask_subst_lin_merge in hm. all: eauto.
        destruct hm as [θ [eθ hθ]].
        exists θ. split. 1: assumption.
        intros θ' hθ'.
        rewrite <- mkApps_nested. cbn.
        rewrite subst_mkApps. cbn.
        eapply subs_merge_complete in eθ as h. 2: eauto.
        destruct h as [? ?].
        erewrite hθ1. 2: eassumption.
        erewrite hθ2. 2: eassumption.
        rewrite subst_mkApps. cbn. reflexivity.
    - inversion hp.
      + subst.
        cbn in hm. cbn. cbn in i.
        destruct nth_error eqn:e1. 2: discriminate.
        rewrite lift0_id in i.
        replace (n - 0) with n in e1 by lia.
        apply untyped_subslet_length in hσ as eσ.
        rewrite subst_context_length in eσ.
        eexists. split.
        * eapply All2_mask_subst_lin_set. all: eauto.
          -- apply subs_add_empty. eassumption.
          -- econstructor. all: eassumption.
          -- eapply All2_mask_subst_linear_mask_init. assumption.
        * intros θ' hθ.
          replace (n - 0) with n by lia.
          apply subs_complete_spec in hθ as hh. destruct hh as [? hθ'].
          erewrite hθ'.
          2:{
            rewrite nth_error_app_ge.
            1:{ rewrite list_init_length. auto. }
            rewrite list_init_length.
            match goal with
            | |- nth_error _ ?n = _ =>
            replace n with 0 by lia
            end.
            cbn. reflexivity.
          }
          rewrite lift0_id. reflexivity.
      + subst. rewrite subst_mkApps in i. cbn in i.
        destruct args using list_rect_rev.
        2:{
          rewrite map_app in i. rewrite <- mkApps_nested in i.
          cbn in i. discriminate.
        }
        cbn in *. apply some_inj in hm. subst.
        apply untyped_subslet_length in hσ as eσ.
        rewrite subst_context_length in eσ.
        eexists. split.
        * eapply All2_mask_subst_linear_mask_init. assumption.
        * intros θ' hθ'. reflexivity.
  Qed.

  (* TODO MOVE *)
  Lemma All2_map_inv_left :
    forall A B C P l l' f,
      @All2 A B P (map f l) l' ->
      @All2 C B (fun x y => P (f x) y) l l'.
  Proof.
    intros A B C P l l' f h.
    dependent induction h.
    - destruct l. 2: discriminate.
      constructor.
    - destruct l0. 1: discriminate.
      cbn in H. inversion H. subst.
      constructor. 1: assumption.
      apply IHh. reflexivity.
  Qed.

  Lemma elim_reduct :
    forall Σ Γ Δ e σ t k ui decl r m,
      wf Σ ->
      let npat := #|r.(pat_context)| in
      elim_pattern npat e ->
      elim_mask npat e = Some m ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ σ (subst_context ss 0 r.(pat_context)) ->
      pred1_elim Σ Γ Δ (subst_elim σ 0 e) t ->
      ∑ θ,
        All2_mask_subst (pred1 Σ Γ Δ) m σ θ ×
        forall θ',
          subs_complete θ θ' ->
          t = subst_elim θ' 0 e.
  Proof.
    intros Σ Γ Δ e σ t k ui decl r m hΣ npat he hm ss hσ h.
    remember (subst_elim σ 0 e) as u eqn:e1.
    induction h in e, σ, hσ, e1, he, m, hm |- *.
    - destruct e. all: try discriminate.
      cbn in e1. inversion e1. subst. clear e1.
      inversion he. subst.
      cbn in hm.
      eapply pattern_reduct in p. all: eauto.
      destruct p as [θ [h1 h2]].
      exists θ. split.
      + assumption.
      + intros θ' hθ. cbn. erewrite h2. 2: eassumption.
        reflexivity.
    - destruct e. all: try discriminate.
      cbn in e1. inversion e1. subst. clear e1.
      inversion he. subst.
      cbn in hm.
      destruct pattern_mask eqn:e1. 2: discriminate.
      destruct monad_map eqn:e2. 2: discriminate.
      destruct monad_fold_right eqn:e3. 2: discriminate.
      cbn.
      eapply pattern_reduct in p0. all: eauto.
      destruct p0 as [θ1 [hm1 ih1]].
      assert (hbrs :
        All2 (fun br br' =>
          br.1 = br'.1 ×
          forall m,
            pattern_mask npat br.2 = Some m ->
            ∑ θ,
              All2_mask_subst (pred1 Σ Γ Δ) m σ θ ×
              forall θ',
                subs_complete θ θ' ->
                br'.2 = subst0 θ' br.2
        ) brs0 brs'
      ).
      { apply All2_map_inv_left in a.
        induction a in H3 |- *. 1: constructor.
        destruct x as [n1 u1], y as [n2 u2]. cbn in *.
        inversion H3. subst. cbn in *.
        destruct r0 as [hu ?]. subst.
        forward IHa by auto.
        constructor.
        - cbn. intuition auto.
          eapply pattern_reduct in hu. all: eauto.
        - apply IHa.
      }
      assert (
        ∑ θ,
          All2_mask_subst (pred1 Σ Γ Δ) l1 σ θ ×
          forall θ',
            subs_complete θ θ' ->
            All2 (fun br br' =>
              br.1 = br'.1 /\
              br'.2 = subst0 θ' br.2
            ) brs0 brs'
      ) as [θ2 [hm2 hθ2]].
      { induction hbrs in l0, e2, l1, e3 |- *.
        - cbn in *. apply some_inj in e2. subst.
          cbn in e3. apply some_inj in e3. subst.
          eexists. split.
          + eapply All2_mask_subst_linear_mask_init.
            apply untyped_subslet_length in hσ.
            rewrite subst_context_length in hσ. assumption.
          + intros θ' hθ. constructor.
        - destruct x as [n0 u], y as [n v]. cbn in *.
          destruct r0 as [? ih]. subst.
          destruct (pattern_mask _ u) eqn:e4. 2: discriminate.
          destruct monad_map eqn:e5. 2: discriminate.
          apply some_inj in e2. subst.
          cbn in e3. destruct monad_fold_right eqn:e6. 2: discriminate.
          specialize ih with (1 := eq_refl).
          destruct ih as [θ2 [hm2 hθ2]].
          specialize IHhbrs with (1 := eq_refl) (2 := e6).
          destruct IHhbrs as [θ3 [hm3 hθ3]].
          eapply All2_mask_subst_lin_merge in e3. all: eauto.
          destruct e3 as [θ [hθ hm]].
          eexists. split.
          + eassumption.
          + intros θ' hθ'.
            eapply subs_merge_complete in hθ. 2: eassumption.
            destruct hθ.
            constructor.
            * cbn. intuition auto.
            * apply hθ3. auto.
      }
      eapply All2_mask_subst_lin_merge in hm. all: eauto.
      destruct hm as [θ [eθ hm]].
      exists θ. split. 1: assumption.
      intros θ' hθ.
      eapply subs_merge_complete in hθ. 2: eassumption.
      destruct hθ as [cθ1 cθ2].
      erewrite -> ih1 by eauto.
      f_equal.
      specialize hθ2 with (1 := cθ2).
      clear - hθ2.
      induction hθ2 as [| [m u] [n v] brs brs' [? ?] a ih ]. 1: reflexivity.
      cbn in *. subst.
      intuition auto.
    - destruct e. all: try discriminate.
      cbn in e1. inversion e1. subst. clear e1.
      cbn in hm. apply some_inj in hm. subst.
      cbn. eexists. split.
      + eapply All2_mask_subst_linear_mask_init.
        apply untyped_subslet_length in hσ.
        rewrite subst_context_length in hσ. assumption.
      + intros. reflexivity.
  Qed.

  Lemma elims_reduct :
    forall Σ Γ Δ σ el el' k decl ui r m,
      wf Σ ->
      let npat := #|r.(pat_context)| in
      All (elim_pattern npat) el ->
      linear_mask npat el = Some m ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ σ (subst_context ss 0 r.(pat_context)) ->
      All2 (pred1_elim Σ Γ Δ) (map (subst_elim σ 0) el) el' ->
      ∑ θ,
        All2_mask_subst (pred1 Σ Γ Δ) m σ θ ×
        forall θ',
          subs_complete θ θ' ->
          el' = map (subst_elim θ' 0) el.
  Proof.
    intros Σ Γ Δ σ el el' k decl ui r m hΣ npat hp hl ss hσ h.
    unfold linear_mask in hl.
    destruct monad_map as [m'|] eqn:e. 2: discriminate.
    cbn in hl.
    remember (map (subst_elim σ 0) el) as l eqn:eql.
    induction h in el, hp, eql, m', e, m, hl |- *.
    - destruct el. 2: discriminate.
      cbn in *. apply some_inj in e. subst.
      cbn in hl. apply some_inj in hl. subst.
      eexists. split.
      + eapply All2_mask_subst_linear_mask_init.
        apply untyped_subslet_length in hσ.
        rewrite subst_context_length in hσ.
        assumption.
      + intros. reflexivity.
    - destruct el as [| d el]. 1: discriminate.
      cbn in eql. inversion eql. subst. clear eql.
      cbn in e. destruct elim_mask eqn:e1. 2: discriminate.
      destruct monad_map eqn:e2. 2: discriminate.
      apply some_inj in e. subst.
      cbn in hl. destruct monad_fold_right eqn:e3. 2: discriminate.
      inversion hp. subst.
      specialize IHh with (2 := e2) (3 := e3) (4 := eq_refl).
      forward IHh by auto.
      destruct IHh as [θ1 [hm1 hθ1]].
      eapply elim_reduct in r0. all: eauto.
      destruct r0 as [θ2 [hm2 hθ2]].
      eapply All2_mask_subst_lin_merge in hl. all: eauto.
      destruct hl as [θ [eθ hm]].
      exists θ. split. 1: auto.
      intros θ' hθ.
      eapply subs_merge_complete in hθ. 2: eauto.
      destruct hθ.
      cbn. erewrite hθ1. 2: eauto.
      f_equal.
      eapply hθ2. assumption.
  Qed.

  Lemma declared_symbol_pattern :
    forall Σ k decl n r,
      wf Σ ->
      declared_symbol Σ k decl ->
      nth_error decl.(rules) n = Some r ->
      All (elim_pattern #|r.(pat_context)|) r.(elims).
  Proof.
    intros Σ k decl n r hΣ h e.
    unfold declared_symbol in h.
    eapply lookup_on_global_env in h. 2: eauto.
    destruct h as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    destruct decl' as [hctx [hr [hpr hprr]]].
    eapply All_nth_error in hr. 2: eassumption.
    destruct hr as [T hl hr hh he].
    assumption.
  Qed.

  Lemma declared_symbol_par_pattern :
    forall Σ k decl n r,
      wf Σ ->
      declared_symbol Σ k decl ->
      nth_error decl.(prules) n = Some r ->
      All (elim_pattern #|r.(pat_context)|) r.(elims).
  Proof.
    intros Σ k decl n r hΣ h e.
    unfold declared_symbol in h.
    eapply lookup_on_global_env in h. 2: eauto.
    destruct h as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    destruct decl' as [hctx [hr [hpr hprr]]].
    eapply All_nth_error in hpr. 2: eassumption.
    destruct hpr as [T hl hpr hh he].
    assumption.
  Qed.

  Lemma is_rewrite_rule_pattern :
    forall Σ k decl r,
      wf Σ ->
      is_rewrite_rule Σ k decl r ->
      All (elim_pattern #|r.(pat_context)|) r.(elims).
  Proof.
    intros Σ k decl r hΣ hr.
    destruct hr as [h [[n e]|[n e]]].
    - eapply declared_symbol_pattern. all: eassumption.
    - eapply declared_symbol_par_pattern. all: eassumption.
  Qed.

  Lemma pattern_subst :
    forall npat p n σ,
      pattern npat p ->
      n >= npat ->
      pattern npat (subst σ n p).
  Proof.
    intros npat p n σ hp hn.
    induction hp using pattern_all_rect.
    - cbn. destruct (Nat.leb_spec0 n n0). 1: exfalso ; lia.
      constructor. auto.
    - rewrite subst_mkApps. cbn. constructor.
      apply All_map. eapply All_impl. 1: eassumption.
      intros p hp. unfold compose.
      assumption.
  Qed.

  Lemma elim_pattern_subst :
    forall npat e n σ,
      elim_pattern npat e ->
      n >= npat ->
      elim_pattern npat (subst_elim σ n e).
  Proof.
    intros npat e n σ he hn.
    induction he.
    - cbn. constructor. apply pattern_subst. all: auto.
    - cbn. constructor.
      + apply pattern_subst. all: auto.
      + apply All_map. eapply All_impl. 1: eauto.
        cbn. unfold compose. intros [m u] hu. cbn in *.
        apply pattern_subst. all: auto.
    - cbn. constructor.
  Qed.

  Lemma declared_symbol_linear :
    forall Σ k decl n r,
      wf Σ ->
      declared_symbol Σ k decl ->
      nth_error decl.(rules) n = Some r ->
      linear #|r.(pat_context)| r.(elims).
  Proof.
    intros Σ k decl n r hΣ h e.
    unfold declared_symbol in h.
    eapply lookup_on_global_env in h. 2: eauto.
    destruct h as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    destruct decl' as [hctx [hr [hpr hprr]]].
    eapply All_nth_error in hr. 2: eassumption.
    destruct hr as [T hl hr hh hlin he].
    assumption.
  Qed.

  Lemma declared_symbol_par_linear :
    forall Σ k decl n r,
      wf Σ ->
      declared_symbol Σ k decl ->
      nth_error decl.(prules) n = Some r ->
      linear #|r.(pat_context)| r.(elims).
  Proof.
    intros Σ k decl n r hΣ h e.
    unfold declared_symbol in h.
    eapply lookup_on_global_env in h. 2: eauto.
    destruct h as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    destruct decl' as [hctx [hr [hpr hprr]]].
    eapply All_nth_error in hpr. 2: eassumption.
    destruct hpr as [T hl hpr hh hlin he].
    assumption.
  Qed.

  Lemma is_rewrite_rule_linear :
    forall Σ k decl r,
      wf Σ ->
      is_rewrite_rule Σ k decl r ->
      linear #|r.(pat_context)| r.(elims).
  Proof.
    intros Σ k decl r hΣ hr.
    destruct hr as [h [[n e]|[n e]]].
    - eapply declared_symbol_linear. all: eassumption.
    - eapply declared_symbol_par_linear. all: eassumption.
  Qed.

  (* TODO MOVE *)
  Lemma lin_set_eq :
    forall n m,
      lin_set n m =
      match nth_error m n with
      | Some true => None
      | Some false => Some (firstn n m ++ true :: skipn (S n) m)
      | None => None
      end.
  Proof.
    intros n m.
    induction n in m |- *.
    - cbn. destruct m as [| [] m]. all: reflexivity.
    - cbn. destruct m as [| [] m].
      + reflexivity.
      + destruct lin_set eqn:e.
        * cbn. rewrite IHn in e.
          destruct nth_error as [[]|] eqn: e1. 1,3: discriminate.
          apply some_inj in e. subst.
          reflexivity.
        * cbn. rewrite IHn in e.
          destruct nth_error as [[]|] eqn: e1. 2: discriminate.
          all: reflexivity.
      + destruct lin_set eqn:e.
        * cbn. rewrite IHn in e.
          destruct nth_error as [[]|] eqn: e1. 1,3: discriminate.
          apply some_inj in e. subst.
          reflexivity.
        * cbn. rewrite IHn in e.
          destruct nth_error as [[]|] eqn: e1. 2: discriminate.
          all: reflexivity.
  Qed.

  (* TODO MOVE *)
  Lemma linear_mask_init_length :
    forall n,
      #|linear_mask_init n| = n.
  Proof.
    intros n. unfold linear_mask_init.
    apply list_init_length.
  Qed.

  Lemma pattern_mask_subst :
    forall npat n σ p m,
      pattern_mask npat p = Some m ->
      n >= npat ->
      pattern_mask npat (subst σ n p) = Some m.
  Proof.
    intros npat n σ p m hp hn.
    induction p in m, hp |- *.
    all: try discriminate.
    - cbn in *.
      rewrite lin_set_eq in hp.
      destruct nth_error as [[]|] eqn:e. 1,3: discriminate.
      apply some_inj in hp. subst.
      apply nth_error_Some_length in e as h.
      rewrite linear_mask_init_length in h.
      destruct (Nat.leb_spec0 n n0). 1: lia.
      cbn. rewrite lin_set_eq.
      rewrite e. reflexivity.
    - cbn in *.
      destruct pattern_mask eqn:e1. 2: discriminate.
      move hp at top.
      destruct pattern_mask eqn:e2. 2: discriminate.
      specialize IHp1 with (1 := eq_refl).
      specialize IHp2 with (1 := eq_refl).
      rewrite IHp1. rewrite IHp2. assumption.
    - cbn in *.
      assumption.
  Qed.

  Lemma elim_mask_subst :
    forall npat n σ e m,
      elim_mask npat e = Some m ->
      n >= npat ->
      elim_mask npat (subst_elim σ n e) = Some m.
  Proof.
    intros npat n σ e m hm hn.
    destruct e.
    - cbn in hm. cbn.
      eapply pattern_mask_subst. all: auto.
    - cbn in hm. cbn.
      destruct pattern_mask eqn:ep. 2: discriminate.
      destruct monad_map as [ml|] eqn:el. 2: discriminate.
      destruct monad_fold_right eqn:em. 2: discriminate.
      eapply pattern_mask_subst with (σ := σ) in ep. 2: eauto.
      rewrite ep.
      match goal with
      | |- context [ monad_map ?f ?l ] =>
        assert (monad_map f l = Some ml) as eml
      end.
      { induction brs as [| [k u]] in ml, el |- *.
        - cbn in el. apply some_inj in el. subst.
          cbn. reflexivity.
        - cbn in el. destruct pattern_mask eqn:eu. 2: discriminate.
          destruct monad_map eqn:em. 2: discriminate.
          apply some_inj in el. subst.
          cbn.
          eapply pattern_mask_subst with (σ := σ) in eu. 2: eauto.
          rewrite eu.
          specialize IHbrs with (1 := eq_refl). rewrite IHbrs.
          reflexivity.
      }
      rewrite eml. rewrite em.
      assumption.
    - cbn in hm. apply some_inj in hm. subst.
      cbn. reflexivity.
  Qed.

  Lemma linear_mask_subst :
    forall npat n σ l m,
      linear_mask npat l = Some m ->
      n >= npat ->
      linear_mask npat (map (subst_elim σ n) l) = Some m.
  Proof.
    intros npat n σ l m hm hn.
    unfold linear_mask in *.
    destruct monad_map as [ml|] eqn:e. 2: discriminate.
    cbn in hm.
    assert (h : monad_map (elim_mask npat) (map (subst_elim σ n) l) = Some ml).
    { induction l as [| x l ih] in ml, e |- *.
      - cbn in e. apply some_inj in e. subst.
        cbn. reflexivity.
      - cbn in e. destruct elim_mask eqn:ex. 2: discriminate.
        destruct monad_map eqn:em. 2: discriminate.
        apply some_inj in e. subst.
        cbn. eapply elim_mask_subst with (σ := σ) in ex. 2: eauto.
        rewrite ex.
        specialize ih with (1 := eq_refl). rewrite ih.
        reflexivity.
    }
    rewrite h. cbn. assumption.
  Qed.

  Lemma linear_subst :
    forall npat n σ l,
      linear npat l ->
      n >= npat ->
      linear npat (map (subst_elim σ n) l).
  Proof.
    intros npat n σ l hl hn.
    unfold linear in *.
    destruct linear_mask eqn:e. 2: discriminate.
    eapply linear_mask_subst with (σ := σ) in e. 2: eauto.
    rewrite e. assumption.
  Qed.

  Lemma All2_mask_subst_all :
    forall P m σ θ,
      forallb (fun x => x) m ->
      All2_mask_subst P m σ θ ->
      ∑ θ',
        map_option_out θ = Some θ' ×
        All2 P σ θ'.
  Proof.
    intros P m σ θ hm h.
    induction h.
    - eexists. intuition constructor.
    - inversion hm. forward IHh by auto.
      destruct IHh as [θ' [h1 h2]].
      eexists. cbn. rewrite h1.
      intuition eauto.
    - inversion hm.
  Qed.

  (** When you do not apply a rewrite rule to a lhs only the substitution
    reduces.
  *)
  Lemma lhs_elim_reduct :
    forall Σ k ui decl r Γ Δ σ el',
      wf Σ ->
      is_rewrite_rule Σ k decl r ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ σ (subst_context ss 0 r.(pat_context)) ->
      let el := (map (subst_elim ss #|σ|) r.(elims)) in
      All2 (pred1_elim Σ Γ Δ) (map (subst_elim σ 0) el) el' ->
      ∑ σ',
        All2 (pred1 Σ Γ Δ) σ σ' ×
        el' = map (subst_elim σ' 0) el.
  Proof.
    intros Σ k ui decl r Γ Δ σ el' hΣ hr ss hσ el h.
    eapply is_rewrite_rule_linear in hr as hlin. 2: auto.
    eapply linear_subst with (σ := ss) (n := #|σ|) in hlin.
    2:{
      apply untyped_subslet_length in hσ.
      rewrite subst_context_length in hσ.
      lia.
    }
    unfold linear in hlin.
    destruct linear_mask eqn:elin. 2: discriminate.
    eapply elims_reduct in h. all: eauto.
    2:{
      apply is_rewrite_rule_pattern in hr. 2: auto.
      apply All_map. eapply All_impl. 1: eauto.
      intros e he. unfold compose.
      eapply elim_pattern_subst in he. 1: eauto.
      apply untyped_subslet_length in hσ.
      rewrite subst_context_length in hσ.
      lia.
    }
    destruct h as [θ [hm hc]].
    eapply All2_mask_subst_all in hlin. 2: eauto.
    destruct hlin as [θ' [eθ h]].
    eexists. intuition eauto.
    apply hc.
    apply map_option_out_subs_complete. auto.
  Qed.

  Inductive All_mask_subst (P : term -> Type) :
    list bool -> partial_subst -> Type :=
  | All_mask_subst_nil : All_mask_subst P [] []
  | All_mask_subst_true m t σ :
      P t ->
      All_mask_subst P m σ ->
      All_mask_subst P (true :: m) (Some t :: σ)
  | All_mask_subst_false m σ :
      All_mask_subst P m σ ->
      All_mask_subst P (false :: m) (None :: σ).

  (* TODO MOVE *)
  Fixpoint decompose_elims_rec t l :=
    match t with
    | tApp u v => decompose_elims_rec u (eApp v :: l)
    | tCase ind p c brs => decompose_elims_rec c (eCase ind p brs :: l)
    | tProj p t => decompose_elims_rec t (eProj p :: l)
    | t => (t, l)
    end.

  Definition decompose_elims t := decompose_elims_rec t [].

  Lemma decompose_elims_mkElims :
    forall t l,
      let d := decompose_elims_rec t l in
      mkElims t l = mkElims d.1 d.2.
  Proof.
    intros t l. induction t in l |- *.
    all: try reflexivity.
    - cbn. rewrite <- IHt1. reflexivity.
    - cbn. rewrite <- IHt2. reflexivity.
    - cbn. rewrite <- IHt. reflexivity.
  Qed.

  Lemma decompose_elims_fst :
    forall t l l',
      (decompose_elims_rec t l).1 = (decompose_elims_rec t l').1.
  Proof.
    intros t l l'.
    induction t in l, l' |- *.
    all: try reflexivity.
    - cbn. apply IHt1.
    - cbn. apply IHt2.
    - cbn. apply IHt.
  Qed.

  Lemma decompose_elims_snd :
    forall t l,
      (decompose_elims_rec t l).2 = (decompose_elims t).2 ++ l.
  Proof.
    intros t l.
    induction t in l |- *.
    all: try reflexivity.
    - cbn. rewrite IHt1. rewrite (IHt1 [_]).
      rewrite <- app_assoc. reflexivity.
    - cbn. rewrite IHt2. rewrite (IHt2 [_]).
      rewrite <- app_assoc. reflexivity.
    - cbn. rewrite IHt. rewrite (IHt [_]).
      rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma mkElims_decompose_elims :
    forall t l,
      decompose_elims (mkElims t l) =
      ((decompose_elims t).1, (decompose_elims t).2 ++ l).
  Proof.
    intros t l.
    induction l as [| [] l ih] in t |- *.
    - cbn. rewrite app_nil_r.
      change (decompose_elims_rec t []) with (decompose_elims t).
      set (d := decompose_elims _). destruct d. reflexivity.
    - cbn. unfold decompose_elims in *. rewrite ih. cbn. f_equal.
      + apply decompose_elims_fst.
      + rewrite decompose_elims_snd.
        rewrite <- app_assoc. reflexivity.
    - cbn. unfold decompose_elims in *. rewrite ih. cbn. f_equal.
      + apply decompose_elims_fst.
      + rewrite decompose_elims_snd.
        rewrite <- app_assoc. reflexivity.
    - cbn. unfold decompose_elims in *. rewrite ih. cbn. f_equal.
      + apply decompose_elims_fst.
      + rewrite decompose_elims_snd.
        rewrite <- app_assoc. reflexivity.
  Qed.

  (* TODO MOVE *)
  (** Identity partial substitution on a given mask
    Similar to idsn I suppose.
  *)
  Fixpoint id_mask i m : partial_subst :=
    match m with
    | true  :: m => Some (tRel i) :: id_mask (S i) m
    | false :: m => None :: id_mask (S i) m
    | [] => []
    end.

  Lemma id_mask_length :
    forall i m,
      #|id_mask i m| = #|m|.
  Proof.
    intros i m.
    induction m as [| [] m ih] in i |- *.
    - reflexivity.
    - cbn. f_equal. apply ih.
    - cbn. f_equal. apply ih.
  Qed.

  Lemma id_mask_app :
    forall i m1 m2,
      id_mask i (m1 ++ m2) = id_mask i m1 ++ id_mask (i + #|m1|) m2.
  Proof.
    intros i m1 m2.
    induction m1 as [| [] m1 ih] in i, m2 |- *.
    - cbn. f_equal. lia.
    - cbn. f_equal. rewrite ih. f_equal. f_equal. lia.
    - cbn. f_equal. rewrite ih. f_equal. f_equal. lia.
  Qed.

  (* TODO MOVE *)
  Lemma All_rev_rect :
    forall A P (R : list A -> Type),
      R [] ->
      (forall x l,
        P x ->
        All P l ->
        R l ->
        R (l ++ [x])
      ) ->
      forall l, All P l -> R l.
  Proof.
    intros A P R Rnil Rcons l h.
    rewrite <- rev_involutive.
    apply All_rev in h. revert h.
    generalize (List.rev l). clear l.
    intros l h. induction h.
    - apply Rnil.
    - cbn. apply Rcons. all: auto.
      apply All_rev. assumption.
  Qed.

  Lemma lin_merge_id_mask :
    forall m1 m2 m i,
      lin_merge m1 m2 = Some m ->
      subs_merge (id_mask i m1) (id_mask i m2) = Some (id_mask i m).
  Proof.
    intros m1 m2 m i hm.
    induction m1 as [| [] m1 ih] in i, m2, m, hm |- *.
    - cbn in hm. destruct m2. 2: discriminate.
      apply some_inj in hm. subst.
      cbn. reflexivity.
    - cbn in hm. destruct m2 as [| [] m2]. 1,2: discriminate.
      destruct lin_merge eqn:e. 2: discriminate.
      apply some_inj in hm. subst.
      cbn. erewrite -> ih by eassumption.
      reflexivity.
    - cbn in hm. destruct m2 as [| b m2]. 1: discriminate.
      destruct lin_merge eqn:e. 2: discriminate.
      apply some_inj in hm. subst.
      destruct b.
      + cbn. erewrite -> ih by eassumption.
        reflexivity.
      + cbn. erewrite -> ih by eassumption.
        reflexivity.
  Qed.

  Lemma id_mask_subst :
    forall p m npat σ,
      pattern npat p ->
      pattern_mask npat p = Some m ->
      subs_complete (id_mask 0 m) σ ->
      p = subst0 σ p.
  Proof.
    intros p m npat σ hp hm hσ.
    induction hp as [n hn | ind n ui args pa ih]
    in m, hm, σ, hσ |- * using pattern_all_rect.
    - cbn. replace (n - 0) with n by lia.
      apply subs_complete_spec in hσ as [eσ hσ].
      cbn in hm. rewrite lin_set_eq in hm.
      destruct nth_error as [[]|] eqn:e1. 1,3: discriminate.
      apply some_inj in hm.
      apply (f_equal (fun l => #|l|)) in hm as e2.
      rewrite app_length in e2. cbn in e2.
      rewrite firstn_length in e2.
      rewrite skipn_length in e2.
      { rewrite linear_mask_init_length. lia. }
      rewrite linear_mask_init_length in e2.
      match type of e2 with
      | ?n = _ => replace n with npat in e2 by lia
      end.
      destruct (nth_error (id_mask 0 m) n) as [[]|] eqn:e.
      3:{
        apply nth_error_None in e.
        rewrite id_mask_length in e.
        lia.
      }
      2:{
        exfalso. subst. rewrite id_mask_app in e.
        cbn in e. rewrite nth_error_app2 in e.
        { rewrite id_mask_length. rewrite firstn_length. lia. }
        rewrite id_mask_length in e. rewrite firstn_length in e.
        rewrite linear_mask_init_length in e.
        replace (n - min n npat) with 0 in e by lia.
        cbn in e. discriminate.
      }
      apply hσ in e as e3. rewrite e3.
      rewrite lift0_id.
      clear - e.
      replace n with (0 + n) by lia.
      revert e. generalize 0. intros i e.
      induction m as [| [] m ih] in i, n, t, e |- *.
      + cbn in e. destruct n. all: discriminate.
      + cbn in e. destruct n.
        * cbn in e. inversion e. f_equal. lia.
        * cbn in e. apply ih in e. subst.
          f_equal. lia.
      + cbn in e. destruct n.
        * cbn in e. discriminate.
        * cbn in e. apply ih in e. subst.
          f_equal. lia.
    - rewrite subst_mkApps. cbn. f_equal.
      eapply All_prod in pa. 2: exact ih.
      clear ih.
      induction pa as [| p l [ihp hp] hl ih]
      in σ, hσ, m, hm |- * using All_rev_rect.
      1: reflexivity.
      rewrite map_app. cbn.
      rewrite <- mkApps_nested in hm. cbn in hm.
      destruct pattern_mask eqn:e1. 2: discriminate.
      destruct (pattern_mask _ p) eqn:e2. 2: discriminate.
      specialize ih with (1 := eq_refl).
      specialize ihp with (1 := eq_refl).
      apply lin_merge_id_mask with (i := 0) in hm as sm.
      eapply subs_merge_complete in sm. 2: eassumption.
      destruct sm as [? ?].
      f_equal.
      + apply ih. assumption.
      + f_equal. apply ihp. assumption.
  Qed.

  (* TODO MOVE *)
  Lemma map_list_init :
    forall A B (f : A -> B) a n,
      map f (list_init a n) = list_init (f a) n.
  Proof.
    intros A B f a n.
    induction n.
    - reflexivity.
    - cbn. f_equal. apply IHn.
  Qed.

  (* TODO MOVE? *)
  Lemma lin_merge_length :
    forall m1 m2 m,
      lin_merge m1 m2 = Some m ->
      #|m| = #|m1| /\ #|m| = #|m2|.
  Proof.
    intros m1 m2 m hm.
    induction m1 as [| [] m1 ih] in m2, m, hm |- *.
    - destruct m2. 2: discriminate.
      cbn in hm. apply some_inj in hm. subst.
      auto.
    - destruct m2 as [| [] m2]. 1,2: discriminate.
      cbn in hm. destruct lin_merge eqn:e. 2: discriminate.
      apply some_inj in hm. subst.
      apply ih in e. cbn. intuition eauto.
    - cbn in hm. destruct m2. 1: discriminate.
      destruct lin_merge eqn:e. 2: discriminate.
      apply some_inj in hm. subst.
      apply ih in e. cbn. intuition eauto.
  Qed.

  (* TODO MOVE? *)
  Lemma pattern_mask_length :
    forall npat p m,
      pattern_mask npat p = Some m ->
      #|m| = npat.
  Proof.
    intros npat p m hm.
    induction p in m, hm |- *.
    all: try discriminate.
    - cbn in hm. induction n in npat, m, hm |- *.
      + cbn in hm. destruct linear_mask_init as [| []] eqn:e.
        1,2: discriminate.
        apply some_inj in hm. subst. cbn.
        apply (f_equal (fun l => #|l|)) in e. cbn in e.
        rewrite linear_mask_init_length in e. auto.
      + cbn in hm. destruct linear_mask_init eqn:e. 1: discriminate.
        destruct lin_set eqn:e1. 2: discriminate.
        apply some_inj in hm. subst. cbn.
        destruct npat. 1: discriminate.
        cbn in e. inversion e. subst. clear e.
        apply IHn in e1. auto.
    - cbn in hm.
      destruct pattern_mask eqn:e1. 2: discriminate.
      destruct (pattern_mask _ p2) eqn:e2. 2: discriminate.
      specialize IHp1 with (1 := eq_refl).
      specialize IHp2 with (1 := eq_refl).
      apply lin_merge_length in hm. lia.
    - cbn in hm. apply some_inj in hm. subst.
      apply linear_mask_init_length.
  Qed.

  (* TODO MOVE *)
  Lemma all_nth_error_All2_mask_subst :
    forall P m σ θ,
      (forall n,
        nth_error m n = Some true ->
        ∑ t u,
          nth_error σ n = Some t ×
          nth_error θ n = Some (Some u) ×
          P t u
      ) ->
      (forall n,
        nth_error m n = Some false ->
        nth_error θ n = Some None
      ) ->
      #|m| = #|σ| ->
      #|m| = #|θ| ->
      All2_mask_subst P m σ θ.
  Proof.
    intros P m σ θ ht hf lσ lθ.
    induction m as [| [] m ih] in σ, θ, ht, hf, lσ, lθ |- *.
    - destruct σ. 2: discriminate.
      destruct θ. 2: discriminate.
      constructor.
    - cbn in *.
      destruct σ. 1: discriminate.
      destruct θ as [| [] θ]. 1: discriminate.
      2:{
        specialize (ht 0). cbn in ht.
        forward ht by auto.
        destruct ht as [? [? [? [? ?]]]]. discriminate.
      }
      constructor.
      + specialize (ht 0). cbn in ht.
        forward ht by auto.
        destruct ht as [u [v [e1 [e2 ?]]]].
        apply some_inj in e1. subst.
        apply some_inj in e2. apply some_inj in e2. subst.
        assumption.
      + apply ih. all: auto.
        * intros n e.
          specialize (ht (S n)). cbn in ht.
          forward ht by auto. assumption.
        * intros n e.
          specialize (hf (S n)). cbn in hf.
          forward hf by auto. assumption.
    - cbn in *.
      destruct σ. 1: discriminate.
      destruct θ as [| [] θ]. 1: discriminate.
      1:{
        specialize (hf 0). cbn in hf.
        forward hf by auto.
        discriminate.
      }
      constructor.
      apply ih. all: auto.
      + intros n e.
        specialize (ht (S n)). cbn in ht.
        forward ht by auto. assumption.
      + intros n e.
        specialize (hf (S n)). cbn in hf.
        forward hf by auto. assumption.
  Qed.

  Lemma nth_error_id_mask :
    forall i m n,
      nth_error m n = Some true ->
      nth_error (id_mask i m) n = Some (Some (tRel (i + n))).
  Proof.
    intros i m n h.
    induction m as [| [] m ih] in i, n, h |- *.
    - destruct n. all: discriminate.
    - cbn. destruct n.
      + cbn. f_equal. f_equal. f_equal. lia.
      + cbn in *. rewrite -> ih by auto.
        f_equal. f_equal. f_equal. lia.
    - cbn. destruct n.
      + cbn in *. discriminate.
      + cbn in *. rewrite -> ih by auto.
        f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma nth_error_false_id_mask :
    forall i m n,
      nth_error m n = Some false ->
      nth_error (id_mask i m) n = Some None.
  Proof.
    intros i m n h.
    induction m as [| [] m ih] in i, n, h |- *.
    - destruct n. all: discriminate.
    - cbn. destruct n.
      + cbn in *. discriminate.
      + cbn in *. rewrite -> ih by auto. reflexivity.
    - cbn. destruct n.
      + cbn. reflexivity.
      + cbn in *. rewrite -> ih by auto. reflexivity.
  Qed.

  Fixpoint weaks i Γ :=
    match Γ with
    | {| decl_body := Some t ; decl_type := A |} :: Γ =>
      subst0 (weaks (S i) Γ) t :: weaks (S i) Γ
    | {| decl_body := None ; decl_type := A |} :: Γ =>
      tRel i :: weaks (S i) Γ
    | [] => []
    end.

  (** The purpose of this lemma is to convince myself this is the right
    definition.
  *)
  Lemma subslet_weaks :
    forall Σ Γ Δ,
      subslet Σ (Γ ,,, Δ) (weaks #|Δ| Γ) Γ.
  Proof.
    intros Σ Γ Δ.
    induction Γ as [| [na [t|] A] Γ ih] in Δ |- *.
    - cbn. constructor.
    - cbn. constructor.
      + match goal with
        | |- subslet _ ((?d :: _) ,,, _) _ _ =>
          specialize (ih (Δ ++ [d]))
        end.
        rewrite app_length in ih. cbn in ih.
        unfold ",,," in *. rewrite <- app_assoc in ih. cbn in ih.
        replace (#|Δ| + 1) with (S #|Δ|) in ih by lia.
        assumption.
      + admit.
    - cbn. constructor.
      + match goal with
        | |- subslet _ ((?d :: _) ,,, _) _ _ =>
          specialize (ih (Δ ++ [d]))
        end.
        rewrite app_length in ih. cbn in ih.
        unfold ",,," in *. rewrite <- app_assoc in ih. cbn in ih.
        replace (#|Δ| + 1) with (S #|Δ|) in ih by lia.
        assumption.
      + admit.
  Abort.

  Lemma untyped_subslet_weaks :
    forall Γ Δ,
      untyped_subslet (Γ ,,, Δ) (weaks #|Δ| Γ) Γ.
  Proof.
    intros Γ Δ.
    induction Γ as [| [na [t|] A] Γ ih] in Δ |- *.
    - cbn. constructor.
    - cbn. constructor.
      match goal with
      | |- untyped_subslet ((?d :: _) ,,, _) _ _ =>
        specialize (ih (Δ ++ [d]))
      end.
      rewrite app_length in ih. cbn in ih.
      unfold ",,," in *. rewrite <- app_assoc in ih. cbn in ih.
      replace (#|Δ| + 1) with (S #|Δ|) in ih by lia.
      assumption.
    - cbn. constructor.
      match goal with
      | |- untyped_subslet ((?d :: _) ,,, _) _ _ =>
        specialize (ih (Δ ++ [d]))
      end.
      rewrite app_length in ih. cbn in ih.
      unfold ",,," in *. rewrite <- app_assoc in ih. cbn in ih.
      replace (#|Δ| + 1) with (S #|Δ|) in ih by lia.
      assumption.
  Qed.

  Definition idsubst Γ :=
    weaks 0 Γ.

  Lemma untyped_subslet_idsubst :
    forall Γ,
      untyped_subslet Γ (idsubst Γ) Γ.
  Proof.
    intro Γ.
    apply untyped_subslet_weaks with (Δ := []).
  Qed.

  (* TODO Maybe useless? *)
  Inductive masks : list bool -> partial_subst -> Type :=
  | masks_nil : masks [] []
  | masks_true :
      forall m σ t,
        masks m σ ->
        masks (true :: m) (Some t :: σ)
  | masks_false :
      forall m σ,
        masks m σ ->
        masks (false :: m) (None :: σ).

  (* Altered version of on_some *)
  Definition on_Some {A} (P : A -> Type) o :=
    match o with
    | Some x => P x
    | None => unit
    end.

  (* Pattern partial substitution *)
  (* TODO Maybe just inline *)
  Definition pattern_partial_subst npat (σ : partial_subst) :=
    All (on_Some (pattern npat)) σ.

  (** Linear mask for a partial substitution *)
  Fixpoint partial_subst_mask npat σ : option (list bool) :=
    match σ with
    | Some p :: σ =>
      mp <- pattern_mask npat p ;;
      mσ <- partial_subst_mask npat σ ;;
      lin_merge mp mσ
    | None :: σ => partial_subst_mask npat σ
    | [] => ret (linear_mask_init npat)
    end.

  (* TODO Not really interesting, for assumptions contexts... *)
  (* Inductive untyped_subs_mask Γ :
    list bool -> partial_subst -> context -> Type :=
  | untyped_subs_true :
      forall Δ σ m na t A,
        untyped_subs_mask Γ (true :: m) (Some t :: σ) (Δ ,, vass na A) *)

  (* It isn't really well defined! We should let go of lets. *)
  (* Inductive untyped_subslet_mask Γ :
    list bool -> partial_subst -> context -> Type :=
  | untyped_mask_emptyslet : untyped_subslet_mask Γ [] [] []
  | untyped_cons_let_ass_true :
      forall m σ Δ na t A,
        untyped_subslet_mask Γ m σ Δ ->
        untyped_subslet_mask Γ (true :: m) (Some t :: σ) (Δ ,, vass na A)
  | untyped_cons_let_def_true :
      forall m σ Δ na t A,
        untyped_subslet_mask Γ m σ Δ ->
        untyped_subslet_mask
          Γ (true :: m) (Some (subst0 σ t) :: σ) (Δ ,, vdef na t A)
  | untyped_cons_false :
      forall m σ Δ d,
        untyped_subslet_mask Γ m σ Δ ->
        untyped_subslet_mask Γ (false :: m) (None :: σ) (Δ ,, d). *)

  (* In case of assumptions contexts, it's just a question of having
    the right length.
    TODO Enfore assumptions contexts for pattern variables.
  *)

  Lemma pattern_unify_subst :
    forall σ θ p1 p2 m1 m2 Γ Δ1 Δ2,
      let npat1 := #|Δ1| in
      let npat2 := #|Δ2| in
      pattern npat1 p1 ->
      pattern npat2 p2 ->
      pattern_mask npat1 p1 = Some m1 ->
      pattern_mask npat2 p2 = Some m2 ->
      untyped_subslet Γ σ Δ1 ->
      untyped_subslet Γ θ Δ2 ->
      subst0 σ p1 = subst0 θ p2 ->
      ∑ φ ψ ξ,
        (* untyped_subslet_mask (Δ1 ,,, Δ2) m1 φ Δ1 ×
        untyped_subslet_mask (Δ1 ,,, Δ2) m2 ψ Δ2 × *)
        All2_mask_subst eq m1 σ (map (option_map (subst0 ξ)) φ) ×
        All2_mask_subst eq m2 θ (map (option_map (subst0 ξ)) ψ) ×
        untyped_subslet Γ ξ Ξ ×
        forall φ' ψ',
          subs_complete φ φ' ->
          subs_complete ψ ψ' ->
          (* untyped_subslet Ξ φ' Δ1 ->
          untyped_subslet Ξ ψ' Δ2 -> *)
          subst0 φ' p1 = subst0 ψ' p2.
  Proof.
    intros σ θ p1 p2 m1 m2 Γ Δ1 Δ2 npat1 npat2 hp1 hp2 hm1 hm2 uσ uθ e.
    induction hp1
    as [n hn | ind n ui args pa ih]
    in p2, hp2, m1, hm1, m2, hm2, σ, uσ, θ, uθ, e |- *
    using pattern_all_rect.
    - cbn in hm1. cbn in e.
      replace (n - 0) with n in e by lia.
      destruct nth_error eqn:e1.
      2:{
        apply nth_error_None in e1.
        apply untyped_subslet_length in uσ.
        exfalso. lia.
      }
      rewrite lift0_id in e. subst.
      case_eq (subs_init npat1 n p2).
      2:{
        intros e2. exfalso.
        unfold subs_init, subs_add in e2.
        apply untyped_subslet_length in uσ.
        destruct (nth_error (subs_empty _) _) as [[]|] eqn:e3.
        - clearbody npat1. clear - e3.
          induction npat1 in t, n, e3 |- *.
          + cbn in e3. destruct n. all: discriminate.
          + cbn in e3. destruct n.
            * cbn in e3. discriminate.
            * cbn in e3. eapply IHnpat1. eassumption.
        - discriminate.
        - apply nth_error_None in e3.
          rewrite subs_empty_length in e3.
          lia.
      }
      intros φ e2.
      exists φ, (id_mask 0 m2), Δ2, θ.
      repeat lazymatch goal with
      | |- _ × _ => split
      | |- forall _, _ => intros φ' ψ' hφ hψ (* uφ uψ *)
      end.
      + apply untyped_subslet_length in uσ.
        assert (e : #|σ| = npat1) by auto.
        clearbody npat1. clear - hm1 e1 e2 e.
        induction npat1 in φ, n, σ, m1, hm1, e1, e2, e |- *.
        1:{ cbn in hm1. destruct n. all: discriminate. }
        cbn in hm1. destruct n.
        * cbn in hm1. apply some_inj in hm1. subst.
          destruct σ. 1: discriminate.
          cbn in e1. apply some_inj in e1. subst.
          cbn in e2. apply some_inj in e2. subst.
          cbn.
          constructor. 1: reflexivity.
          unfold skipn. rewrite map_list_init. cbn.
          apply All2_mask_subst_linear_mask_init.
          cbn in e. lia.
        * cbn in hm1. destruct lin_set eqn:e3. 2: discriminate.
          apply some_inj in hm1. subst.
          destruct σ. 1: discriminate.
          cbn in e1. cbn in e.
          unfold subs_init, subs_add in e2.
          cbn in e2.
          destruct (nth_error (list_init _ _) _) as [[]|] eqn:e4.
          1,3: discriminate.
          apply some_inj in e2. subst. cbn.
          constructor.
          eapply IHnpat1. all: eauto.
          unfold subs_init, subs_add. rewrite e4.
          reflexivity.
      + apply all_nth_error_All2_mask_subst.
        * intros i e.
          destruct (nth_error θ i) eqn:e3.
          2:{
            apply nth_error_Some_length in e.
            apply nth_error_None in e3.
            apply untyped_subslet_length in uθ.
            apply pattern_mask_length in hm2.
            exfalso. lia.
          }
          rewrite nth_error_map.
          apply nth_error_id_mask with (i := 0) in e as e4. cbn in e4.
          rewrite e4. cbn - [subst]. cbn.
          replace (i - 0) with i by lia.
          rewrite e3. rewrite lift0_id.
          eexists _, _.
          intuition reflexivity.
        * intros i e.
          rewrite nth_error_map.
          apply nth_error_false_id_mask with (i := 0) in e as e3.
          rewrite e3. cbn. reflexivity.
        * apply untyped_subslet_length in uθ.
          apply pattern_mask_length in hm2.
          lia.
        * rewrite map_length. rewrite id_mask_length. reflexivity.
      + assumption.
      + cbn. replace (n - 0) with n by lia.
        apply subs_complete_spec in hφ as [lφ hφ].
        apply subs_init_nth_error in e2 as e3.
        apply hφ in e3. rewrite e3. rewrite lift0_id.
        eapply id_mask_subst. all: eauto.
    - rewrite subst_mkApps in e. cbn in e.
      destruct hp2 as [i hi | ind' n' ui' args' pa'].
      + (* Symmetric case of the other *)
        admit.
      + rewrite subst_mkApps in e. cbn in e.
        apply (f_equal decompose_app) in e.
        rewrite -> 2!decompose_app_mkApps in e by auto.
        symmetry in e. inversion e. subst. clear e.
        match goal with
        | h : map _ _ = map _ _ |- _ => rename h into e
        end.
        symmetry in e.
        eapply All_prod in ih. 2: exact pa.
        clear pa.
        induction ih
        as [| p l [hp ihp] hl ih]
        in σ, θ, args', pa', m1, hm1, m2, hm2, uσ, uθ, e |- *
        using All_rev_rect.
        * destruct args'. 2: discriminate.
          cbn in *.
          apply some_inj in hm1.
          apply some_inj in hm2. subst.
          exists (subs_empty npat1), (subs_empty npat2), Γ, (idsubst Γ).
          repeat lazymatch goal with
          | |- _ × _ => split
          | |- forall _, _ => intros φ' ψ' hφ hψ (* uφ uψ *)
          end.
          -- unfold subs_empty. rewrite map_list_init. cbn.
             eapply All2_mask_subst_linear_mask_init.
             apply untyped_subslet_length in uσ. auto.
          -- unfold subs_empty. rewrite map_list_init. cbn.
             eapply All2_mask_subst_linear_mask_init.
             apply untyped_subslet_length in uθ. auto.
          -- apply untyped_subslet_idsubst.
          -- reflexivity.
        * destruct args' as [| p' l' _] using list_rect_rev.
          1:{
            apply (f_equal (fun l => #|l|)) in e. cbn in e.
            rewrite map_length in e. rewrite app_length in e.
            cbn in e. exfalso. lia.
          }
          rewrite 2!map_app in e. cbn in e.
          apply (f_equal rev) in e. rewrite 2!rev_app in e. cbn in e.
          inversion e. clear e.
          rename H0 into ep, H1 into el.
          apply (f_equal rev) in el. rewrite 2!rev_invol in el.
          rewrite <- mkApps_nested in hm1. cbn in hm1.
          destruct pattern_mask eqn:pm1. 2: discriminate.
          destruct (pattern_mask _ p) eqn:pmp. 2: discriminate.
          rewrite <- mkApps_nested in hm2. cbn in hm2.
          destruct (pattern_mask npat2 _) eqn:pm2. 2: discriminate.
          destruct (pattern_mask _ p') eqn:pmp'. 2: discriminate.
          apply All_app in pa' as [pl' pp'].
          inversion pp'. subst. clear pp'.
          specialize ihp with (2 := eq_refl) (3 := pmp') (4 := uσ) (5 := uθ).
          forward ihp by auto. forward ihp by auto.
          destruct ihp as [φ1 [ψ1 [Ξ1 [ξ1 [eφ1 [eψ1 [uξ1 h1]]]]]]].
          specialize ih with (2 := eq_refl) (3 := pm2) (4 := uσ) (5 := uθ).
          forward ih by auto. forward ih by auto.
          destruct ih as [φ2 [ψ2 [Ξ2 [ξ2 [eφ2 [eψ2 [uξ2 h2]]]]]]].
          eapply All2_mask_subst_lin_merge in hm1 as me. 2,3: eauto.
          destruct me as [φ [mφ eφ]].
          eapply All2_mask_subst_lin_merge in hm2 as me. 2,3: eauto.
          destruct me as [ψ [mψ eψ]].
          (* PROBLEM 1:
            We don't have the right φ and ψ they are already "mapped".
            Maybe uses masks or some fancier All2_mask_subst_lin_merge
            to accont for the map?
            Or have some subs_merge_map?
          *)
          (* PROBLEM 2:
            What do we do with ξ? And even worse with Ξ1 and Ξ2, if they are
            different it seems doomed.
          *)
          (* exists φ, ψ. *)
  Abort.

  Lemma elim_unify_subst :
    forall σ θ npat e1 e2 m1 m2,
      elim_pattern npat e1 ->
      elim_pattern npat e2 ->
      elim_mask npat e1 = Some m1 ->
      elim_mask npat e2 = Some m2 ->
      subst_elim σ 0 e1 = subst_elim θ 0 e2 ->
      ∑ φ ψ,
        All_mask_subst (pattern npat) m1 φ ×
        All_mask_subst (pattern npat) m2 ψ ×
        forall φ' ψ',
          subs_complete φ φ' ->
          subs_complete ψ ψ' ->
          subst_elim φ' 0 e1 = subst_elim ψ' 0 e2.
  Proof.
    intros σ θ npat e1 e2 m1 m2 he1 he2 hm1 hm2 e.
    induction he1 in m1, hm1, m2, hm2, θ, e2, he2, e |- *.
    - cbn in e. destruct he2. all: try discriminate.
      cbn in e. inversion e as [h]. clear e.
      (* Now we have to deal with patterns *)
  Abort.

  Lemma lhs_unify_subst :
    forall Σ k decl ui r r' σ θ m Γ,
      wf Σ ->
      is_rewrite_rule Σ k decl r ->
      is_rewrite_rule Σ k decl r' ->
      let ss := symbols_subst k 0 ui #|decl.(symbols)| in
      untyped_subslet Γ σ (subst_context ss 0 r.(pat_context)) ->
      untyped_subslet Γ θ (subst_context ss 0 r'.(pat_context)) ->
      r.(head) = r'.(head) ->
      m <= #|r.(elims)| ->
      let npat := #|r.(pat_context)| in
      let prelhs1 := mkElims (tRel (npat + r.(head))) (firstn m r.(elims)) in
      let prelhs2 := subst ss #|σ| prelhs1 in
      let lhs' := subst ss #|θ| (lhs r') in
      subst0 σ prelhs2 = subst0 θ lhs' ->
      ∑ mask φ ψ,
        linear_mask npat (firstn m r.(elims)) = Some mask ×
        All_mask_subst (pattern npat) mask φ ×
        All (pattern npat) ψ ×
        forall φ',
          subs_complete φ φ' ->
          subst0 φ' prelhs2 = subst0 ψ lhs'.
          (* + decomposition of substitutions *)
          (* + intermediary contexts (maybe the same one?) and untyped_subslet *)
  Proof.
    intros Σ k decl ui r r' σ θ m Γ hΣ hr hr' ss uσ uθ eh hm npat prelhs1
      prelhs2 lhs' e.
    subst prelhs1 prelhs2 lhs'.
    unfold lhs in e. rewrite <- eh in e.
    rewrite 4!mkElims_subst in e.
    apply untyped_subslet_length in uσ as lσ.
    rewrite subst_context_length in lσ.
    apply untyped_subslet_length in uθ as lθ.
    rewrite subst_context_length in lθ.
    cbn in e.
    destruct leb eqn:e1.
    2:{ exfalso. apply leb_complete_conv in e1. lia. }
    destruct (leb #|θ| _) eqn:e2.
    2:{ exfalso. apply leb_complete_conv in e2. lia. }
    replace (npat + head r - #|σ|) with r.(head) in e by lia.
    replace (#|pat_context r'| + head r - #|θ|) with r.(head) in e by lia.
    destruct nth_error eqn:e3.
    2:{
      apply is_rewrite_rule_head in hr. 2: auto.
      apply nth_error_None in e3. subst ss.
      rewrite symbols_subst_length in e3. exfalso. lia.
    }
    apply symbols_subst_nth_error in e3. subst. cbn in e.
    apply (f_equal decompose_elims) in e.
    rewrite 2!mkElims_decompose_elims in e. cbn in e.
    inversion e as [h]. clear e.
    (* Now we have to conclude on unification of eliminations.
      Since they have the same length we can do it pointwise.
    *)
  Abort.

End ParallelSubstitution.

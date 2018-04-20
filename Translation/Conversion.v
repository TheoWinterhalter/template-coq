From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation
Require Import util SAst SInduction Equality SLiftSubst SCommon.

Open Scope s_scope.

(*! Reduction. *)

(* TODO in branch case with Apps *)
(* Definition iota_red npar c args brs := *)
(*   (mkApps (snd (List.nth c brs (0, tRel 0))) (List.skipn npar args)). *)

Inductive red1 (Σ : sglobal_declarations) : sterm -> sterm -> Prop :=
(*! Computation *)

(** β *)
| red_beta n A B A' B' t u :
    red1 Σ (sApp (sLambda n A B t) A' B' u) (t{ 0 := u })

(** Case TODO *)
(* | red_iota ind pars c args p brs : *)
(*     red1 Σ Γ (sCase (ind, pars) p (Apps (sConstruct ind c) _ _ args) brs) *)
(*          (iota_red pars c args brs) *)

(** J-Refl *)
| red_JRefl A u P w v A' u' :
    red1 Σ (sJ A u P w v (sRefl A' u')) w

(** Transport of Refl *)
| red_TransportRefl A A' A'' T t :
    red1 Σ (sTransport A A' (sRefl T A'') t) t

(*! Subterm reduction *)

(** Lambda *)
| abs_red_dom na A A' B t :
    red1 Σ A A' ->
    red1 Σ (sLambda na A B t) (sLambda na A' B t)

| abs_red_codom na A B B' t :
    red1 Σ B B' ->
    red1 Σ (sLambda na A B t) (sLambda na A B' t)

| abs_red_body na A B t t' :
    red1 Σ t t' ->
    red1 Σ (sLambda na A B t) (sLambda na A B t')

(** Case *)
| case_red_pred ind p p' c brs :
    red1 Σ p p' ->
    red1 Σ (sCase ind p c brs) (sCase ind p' c brs)

| case_red_discr ind p c c' brs :
    red1 Σ c c' ->
    red1 Σ (sCase ind p c brs) (sCase ind p c' brs)

| case_red_brs ind p c brs brs' :
    redbrs1 Σ brs brs' ->
    red1 Σ (sCase ind p c brs) (sCase ind p c brs')

(** App *)
| app_red_fun u u' A B v :
    red1 Σ u u' ->
    red1 Σ (sApp u A B v) (sApp u' A B v)

| app_red_dom u A A' B v :
    red1 Σ A A' ->
    red1 Σ (sApp u A B v) (sApp u A' B v)

| app_red_codom u A B B' v :
    red1 Σ B B' ->
    red1 Σ (sApp u A B v) (sApp u A B' v)

| app_red_arg u A B v v' :
    red1 Σ v v' ->
    red1 Σ (sApp u A B v) (sApp u A B v')

(** Prod *)
| prod_red_l na na' A A' B :
    red1 Σ A A' ->
    red1 Σ (sProd na A B) (sProd na' A' B)

| prod_red_r na na' A B B' :
    red1 Σ B B' ->
    red1 Σ (sProd na A B) (sProd na' A B')

(** Eq *)
| eq_red_ty A A' u v :
    red1 Σ A A' ->
    red1 Σ (sEq A u v) (sEq A' u v)

| eq_red_l A u u' v :
    red1 Σ u u' ->
    red1 Σ (sEq A u v) (sEq A u' v)

| eq_red_r A u v v' :
    red1 Σ v v' ->
    red1 Σ (sEq A u v) (sEq A u v')

(** Refl *)
| refl_red_ty A A' u :
    red1 Σ A A' ->
    red1 Σ (sRefl A u) (sRefl A' u)

| refl_red_tm A u u' :
    red1 Σ u u' ->
    red1 Σ (sRefl A u) (sRefl A u')

(** J *)
| j_red_ty A A' u v P p w :
    red1 Σ A A' ->
    red1 Σ (sJ A u P w v p) (sJ A' u P w v p)

| j_red_l A u u' v P p w :
    red1 Σ u u' ->
    red1 Σ (sJ A u P w v p) (sJ A u' P w v p)

| j_red_pred A u v P P' p w :
    red1 Σ P P' ->
    red1 Σ (sJ A u P w v p) (sJ A u P' w v p)

| j_red_prf A u v P p w w' :
    red1 Σ w w' ->
    red1 Σ (sJ A u P w v p) (sJ A u P w' v p)

| j_red_r A u v v' P p w :
    red1 Σ v v' ->
    red1 Σ (sJ A u P w v p) (sJ A u P w v' p)

| j_red_eq A u v P p p' w :
    red1 Σ p p' ->
    red1 Σ (sJ A u P w v p) (sJ A u P w v p')

(** Transport *)
| transport_red_ty_l A A' B p t :
    red1 Σ A A' ->
    red1 Σ (sTransport A B p t) (sTransport A' B p t)

| transport_red_ty_r A B B' p t :
    red1 Σ B B' ->
    red1 Σ (sTransport A B p t) (sTransport A B' p t)

| transport_red_eq A B p p' t :
    red1 Σ p p' ->
    red1 Σ (sTransport A B p t) (sTransport A B p' t)

| transport_red_tm A B p t t' :
    red1 Σ t t' ->
    red1 Σ (sTransport A B p t) (sTransport A B p t')

(** Heq *)
| heq_red_ty_l A A' a B b :
    red1 Σ A A' ->
    red1 Σ (sHeq A a B b) (sHeq A' a B b)

| heq_red_tm_l A a a' B b :
    red1 Σ a a' ->
    red1 Σ (sHeq A a B b) (sHeq A a' B b)

| heq_red_ty_r A a B B' b :
    red1 Σ B B' ->
    red1 Σ (sHeq A a B b) (sHeq A a B' b)

| heq_red_tm_r A a B b b' :
    red1 Σ b b' ->
    red1 Σ (sHeq A a B b) (sHeq A a B b')

(** HeqToEq *)
| heqtoeq_red p p' :
    red1 Σ p p' ->
    red1 Σ (sHeqToEq p) (sHeqToEq p')

(** HeqRefl *)
| heqrefl_red_ty A A' a :
    red1 Σ A A' ->
    red1 Σ (sHeqRefl A a) (sHeqRefl A' a)

| heqrefl_red_tm A a a' :
    red1 Σ a a' ->
    red1 Σ (sHeqRefl A a) (sHeqRefl A a')

(** HeqSym *)
| heqsym_red p p' :
    red1 Σ p p' ->
    red1 Σ (sHeqSym p) (sHeqSym p')

(** HeqTrans *)
| heqtrans_red_l p p' q :
    red1 Σ p p' ->
    red1 Σ (sHeqTrans p q) (sHeqTrans p' q)

| heqtrans_red_r p q q' :
    red1 Σ q q' ->
    red1 Σ (sHeqTrans p q) (sHeqTrans p q')

(** HeqTransport *)
| heqtransport_red_eq p p' t :
    red1 Σ p p' ->
    red1 Σ (sHeqTransport p t) (sHeqTransport p' t)

| heqtransport_red_tm p t t' :
    red1 Σ t t' ->
    red1 Σ (sHeqTransport p t) (sHeqTransport p t')

(** CongProd *)
| congprod_red_ty_l B1 B1' B2 pA pB :
    red1 Σ B1 B1' ->
    red1 Σ (sCongProd B1 B2 pA pB) (sCongProd B1' B2 pA pB)

| congprod_red_ty_r B1 B2 B2' pA pB :
    red1 Σ B2 B2' ->
    red1 Σ (sCongProd B1 B2 pA pB) (sCongProd B1 B2' pA pB)

| congprod_red_tm_l B1 B2 pA pA' pB :
    red1 Σ pA pA' ->
    red1 Σ (sCongProd B1 B2 pA pB) (sCongProd B1 B2 pA' pB)

| congprod_red_tm_r B1 B2 pA pB pB' :
    red1 Σ pB pB' ->
    red1 Σ (sCongProd B1 B2 pA pB) (sCongProd B1 B2 pA pB')

(** CongLambda *)
| conglambda_red_ty_l B1 B2 t1 t2 pA pB pt B1' :
    red1 Σ B1 B1' ->
    red1 Σ (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1' B2 t1 t2 pA pB pt)

| conglambda_red_ty_r B1 B2 t1 t2 pA pB pt B2' :
    red1 Σ B2 B2' ->
    red1 Σ (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2' t1 t2 pA pB pt)

| conglambda_red_tm_l B1 B2 t1 t2 pA pB pt t1' :
    red1 Σ t1 t1' ->
    red1 Σ (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1' t2 pA pB pt)

| conglambda_red_tm_r B1 B2 t1 t2 pA pB pt t2' :
    red1 Σ t2 t2' ->
    red1 Σ (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1 t2' pA pB pt)

| conglambda_red_eq_dom B1 B2 t1 t2 pA pB pt pA' :
    red1 Σ pA pA' ->
    red1 Σ (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1 t2 pA' pB pt)

| conglambda_red_eq_codom B1 B2 t1 t2 pA pB pt pB' :
    red1 Σ pB pB' ->
    red1 Σ (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1 t2 pA pB' pt)

| conglambda_red_eq_tm B1 B2 t1 t2 pA pB pt pt' :
    red1 Σ pt pt' ->
    red1 Σ (sCongLambda B1 B2 t1 t2 pA pB pt)
             (sCongLambda B1 B2 t1 t2 pA pB pt')

(** CongApp *)
| congapp_red_ty_l B1 B2 pu pA pB pv B1' :
    red1 Σ B1 B1' ->
    red1 Σ (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1' B2 pu pA pB pv)

| congapp_red_ty_r B1 B2 pu pA pB pv B2' :
    red1 Σ B2 B2' ->
    red1 Σ (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2' pu pA pB pv)

| congapp_red_eq_fun B1 B2 pu pA pB pv pu' :
    red1 Σ pu pu' ->
    red1 Σ (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2 pu' pA pB pv)

| congapp_red_eq_dom B1 B2 pu pA pB pv pA' :
    red1 Σ pA pA' ->
    red1 Σ (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2 pu pA' pB pv)

| congapp_red_eq_codom B1 B2 pu pA pB pv pB' :
    red1 Σ pB pB' ->
    red1 Σ (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2 pu pA pB' pv)

| congapp_red_eq_arg B1 B2 pu pA pB pv pv' :
    red1 Σ pv pv' ->
    red1 Σ (sCongApp B1 B2 pu pA pB pv)
             (sCongApp B1 B2 pu pA pB pv')

(** CongEq *)
| congeq_red_eq_ty pA pu pv pA' :
    red1 Σ pA pA' ->
    red1 Σ (sCongEq pA pu pv) (sCongEq pA' pu pv)

| congeq_red_eq_tm_l pA pu pv pu' :
    red1 Σ pu pu' ->
    red1 Σ (sCongEq pA pu pv) (sCongEq pA pu' pv)

| congeq_red_eq_tm_r pA pu pv pv' :
    red1 Σ pv pv' ->
    red1 Σ (sCongEq pA pu pv) (sCongEq pA pu pv')

(* (** CongRefl *) *)
| congrefl_red_ty pA pu pA' :
    red1 Σ pA pA' ->
    red1 Σ (sCongRefl pA pu) (sCongRefl pA' pu)

| congrefl_red_tm pA pu pu' :
    red1 Σ pu pu' ->
    red1 Σ (sCongRefl pA pu) (sCongRefl pA pu')

(** EqToHeq *)
| eqtoheq_red p p' :
    red1 Σ p p' ->
    red1 Σ (sEqToHeq p) (sEqToHeq p')

(** HeqTypeEq *)
| heqtypeeq_red_ty_l A B p A' :
    red1 Σ A A' ->
    red1 Σ (sHeqTypeEq A B p) (sHeqTypeEq A' B p)

| heqtypeeq_red_ty_r A B p B' :
    red1 Σ B B' ->
    red1 Σ (sHeqTypeEq A B p) (sHeqTypeEq A B' p)

| heqtypeeq_red_prf A B p p' :
    red1 Σ p p' ->
    red1 Σ (sHeqTypeEq A B p) (sHeqTypeEq A B p')

(** Pack *)
| pack_red_l A1 A2 A1' :
    red1 Σ A1 A1' ->
    red1 Σ (sPack A1 A2) (sPack A1' A2)

| pack_red_r A1 A2 A2' :
    red1 Σ A2 A2' ->
    red1 Σ (sPack A1 A2) (sPack A1 A2')

(** ProjT1 *)
| projt1_red p p' :
    red1 Σ p p' ->
    red1 Σ (sProjT1 p) (sProjT1 p')

(** ProjT2 *)
| projt2_red p p' :
    red1 Σ p p' ->
    red1 Σ (sProjT2 p) (sProjT2 p')

(** ProjTe *)
| projte_red p p' :
    red1 Σ p p' ->
    red1 Σ (sProjTe p) (sProjTe p')

with redbrs1 (Σ : sglobal_declarations) :
       list (nat * sterm) -> list (nat * sterm) -> Prop :=
| redbrs1_hd n hd hd' tl :
    red1 Σ hd hd' ->
    redbrs1 Σ ((n, hd) :: tl) ((n, hd') :: tl)
| redbrs1_tl hd tl tl' :
    redbrs1 Σ tl tl' ->
    redbrs1 Σ (hd :: tl) (hd :: tl')
.

Derive Signature for red1.

Notation " Σ '|-i' t ▷ u " :=
  (red1 Σ t u) (at level 50, t, u at next level).

(* Reflexive and transitive closure of 1-step reduction. *)
Inductive red Σ t : sterm -> Prop :=
| refl_red : red Σ t t
| trans_red u v : red1 Σ t u -> red Σ u v -> red Σ t v.

Notation " Σ '|-i' t ▷⃰ u " :=
  (red Σ t u) (at level 50, t, u at next level).


Section nlred.

  (* We have to use this definition to trick Equations into not doing anything
   about this equality.
   *)
  Definition nleq u v := nl u = nl v.

  Ltac nlred :=
    match goal with
    | h : _ |-i ?t ▷ ?t', eq : nl ?t = _, ih : forall _, _ |-i ?t ▷ _ -> _ |- _ =>
      destruct (ih _ h _ eq) as [? [? ?]] ;
      eexists ; split ; [
        econstructor ; eassumption
      | unfold nleq ; cbn ; f_equal ; assumption
      ]
    end.

  Fact redbrs1_one :
    forall {Σ b1 b2},
      redbrs1 Σ b1 b2 ->
      exists n m t1 t2,
        (Σ |-i t1 ▷ t2) *
        (nth_error b1 n = Some (m, t1)) *
        (b2 = firstn n b1 ++ ((m, t2) :: skipn (S n) b1))%list.
  Proof.
    intros Σ b1 b2 h.
    induction h.
    - exists 0, n, hd, hd'. repeat split. assumption.
    - destruct IHh as (n & m & t1 & t2 & hh). destruct hh as [[? ?] ?].
      exists (S n), m, t1, t2. repeat split ; try assumption.
      rewrite pi2_0. reflexivity.
  Defined.

  Fact one_redbrs1 :
    forall {Σ b n m t1 t2},
      Σ |-i t1 ▷ t2 ->
      nth_error b n = Some (m, t1) ->
      redbrs1 Σ b (firstn n b ++ ((m, t2) :: skipn (S n) b))%list.
  Proof.
    intros Σ b.
    induction b ; intros n m t1 t2 hr hn.
    - destruct n ; cbn in hn ; discriminate hn.
    - destruct n.
      + cbn in hn. inversion hn. subst. clear hn.
        econstructor. assumption.
      + cbn in hn.
        change (firstn (S n) (a :: b)) with (a :: firstn n b).
        rewrite <- app_comm_cons.
        econstructor 2. eapply IHb ; eassumption.
  Defined.

  Lemma nl_red1 :
    forall {Σ t t' u},
      Σ |-i t ▷ u ->
      nleq t t' ->
      exists u', (Σ |-i t' ▷ u') /\ (nleq u u').
  Proof.
    intros Σ t t' u h. revert u h t'.
    induction t using sterm_rect_list.
    all: intros u h ; dependent destruction h ;
         intros tt eq ;
         destruct tt ; unfold nleq in eq ; simpl in eq ; try discriminate eq ;
         inversion eq ; try nlred.
    - destruct tt1 ; simpl nl in H0 ; try discriminate H0.
      inversion H0.
      eexists. split.
      + eapply red_beta.
      + apply nl_subst ; easy.
    - destruct tt6 ; simpl nl in H5 ; try discriminate H5.
      inversion H5.
      eexists. split.
      + eapply red_JRefl.
      + assumption.
    - destruct tt3 ; simpl nl in H2 ; try discriminate H2.
      inversion H2.
      eexists. split.
      + eapply red_TransportRefl.
      + assumption.
    - clear eq H1 ind IHt1 IHt2.
      destruct (redbrs1_one H) as [n [m [t1 [t2 [[rt hn] ?]]]]].
      subst. clear H.
      assert (hn' : exists t1', (nth_error brs n = Some (m, t1')) /\ (nl t1 = nl t1')).
      { clear - H4 hn. revert n brs0 H4 hn.
        induction brs ; intros n brs0 h hn.
        - destruct brs0 ; cbn in h ; try discriminate h.
          destruct n ; cbn in hn ; inversion hn.
        - destruct brs0 ; cbn in h ; try discriminate h.
          destruct n.
          + cbn in hn. inversion hn. subst. clear hn.
            destruct a as [m' t1'].
            inversion h. subst.
            exists t1'. split.
            * cbn. reflexivity.
            * assumption.
          + cbn in hn. inversion h.
            destruct (IHbrs _ _ H2 hn) as [t1' [? ?]].
            exists t1'. split.
            * cbn. assumption.
            * assumption.
      }
      destruct hn' as [t1' [hn' hnl]].
      destruct (sCaseBrsT_nth X hn _ rt _ hnl) as [t2' [hr2 hnl2]].
      eexists. split.
      + eapply case_red_brs. eapply one_redbrs1 ; eassumption.
      + unfold nleq. cbn. f_equal ; try assumption.
        rewrite !map_app. cbn. f_equal.
        * eapply map_firstn. assumption.
        * f_equal.
          -- unfold on_snd. cbn. f_equal. assumption.
          -- match goal with
             | |- map ?f ?l1 = map ?f ?l2 =>
               change (map f l1 = map f l2)
                 with (map f (skipn (S n) brs0) = map f (skipn (S n) brs))
             end.
             apply map_skipn. assumption.
    Unshelve. all: exact nAnon.
  Defined.

End nlred.

(*! Conversion *)

Reserved Notation " Σ '|-i' t = u " (at level 50, t, u at next level).

Inductive conv (Σ : sglobal_context) : sterm -> sterm -> Prop :=
| conv_eq t u : nl t = nl u -> Σ |-i t = u
| conv_red_l t u v : red1 (fst Σ) t v -> Σ |-i v = u -> Σ |-i t = u
| conv_red_r t u v : Σ |-i t = v -> red1 (fst Σ) u v -> Σ |-i t = u

where " Σ '|-i' t = u " := (@conv Σ t u) : i_scope.

Derive Signature for conv.

Open Scope i_scope.

Lemma conv_refl :
  forall Σ t , Σ |-i t = t.
Proof.
  intros Σ t.
  apply conv_eq. reflexivity.
Defined.

Lemma conv_sym :
  forall {Σ t u},
    Σ |-i t = u ->
    Σ |-i u = t.
Proof.
  intros Σ t u h.
  induction h.
  - apply conv_eq. symmetry. assumption.
  - eapply conv_red_r ; eassumption.
  - eapply conv_red_l ; eassumption.
Defined.

Lemma nl_conv :
  forall {Σ t u t' u'},
    Σ |-i t = u ->
    nl t = nl t' ->
    nl u = nl u' ->
    Σ |-i t' = u'.
Proof.
  intros Σ t u t' u' h. revert t' u'.
  induction h.
  - intros t' u' ht hu.
    apply conv_eq.
    transitivity (nl t).
    + symmetry. assumption.
    + transitivity (nl u) ; assumption.
  - intros t' u' ht hu.
    destruct (nl_red1 H ht) as [t'' [? ?]].
    eapply conv_red_l ; try eassumption.
    eapply IHh ; assumption.
  - intros t' u' ht hu.
    destruct (nl_red1 H hu) as [t'' [? ?]].
    eapply conv_red_r ; try eassumption.
    eapply IHh ; assumption.
Defined.

(* TODO? WARNING AXIOM *)
(* We dedice to have confluence of reduction as an axiom.
   The idea is that it then allows to derive transitivity of conversion
   without having to assume it, meaning we get a lot of properties
   like injectivity of constructors.
 *)

(* PARTIAL AXIOM Transitivity *)
Axiom conv_trans_AXIOM :
  forall {Σ t u v},
    Σ |-i t = u ->
    Σ |-i u = v ->
    Σ |-i t = v.

Lemma conv_trans :
  forall {Σ t u v},
    Σ |-i t = u ->
    Σ |-i u = v ->
    Σ |-i t = v.
Proof.
  intros Σ t u v h. revert v.
  induction h ; intros w h2.
  - symmetry in H.
    eapply nl_conv ; try eassumption.
    reflexivity.
  - specialize (IHh _ h2). eapply conv_red_l ; eassumption.
  - dependent induction h2.
    + eapply nl_conv ; [ .. | eassumption ].
      * eapply conv_red_r ; eassumption.
      * reflexivity.
    + eapply conv_trans_AXIOM.
      * eapply conv_red_r ; eassumption.
      * eapply conv_red_l ; eassumption.
    + eapply conv_trans_AXIOM.
      * eapply conv_red_r ; eassumption.
      * eapply conv_red_r ; eassumption.
Defined.

(*! Congruences for conversion *)

Ltac conv_rewrite_l h :=
  let h' := fresh "h" in
  match type of h with
  | _ |-i ?A = ?B =>
    lazymatch goal with
    | |- ?Σ |-i ?lctx = ?rctx =>
      lazymatch lctx with
      | context T [A] =>
        let T1 := context T[A] in
        let T2 := context T[B] in
        assert (h' : Σ |-i T1 = T2) ; [
          clear - h ;
          induction h ; [
            apply conv_eq ; simpl nl ; f_equal ; assumption
          | eapply conv_red_l ; [
              econstructor ; eassumption
            | eassumption
            ]
          | eapply conv_red_r ; [
              eassumption
            | econstructor ; eassumption
            ]
          ]
        | apply (conv_trans h') ; clear h'
        ]
      | _ => fail "Equation doesn't contain " A
      end
    | _ => fail "conv rewrite cannot apply to this goal"
    end
  end.

Ltac conv_rewrite h :=
  (conv_rewrite_l h) + (apply conv_sym ; conv_rewrite_l h ; apply conv_sym).

Ltac conv_rewrite_sym h :=
  let h' := fresh "h" in
  pose proof (conv_sym h) as h' ;
  conv_rewrite h' ;
  clear h'.

(* Ltac conv_rewrites hl := *)
(*   match hl with *)
(*   (* | ?h ?l => conv_rewrite h ; conv_rewrites l *) *)
(*   | ?h => conv_rewrite h *)
(*   end. *)

Tactic Notation "conv" "rewrite" hyp(h) := conv_rewrite h.
(* Tactic Notation "conv" "rewrite" hyp_list(hl) := conv_rewrites hl. *)
(* Tactic Notation "conv" "rewrite" ne_hyp_list(hl) := conv_rewrites hl. *)
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) :=
  conv rewrite h1 ; conv rewrite h2.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) :=
  conv rewrite h1 ; conv rewrite h2, h3.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4) :=
  conv rewrite h1 ; conv rewrite h2, h3, h4.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) :=
  conv rewrite h1 ; conv rewrite h2, h3, h4, h5.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) :=
  conv rewrite h1 ; conv rewrite h2, h3, h4, h5, h6.
Tactic Notation "conv" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) "," hyp(h7) :=
  conv rewrite h1 ; conv rewrite h2, h3, h4, h5, h6, h7.

Tactic Notation "conv" "rewrite" "<-" hyp(h) := conv_rewrite_sym h.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) :=
  conv rewrite <- h1 ; conv rewrite <- h2.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3, h4.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3, h4, h5.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3, h4, h5, h6.
Tactic Notation "conv" "rewrite" "<-" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) "," hyp(h7) :=
  conv rewrite <- h1 ; conv rewrite <- h2, h3, h4, h5, h6, h7.

Lemma cong_Heq :
  forall {Σ A a B b A' a' B' b'},
    Σ |-i A = A' ->
    Σ |-i a = a' ->
    Σ |-i B = B' ->
    Σ |-i b = b' ->
    Σ |-i sHeq A a B b = sHeq A' a' B' b'.
Proof.
  intros Σ A a B b A' a' B' b' hA ha hB hb.
  conv rewrite hA, ha, hB, hb.
  apply conv_refl.
Defined.

Lemma cong_Eq :
  forall {Σ A u v A' u' v'},
    Σ |-i A = A' ->
    Σ |-i u = u' ->
    Σ |-i v = v' ->
    Σ |-i sEq A u v = sEq A' u' v'.
Proof.
  intros Σ A u v A' u' v' hA hu hv.
  conv rewrite hA, hu, hv.
  apply conv_refl.
Defined.

Lemma cong_Transport :
  forall {Σ A B p t A' B' p' t'},
    Σ |-i A = A' ->
    Σ |-i B = B' ->
    Σ |-i p = p' ->
    Σ |-i t = t' ->
    Σ |-i sTransport A B p t = sTransport A' B' p' t'.
Proof.
  intros Σ A B p t A' B' p' t' hA hB hp ht.
  conv rewrite hA, hB, hp, ht.
  apply conv_refl.
Defined.

Lemma cong_Prod :
  forall {Σ nx A B nx' A' B'},
    Σ |-i A = A' ->
    Σ |-i B = B' ->
    Σ |-i sProd nx A B = sProd nx' A' B'.
Proof.
  intros Σ nx A B nx' A' B' hA hB.
  conv rewrite hB, hA.
  apply conv_eq. cbn. reflexivity.
Defined.

Lemma cong_Lambda :
  forall {Σ nx A B t nx' A' B' t'},
    Σ |-i A = A' ->
    Σ |-i B = B' ->
    Σ |-i t = t' ->
    Σ |-i sLambda nx A B t = sLambda nx' A' B' t'.
Proof.
  intros Σ nx A B t nx' A' B' t' hA hB ht.
  conv rewrite hB, ht, hA.
  apply conv_eq. cbn. reflexivity.
Defined.

Lemma cong_App :
  forall {Σ u A B v u' A' B' v'},
    Σ |-i A = A' ->
    Σ |-i B = B' ->
    Σ |-i u = u' ->
    Σ |-i v = v' ->
    Σ |-i sApp u A B v = sApp u' A' B' v'.
Proof.
  intros Σ u A B v u' A' B' v' hA hB hu hv.
  conv rewrite hB, hu, hv, hA.
  apply conv_eq. cbn. reflexivity.
Defined.

Lemma cong_Refl :
  forall {Σ A u A' u'},
    Σ |-i A = A' ->
    Σ |-i u = u' ->
    Σ |-i sRefl A u = sRefl A' u'.
Proof.
  intros Σ A u A' u' hA hu.
  conv rewrite hA, hu. apply conv_refl.
Defined.

Lemma cong_Pack :
  forall {Σ A1 A2 A1' A2'},
    Σ |-i A1 = A1' ->
    Σ |-i A2 = A2' ->
    Σ |-i sPack A1 A2 = sPack A1' A2'.
Proof.
  intros Σ A1 A2 A1' A2' h1 h2.
  conv rewrite h2, h1.
  apply conv_refl.
Defined.


(** Congruence with lift *)

Lemma meta_red_eq :
  forall {Σ t u u'},
    Σ |-i t ▷ u ->
    u = u' ->
    Σ |-i t ▷ u'.
Proof.
  intros Σ t u u' h e. destruct e. assumption.
Defined.

Fixpoint lift_red1 {Σ n k t1 t2} (h : Σ |-i t1 ▷ t2) :
  Σ |-i lift n k t1 ▷ lift n k t2

with lift_redbrs1 {Σ n k b1 b2} (h : redbrs1 Σ b1 b2) :
  redbrs1 Σ
          (map (on_snd (lift n k)) b1) (map (on_snd (lift n k)) b2).
Proof.
  - { destruct h ; cbn ;
      try match goal with
          | h : _ |-i ?t ▷ _ |- _ |-i ?tt ▷ _ =>
            match tt with
            | context [t] =>
              econstructor ;
              eapply lift_red1 ; [ exact h | .. ]
            end
          end.
      - eapply meta_red_eq ; [ econstructor |].
        rewrite <- substP1. cbn. reflexivity.
      - eapply meta_red_eq ; [ econstructor |]. reflexivity.
      - eapply meta_red_eq ; [ econstructor |]. reflexivity.
      - eapply meta_red_eq ; [ econstructor | reflexivity ].
        eapply lift_redbrs1. assumption.
    }

  - { destruct h.
      - econstructor. eapply lift_red1. assumption.
      - cbn. econstructor. eapply lift_redbrs1. assumption.
    }
Defined.

Lemma lift_conv :
  forall {Σ n k t1 t2},
    Σ |-i t1 = t2 ->
    Σ |-i lift n k t1 = lift n k t2.
Proof.
  intros Σ n k t1 t2 h.
  induction h.
  - apply conv_eq. apply nl_lift. assumption.
  - eapply conv_red_l.
    + eapply lift_red1. eassumption.
    + assumption.
  - eapply conv_red_r.
    + eassumption.
    + eapply lift_red1. eassumption.
Defined.

Corollary cong_lift01 :
  forall {Σ t1 t2},
    Σ |-i t1 = t2 ->
    Σ |-i lift0 1 t1 = lift0 1 t2.
Proof.
  intros Σ t1 t2 h.
  apply lift_conv. assumption.
Defined.

(** Congruence with substitution *)

Fixpoint subst_red1 {Σ n t1 t2 u}
  (h : Σ |-i t1 ▷ t2) :
  Σ |-i t1{ n := u } ▷ t2{ n := u }

with subst_redbrs1 {Σ n b1 b2 u}
  (h : redbrs1 Σ b1 b2) :
  redbrs1 Σ
          (map (on_snd (subst u n)) b1) (map (on_snd (subst u n)) b2).
Proof.
  - { destruct h ; cbn ;
      try match goal with
          | h : _ |-i ?t ▷ _ |- _ |-i ?tt ▷ _ =>
            match tt with
            | context [t] =>
              econstructor ;
              eapply subst_red1 ; [ exact h | .. ]
            end
          end.
      - eapply meta_red_eq ; [ econstructor |].
        rewrite <- substP4. cbn. reflexivity.
      - eapply meta_red_eq ; [ econstructor |]. reflexivity.
      - eapply meta_red_eq ; [ econstructor |]. reflexivity.
      - eapply meta_red_eq ; [ econstructor | reflexivity ].
        eapply subst_redbrs1. eassumption.
    }

  - { destruct h.
      - econstructor. eapply subst_red1. eassumption.
      - cbn. econstructor. eapply subst_redbrs1. eassumption.
    }
Defined.

Lemma subst_conv :
  forall {Σ n u t1 t2},
    Σ |-i t1 = t2 ->
    Σ |-i t1{ n := u } = t2{ n := u }.
Proof.
  intros Σ n u t1 t2 h.
  induction h.
  - apply conv_eq. apply nl_subst ; [ assumption | reflexivity ].
  - eapply conv_red_l.
    + eapply subst_red1. eassumption.
    + assumption.
  - eapply conv_red_r.
    + eassumption.
    + eapply subst_red1. eassumption.
Defined.


(** Congruence of equal substitutions *)

Lemma red_trans :
  forall {Σ t u v},
    Σ |-i t ▷⃰ u ->
    Σ |-i u ▷⃰ v ->
    Σ |-i t ▷⃰ v.
Proof.
  intros Σ t u v h1 h2. revert v h2.
  induction h1.
  - intros v h2. assumption.
  - intros w h2. specialize (IHh1 w h2).
    econstructor ; eassumption.
Defined.

Ltac red_rewrite h :=
  let h' := fresh "h" in
  match type of h with
  | _ |-i ?A ▷⃰ ?B =>
    lazymatch goal with
    | |- ?Σ |-i ?ctx ▷⃰ _ =>
      lazymatch ctx with
      | context T [A] =>
        let T1 := context T[A] in
        let T2 := context T[B] in
        assert (h' : Σ |-i T1 ▷⃰ T2) ; [
          clear - h ;
          induction h ; [
            constructor
          | econstructor ; [
              econstructor ; eassumption
            | eassumption
            ]
          ]
        | eapply (red_trans h') ; clear h'
        ]
      | _ => fail "Lhs doesn't contain " A
      end
    | _ => fail "red rewrite cannot apply to this goal"
    end
  end.

Tactic Notation "red" "rewrite" hyp(h) := red_rewrite h.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) :=
  red rewrite h1 ; red rewrite h2.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) :=
  red rewrite h1 ; red rewrite h2, h3.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4) :=
  red rewrite h1 ; red rewrite h2, h3, h4.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) :=
  red rewrite h1 ; red rewrite h2, h3, h4, h5.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) :=
  red rewrite h1 ; red rewrite h2, h3, h4, h5, h6.
Tactic Notation "red" "rewrite" hyp(h1) "," hyp(h2) "," hyp(h3) "," hyp(h4)
       "," hyp(h5) "," hyp(h6) "," hyp(h7) :=
  red rewrite h1 ; red rewrite h2, h3, h4, h5, h6, h7.

Section conv_substs.

  Ltac sp h n :=
    lazymatch goal with
    | hu : _ |-i _ ▷ _ |- _ =>
      specialize (h n _ _ hu) ;
      cbn in h
    end.

  Ltac spone :=
    match goal with
    | ih : forall n u1 u2, _ -> _ |-i ?t{n := u1} = _ |- context [ ?t{ ?m := _ } ] =>
      sp ih m
    end.

  Ltac spall :=
    repeat spone.

  Ltac conv_rewrite_assumption :=
    match goal with
    | ih : _ |-i _ = _ |- _ => conv rewrite ih
    end.

  Ltac conv_rewrite_assumptions :=
    repeat conv_rewrite_assumption.

  Reserved Notation " Σ '|-i' t == u " (at level 50, t, u at next level).

  Inductive convbrs (Σ : sglobal_context) :
    list (nat * sterm) -> list (nat * sterm) -> Prop :=
  | convbrs_nil : Σ |-i [] == []
  | convbrs_cons n u v b c :
      Σ |-i u = v ->
      Σ |-i b == c ->
      Σ |-i ((n,u) :: b) == ((n,v) :: c)

  where " Σ '|-i' t == u " := (@convbrs Σ t u) : i_scope.

  Fact convbrs_length :
    forall {Σ b1 b2},
      Σ |-i b1 == b2 ->
      #|b1| = #|b2|.
  Proof.
    intros Σ b1 b2 h. induction h ; cbn ; easy.
  Defined.

  Lemma convbrs_nth :
    forall {Σ b1 b2 n h1 h2},
      Σ |-i b1 == b2 ->
      let u := safe_nth b1 (exist _ n h1) in
      let v := safe_nth b2 (exist _ n h2) in
      (fst u = fst v) * (Σ |-i snd u = snd v).
  Proof.
    intros Σ b1 b2 n h1 h2 h. revert n h1 h2.
    induction h.
    - cbn. intros. bang.
    - intros [| m] h1 h2 u' v'.
      + cbn in *. split ; [ reflexivity | assumption ].
      + cbn in u'. cbn in v'.
        apply IHh.
  Defined.

  Lemma cong_Case_brs :
    forall {Σ indn p c b1 b2},
      Σ |-i b1 == b2 ->
      Σ |-i sCase indn p c b1 = sCase indn p c b2.
  Proof.
    intros Σ indn p c b1 b2 hb.
    pose (P := fun m =>
                 let bb := ((firstn m b1) ++ (skipn m b2))%list in
                 Σ |-i sCase indn p c bb = sCase indn p c b2).
    pose proof (convbrs_length hb) as eql.
    assert (aux : P #|b1|).
    { eapply fin_indT_last ; subst P ; cbn beta.
      - cbn. apply conv_refl.
      - intros n hn ih _. cbn in ih.
        pose (u := safe_nth b1 (exist _ n hn)).
        assert (hn' : n < #|b2|) by omega.
        pose (v := safe_nth b2 (exist _ n hn')).
        erewrite @firstn_reconstruct
          with (a := u) by (eapply nth_error_safe_nth).
        assert (eq : (fst u = fst v) * (Σ |-i snd u = snd v)).
        { eapply convbrs_nth. assumption.
        }
        destruct eq as [eq h].
        assert (hh :
          Σ |-i sCase indn p c ((firstn n b1 ++ [u]) ++ skipn (S n) b2)
             = sCase indn p c ((firstn n b1 ++ [v]) ++ skipn (S n) b2)).
        { clearbody u. clearbody v.
          destruct u as [m' u], v as [m v]. cbn in eq. subst. cbn in h.
          clear - h. dependent induction h.
          - apply conv_eq. simpl.
            f_equal. rewrite !map_app. f_equal. f_equal.
            cbn. f_equal. unfold on_snd. f_equal ; assumption.
          - eapply conv_red_l ; [
              eapply case_red_brs
            | eassumption
            ].
            set (l1 := firstn n b1). clearbody l1.
            set (l2 := skipn (S n) b2). clearbody l2.
            clear - H. revert l2. induction l1.
            + intro l2. cbn. econstructor. assumption.
            + intro l2. cbn. econstructor. apply IHl1.
          - eapply conv_red_r ; [
              eassumption
            | eapply case_red_brs
            ].
            set (l1 := firstn n b1). clearbody l1.
            set (l2 := skipn (S n) b2). clearbody l2.
            clear - H. revert l2. induction l1.
            + intro l2. cbn. econstructor. assumption.
            + intro l2. cbn. econstructor. apply IHl1.
        }
        eapply conv_trans ; try eassumption.
        erewrite @skipn_reconstruct
          with (a := v) in ih by (eapply nth_error_safe_nth).
        replace ((firstn n b1 ++ [v]) ++ skipn (S n) b2)%list
          with (firstn n b1 ++ v :: skipn (S n) b2)%list
          by (rewrite app_assoc_reverse ; reflexivity).
        assumption.
    }
    subst P. cbn in aux.
    rewrite firstn_all, eql, skipn_all, app_nil_r in aux.
    assumption.
  Defined.

  Lemma substs_red1 {Σ} (t : sterm) :
    forall n {u1 u2},
      fst Σ |-i u1 ▷ u2 ->
      Σ |-i t{ n := u1 } = t{ n := u2 }.
  Proof.
    induction t using sterm_rect_list ; intros m u1 u2 h.
    all: cbn ; spall ; conv_rewrite_assumptions.
    all: try (apply conv_refl).
    - case_eq (m ?= n) ; intro e ; bprop e.
      + eapply lift_conv.
        eapply conv_red_l ; try eassumption. apply conv_refl.
      + apply conv_refl.
      + apply conv_refl.
    - assert (h' : Σ |-i map (on_snd (subst u1 m)) brs
                     == map (on_snd (subst u2 m)) brs).
      { clear - h X. revert u1 u2 h. induction X.
        - cbn. constructor.
        - intros u1 u2 h. cbn.
          destruct x as [n x].
          econstructor.
          + eapply p. assumption.
          + eapply IHX. assumption.
      }
      apply cong_Case_brs. assumption.
  Defined.

End conv_substs.

Lemma substs_conv :
  forall {Σ n u1 u2 t},
    Σ |-i u1 = u2 ->
    Σ |-i t{ n := u1 } = t{ n := u2 }.
Proof.
  intros Σ n u1 u2 t h.
  induction h.
  - apply conv_eq. apply nl_subst ; [ reflexivity | assumption ].
  - eapply conv_trans ; try eassumption.
    eapply substs_red1. assumption.
  - eapply conv_trans ; try eassumption.
    eapply conv_sym.
    eapply substs_red1. assumption.
Defined.

Corollary cong_subst :
  forall {Σ n u1 u2 t1 t2},
    Σ |-i u1 = u2 ->
    Σ |-i t1 = t2 ->
    Σ |-i t1{ n := u1 } = t2{ n := u2 }.
Proof.
  intros Σ n u1 u2 t1 t2 hu ht.
  eapply conv_trans.
  - eapply substs_conv. eassumption.
  - eapply subst_conv. assumption.
Defined.

(*! Inversion results about conversion *)

Lemma sort_conv_inv :
  forall {Σ s1 s2},
    Σ |-i sSort s1 = sSort s2 ->
    s1 = s2.
Proof.
  intros Σ s1 s2 h. dependent induction h.
  - cbn in H. now inversion H.
  - inversion H.
  - inversion H.
Defined.

Ltac inversion_eq :=
  match goal with
  | H : _ = _ |- _ => inversion H
  end.

Ltac invconv h :=
  dependent induction h ; [
    cbn in * ; inversion_eq ;
    repeat split ; apply conv_eq ; assumption
  | dependent destruction H ;
    split_hyps ; repeat split ; try assumption ;
    eapply conv_red_l ; eassumption
  | dependent destruction H ;
    split_hyps ; repeat split ; try assumption ;
    eapply conv_red_r ; eassumption
  ].

Lemma heq_conv_inv :
  forall {Σ A a B b A' a' B' b'},
    Σ |-i sHeq A a B b = sHeq A' a' B' b' ->
    (Σ |-i A = A') *
    (Σ |-i a = a') *
    (Σ |-i B = B') *
    (Σ |-i b = b').
Proof.
  intros Σ A a B b A' a' B' b' h.
  invconv h.
Defined.

Lemma eq_conv_inv :
  forall {Σ A u v A' u' v'},
    Σ |-i sEq A u v = sEq A' u' v' ->
    (Σ |-i A = A') *
    (Σ |-i u = u') *
    (Σ |-i v = v').
Proof.
  intros Σ A u v A' u' v' h.
  invconv h.
Defined.

Lemma pack_conv_inv :
  forall {Σ A1 A2 A1' A2'},
    Σ |-i sPack A1 A2 = sPack A1' A2' ->
    (Σ |-i A1 = A1') * (Σ |-i A2 = A2').
Proof.
  intros Σ A1 A2 A1' A2' h.
  invconv h.
Defined.

Lemma prod_inv :
  forall {Σ nx ny A B A' B'},
    Σ |-i sProd nx A B = sProd ny A' B' ->
    (Σ |-i A = A') * (Σ |-i B = B').
Proof.
  intros Σ nx ny A B A' B' h.
  invconv h.
Defined.
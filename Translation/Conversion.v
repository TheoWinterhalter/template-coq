From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import util SAst SInduction SLiftSubst SCommon.

Open Scope s_scope.

(*! Reduction. *)

(** NOTE: Do we need to switch to n-ary application? *)

(* TODO in branch case with Apps *)
(* Definition iota_red npar c args brs := *)
(*   (mkApps (snd (List.nth c brs (0, tRel 0))) (List.skipn npar args)). *)

Inductive red1 (Σ : sglobal_declarations) : sterm -> sterm -> Prop :=
(*! Computation *)

(** β *)
| red_beta n A B t u :
    red1 Σ (sApp (sLambda n A B t) n A B u) (t{ 0 := u })

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
| case_red_discr ind p c c' brs :
    red1 Σ c c' ->
    red1 Σ (sCase ind p c brs) (sCase ind p c' brs)

| case_red_brs ind p c brs brs' :
    redbrs1 Σ brs brs' ->
    red1 Σ (sCase ind p c brs) (sCase ind p c brs')

(** App *)
| app_red_fun u u' na A B v :
    red1 Σ u u' ->
    red1 Σ (sApp u na A B v) (sApp u' na A B v)

| app_red_dom u na A A' B v :
    red1 Σ A A' ->
    red1 Σ (sApp u na A B v) (sApp u na A' B v)

| app_red_codom u na A B B' v :
    red1 Σ B B' ->
    red1 Σ (sApp u na A B v) (sApp u na A B' v)

| app_red_arg u na A B v v' :
    red1 Σ v v' ->
    red1 Σ (sApp u na A B v) (sApp u na A B v')

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
| heqtypeeq_red p p' :
    red1 Σ p p' ->
    red1 Σ (sHeqTypeEq p) (sHeqTypeEq p')

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

(*! Conversion *)

Reserved Notation " Σ '|-i' t = u " (at level 50, t, u at next level).

(* TODO: Stop using eq_term but instead something that compares the nameless
   terms. *)

Inductive conv (Σ : sglobal_context) : sterm -> sterm -> Prop :=
| conv_eq t u : eq_term t u = true -> Σ |-i t = u
| conv_red_l t u v : red1 (fst Σ) t v -> Σ |-i v = u -> Σ |-i t = u
| conv_red_r t u v : Σ |-i t = v -> red1 (fst Σ) u v -> Σ |-i t = u
| conv_trans t u v : Σ |-i t = u -> Σ |-i u = v -> Σ |-i t = v

where " Σ '|-i' t = u " := (@conv Σ t u) : i_scope.

Derive Signature for conv.

Arguments conv_trans {_ _ _ _} _ _.

Open Scope i_scope.

Lemma conv_refl :
  forall Σ t, Σ |-i t = t.
Proof.
  intros Σ t.
  apply conv_eq. apply eq_term_refl.
Defined.

(* TODO Anonymise terms before comparing them so that eq_term reflects
   equality *)
Lemma conv_sym :
  forall {Σ t u},
    Σ |-i t = u ->
    Σ |-i u = t.
Proof.
  intros Σ t u h.
  induction h.
  - admit.
  - eapply conv_red_r ; eassumption.
  - eapply conv_red_l ; eassumption.
  - eapply conv_trans ; eassumption.
Admitted.


(*! Congruences for conversion *)

Ltac conv_rewrite h :=
  let h' := fresh "h" in
  match type of h with
  | _ |-i ?A = ?B =>
    lazymatch goal with
    | |- ?Σ |-i ?ctx = _ =>
      lazymatch ctx with
      | context T [A] =>
        let T1 := context T[A] in
        let T2 := context T[B] in
        assert (h' : Σ |-i T1 = T2) ; [
          clear - h ;
          induction h ; [
            apply conv_eq ; cbn ; rewrite ?eq_term_refl ;
            rewrite_assumption ; reflexivity
          | eapply conv_red_l ; [
              econstructor ; eassumption
            | eassumption
            ]
          | eapply conv_red_r ; [
              eassumption
            | econstructor ; eassumption
            ]
          | eapply conv_trans ; eassumption
          ]
        | apply (conv_trans h') ; clear h'
        ]
      | _ => fail "Lhs doesn't contain " A
      end
    | _ => fail "conv rewrite cannot apply to this goal"
    end
  end.

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
  apply conv_eq. cbn. rewrite !eq_term_refl. reflexivity.
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
  apply conv_eq. cbn. rewrite !eq_term_refl. reflexivity.
Defined.

Lemma cong_App :
  forall {Σ u nx A B v u' nx' A' B' v'},
    Σ |-i A = A' ->
    Σ |-i B = B' ->
    Σ |-i u = u' ->
    Σ |-i v = v' ->
    Σ |-i sApp u nx A B v = sApp u' nx' A' B' v'.
Proof.
  intros Σ u nx A B v u' nx' A' B' v' hA hB hu hv.
  conv rewrite hB, hu, hv, hA.
  apply conv_eq. cbn. rewrite !eq_term_refl. reflexivity.
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
  - apply conv_eq. admit.
  - eapply conv_red_l.
    + eapply lift_red1. eassumption.
    + assumption.
  - eapply conv_red_r.
    + eassumption.
    + eapply lift_red1. eassumption.
  - eapply conv_trans ; eassumption.
Admitted.

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
  - apply conv_eq. admit.
  - eapply conv_red_l.
    + eapply subst_red1. eassumption.
    + assumption.
  - eapply conv_red_r.
    + eassumption.
    + eapply subst_red1. eassumption.
  - eapply conv_trans ; eassumption.
Admitted.


(** Congruence of equal substitutions *)

Section conv_substs.

  Ltac sp h n :=
    lazymatch goal with
    | hu : _ |-i _ ▷ _ |- _ =>
      specialize (h n _ _ hu) ;
      cbn in h ;
      try rewrite !subst_decl_svass in h
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

  Lemma substs_red1 {Σ} (t : sterm) :
    forall n {u1 u2},
      (fst Σ) |-i u1 ▷ u2 ->
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
    - (* Tedious? *)
      admit.
  Admitted.

End conv_substs.

Lemma substs_conv :
  forall {Σ n u1 u2 t},
    Σ |-i u1 = u2 ->
    Σ |-i t{ n := u1 } = t{ n := u2 }.
Proof.
  intros Σ n u1 u2 t h.
  induction h.
  - apply conv_eq. admit.
  - eapply conv_trans ; try eassumption.
    eapply substs_red1. assumption.
  - eapply conv_trans ; try eassumption.
    eapply conv_sym.
    eapply substs_red1. assumption.
  - eapply conv_trans ; eassumption.
Admitted.
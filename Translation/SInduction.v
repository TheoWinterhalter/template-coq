(* Induction principle on SAst *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst.
From Translation Require Import util SAst.

Open Scope type_scope.

Definition on_snd {A B B'} (f : B -> B') (x : A * B) : A * B' :=
  (* let '(u,v) := x in (u, f v). *)
  (fst x, f (snd x)).

Definition test_snd {A B} (f : B -> bool) (p : A * B) :=
  f (snd p).

Lemma on_snd_on_snd {A B} (f g : B -> B) (d : A * B) :
  on_snd f (on_snd g d) = on_snd (fun x => f (g x)) d.
Proof.
  destruct d; reflexivity.
Defined.

Lemma compose_on_snd {A B C D} (f : C -> D) (g : B -> C) :
  compose (A := A * B) (on_snd f) (on_snd g) = on_snd (compose f g).
Proof.
  reflexivity.
Defined.

Lemma map_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (compose g f) l.
Proof. apply map_map. Defined.
Hint Unfold compose : terms.

Lemma map_id_f {A} (l : list A) (f : A -> A) :
  (forall x, f x = x) ->
  map f l = l.
Proof.
  induction l; intros; simpl; try easy.
  rewrite H. f_equal. eauto.
Defined.

Lemma map_on_snd_id {A B} (l : list (A * B)) :
  map (on_snd id) l = l.
Proof.
  eapply map_id_f. intros [x y].
  reflexivity.
Defined.

Lemma forallb_map :
  forall {A} {f : A -> A} {p : A -> bool} {l : list A},
    forallb p (map f l) = forallb (compose p f) l.
Proof.
  intros A f p l.
  induction l.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Lemma compose_test_snd_on_snd :
  forall {A B} {f : B -> bool} {g : B -> B},
    @test_snd A B f ∘ on_snd g = test_snd (f ∘ g).
Proof.
  intros A B f g.
  reflexivity.
Defined.

Definition ftrue {A} (x : A) : bool := true.

Lemma forallb_true :
  forall {A} (l : list A),
    forallb ftrue l = true.
Proof.
  intros A l. induction l.
  - reflexivity.
  - cbn. assumption.
Defined.

Lemma forallb_test_snd_true :
  forall {A B} (l : list (A * B)),
    forallb (test_snd ftrue) l = true.
Proof.
  intros A B l.
  apply forallb_true.
Defined.

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
| ForallT_nil : ForallT P []
| ForallT_cons x l : P x -> ForallT P l -> ForallT P (x :: l).

Derive Signature for ForallT.

Lemma ForallT_nth :
  forall {A} {P : A -> Type} {l n t},
    ForallT P l ->
    nth_error l n = Some t ->
    P t.
Proof.
  intros A P l n t h hn. revert n t hn.
  induction h ; intros n t hn.
  - destruct n ; cbn in hn ; discriminate hn.
  - destruct n.
    + cbn in hn. inversion hn. subst. assumption.
    + cbn in hn. eapply IHh. eassumption.
Defined.

Definition sCaseBrsT (P : sterm -> Type) (brs : list (nat * sterm)) :=
  ForallT (fun x => P (snd x)) brs.

Fact sCaseBrsT_nth :
  forall {P brs n p},
    sCaseBrsT P brs ->
    nth_error brs n = Some p ->
    P (snd p).
Proof.
  intros P brs n p h hn.
  unfold sCaseBrsT in h.
  eapply @ForallT_nth with (P := fun p => P (snd p)) ; eassumption.
Defined.

Lemma sterm_rect_list :
  forall P : sterm -> Type,
    (forall n : nat, P (sRel n)) ->
    (forall s : sort, P (sSort s)) ->
    (forall (nx : name) (A : sterm), P A -> forall B : sterm, P B -> P (sProd nx A B)) ->
    (forall (nx : name) (A : sterm), P A -> forall B : sterm, P B -> forall t : sterm, P t ->
       P (sLambda nx A B t)) ->
    (forall u : sterm, P u ->
     forall (A : sterm), P A ->
     forall B : sterm, P B ->
     forall v : sterm, P v ->
       P (sApp u A B v)) ->
    (forall A : sterm, P A -> forall u : sterm, P u -> forall v : sterm, P v -> P (sEq A u v)) ->
    (forall A : sterm, P A -> forall u : sterm, P u -> P (sRefl A u)) ->
    (forall A : sterm, P A ->
     forall u : sterm, P u ->
     forall P0 : sterm, P P0 ->
     forall w : sterm, P w ->
     forall v : sterm, P v ->
     forall p : sterm, P p ->
       P (sJ A u P0 w v p)) ->
    (forall T1 : sterm, P T1 ->
     forall T2 : sterm, P T2 ->
     forall p : sterm, P p ->
     forall t : sterm, P t ->
       P (sTransport T1 T2 p t)) ->
    (forall A : sterm, P A ->
     forall a : sterm, P a ->
     forall B : sterm, P B ->
     forall b : sterm, P b ->
       P (sHeq A a B b)) ->
    (forall p : sterm, P p -> P (sHeqToEq p)) ->
    (forall A : sterm, P A -> forall a : sterm, P a -> P (sHeqRefl A a)) ->
    (forall p : sterm, P p -> P (sHeqSym p)) ->
    (forall p : sterm, P p -> forall q : sterm, P q -> P (sHeqTrans p q)) ->
    (forall p : sterm, P p -> forall t : sterm, P t -> P (sHeqTransport p t)) ->
    (forall B1 : sterm, P B1 ->
     forall B2 : sterm, P B2 ->
     forall pA : sterm, P pA ->
     forall pB : sterm, P pB ->
       P (sCongProd B1 B2 pA pB)) ->
    (forall B1 : sterm, P B1 ->
     forall B2 : sterm, P B2 ->
     forall t1 : sterm, P t1 ->
     forall t2 : sterm, P t2 ->
     forall pA : sterm, P pA ->
     forall pB : sterm, P pB ->
     forall pt : sterm, P pt ->
       P (sCongLambda B1 B2 t1 t2 pA pB pt)) ->
    (forall B1 : sterm, P B1 ->
     forall B2 : sterm, P B2 ->
     forall pu : sterm, P pu ->
     forall pA : sterm, P pA ->
     forall pB : sterm, P pB ->
     forall pv : sterm, P pv ->
       P (sCongApp B1 B2 pu pA pB pv)) ->
    (forall pA : sterm, P pA -> forall pu : sterm, P pu -> forall pv : sterm, P pv ->
       P (sCongEq pA pu pv)) ->
    (forall pA : sterm, P pA -> forall pu : sterm, P pu -> P (sCongRefl pA pu)) ->
    (forall p : sterm, P p -> P (sEqToHeq p)) ->
    (forall A, P A -> forall B, P B -> forall p : sterm, P p -> P (sHeqTypeEq A B p)) ->
    (forall A1 : sterm, P A1 -> forall A2 : sterm, P A2 -> P (sPack A1 A2)) ->
    (forall p : sterm, P p -> P (sProjT1 p)) ->
    (forall p : sterm, P p -> P (sProjT2 p)) ->
    (forall p : sterm, P p -> P (sProjTe p)) ->
    (forall ind : inductive, P (sInd ind)) ->
    (forall (ind : inductive) (n : nat), P (sConstruct ind n)) ->
    (forall (indn : inductive * nat) (p : sterm), P p ->
     forall c : sterm, P c ->
     forall brs : list (nat * sterm), sCaseBrsT P brs ->
       P (sCase indn p c brs)) ->
    (forall ind : inductive, P (sElim ind)) ->
    forall t : sterm, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t ;
  match goal with
  | H : _ |- _ => apply H
  end ; auto.
  revert brs.
  fix auxbrs' 1.
  destruct brs ; constructor ; [| apply auxbrs' ].
  apply auxt.
Defined.

Lemma forall_map_spec {A} {P : A -> Type} {l B} {f g : A -> B} :
  ForallT P l ->
  (forall x, P x -> f x = g x) ->
  map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  intros Heq. rewrite Heq by assumption.
  f_equal. apply IHX. apply Heq.
Defined.

Lemma on_snd_spec {A B C} (P : B -> Type) (f g : B -> C) (x : A * B) :
  P (snd x) -> (forall x, P x -> f x = g x) ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H; auto.
Defined.

Lemma case_brs_map_spec {P : sterm -> Type} {l A} {f g : sterm -> A} :
  sCaseBrsT P l ->
  (forall x, P x -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros.
  eapply (forall_map_spec X).
  intros.
  eapply on_snd_spec; eauto.
Defined.

Lemma forall_forallb_spec :
  forall {A} {P : A -> Type} {l} {f g : A -> bool},
    ForallT P l ->
    (forall x, P x -> f x = g x) ->
    forallb f l = forallb g l.
Proof.
  intros A P l f g. induction 1.
  - simpl. trivial.
  - intro eq. cbn. rewrite eq by assumption.
    f_equal. apply IHX. assumption.
Defined.

Lemma test_snd_spec {A B} (P : B -> Type) (f g : B -> bool) (x : A * B) :
  P (snd x) -> (forall x, P x -> f x = g x) ->
  test_snd f x = test_snd g x.
Proof.
  intros. destruct x. unfold test_snd. simpl.
  now rewrite H; auto.
Defined.

Lemma case_brs_forallb_spec {P : sterm -> Type} {l} {f g : sterm -> bool} :
  sCaseBrsT P l ->
  (forall x, P x -> f x = g x) ->
  forallb (test_snd f) l = forallb (test_snd g) l.
Proof.
  intros.
  eapply (forall_forallb_spec X).
  intros x h.
  eapply test_snd_spec; eauto.
Defined.

Lemma forall_forallb_forallb_spec {A : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f g : A -> bool} :
    ForallT P l ->
    forallb p l = true ->
    (forall x : A, P x -> p x = true -> f x = g x) ->
    forallb f l = forallb g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_true_iff. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHX.
Defined.

Lemma case_brs_forallb_forallb_spec {P : sterm -> Type} {p : sterm -> bool}
  {f g : sterm -> bool} {l} :
  sCaseBrsT P l ->
  forallb (test_snd p) l = true ->
  (forall x, P x -> p x = true -> f x = g x) ->
  forallb (test_snd f) l = forallb (test_snd g) l.
Proof.
  intros.
  eapply (forall_forallb_forallb_spec X H).
  intros x h1 h2. eapply H0 ; eauto.
Defined.

Lemma forall_forallb_map_spec {A : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f g : A -> A} :
    ForallT P l ->
    forallb p l = true ->
    (forall x : A, P x -> p x = true -> f x = g x) ->
    map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_true_iff. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHX.
Defined.

Lemma on_snd_test_spec {A B} (P : B -> Type) (p : B -> bool) (f g : B -> B) (x : A * B) :
  P (snd x) ->
  (forall x, P x -> p x = true -> f x = g x) ->
  test_snd p x = true ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H; auto.
Defined.

Lemma case_brs_forallb_map_spec {P : sterm -> Type} {p : sterm -> bool}
      {l} {f g : sterm -> sterm} :
  sCaseBrsT P l ->
  forallb (test_snd p) l = true ->
  (forall x, P x -> p x = true -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros.
  eapply (forall_forallb_map_spec X H).
  intros.
  eapply on_snd_test_spec; eauto.
Defined.
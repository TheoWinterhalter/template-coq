From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import util SAst SInduction SLiftSubst.

Record scontext_decl := { sdecl_name : name ;
                          sdecl_body : option sterm ;
                          sdecl_type : sterm }.

Definition svass x A :=
  {| sdecl_name := x; sdecl_body := None; sdecl_type := A |}.
Definition svdef x t A :=
  {| sdecl_name := x; sdecl_body := Some t; sdecl_type := A |}.

Definition scontext := (list scontext_decl).

Definition ssnoc (Γ : scontext) (d : scontext_decl) := d :: Γ.

Notation " Γ ,, d " := (ssnoc Γ d) (at level 20, d at next level) : s_scope.
Delimit Scope s_scope with s.

Record squash (A : Set) : Prop := { _ : A }.

Fixpoint eq_term (t u : sterm) {struct t} :=
  match t, u with
  | sRel n, sRel n' => eq_nat n n'
  | sSort s, sSort s' => eq_nat s s'
  | sProd _ A B, sProd _ A' B' => eq_term A A' && eq_term B B'
  | sLambda _ A B t, sLambda _ A' B' t' =>
    eq_term A A' && eq_term B B' && eq_term t t'
  | sApp u _ A B v, sApp u' _ A' B' v' =>
    eq_term u u' && eq_term A A' && eq_term B B' && eq_term v v'
  | sEq A u v, sEq A' u' v' =>
    eq_term A A' && eq_term u u' && eq_term v v'
  | sRefl A u, sRefl A' u' => eq_term A A' && eq_term u u'
  | sJ A u P w v p, sJ A' u' P' w' v' p' =>
    eq_term A A' && eq_term u u' && eq_term P P' &&
    eq_term w w' && eq_term v v' && eq_term p p'
  | sTransport T1 T2 p t, sTransport T1' T2' p' t' =>
    eq_term T1 T1' && eq_term T2 T2' &&
    eq_term p p' && eq_term t t'
  | sHeq A a B b, sHeq A' a' B' b' =>
    eq_term A A' && eq_term a a' &&
    eq_term B B' && eq_term b b'
  | sHeqToEq p, sHeqToEq p' => eq_term p p'
  | sHeqRefl A a, sHeqRefl A' a' => eq_term A A' && eq_term a a'
  | sHeqSym p, sHeqSym p' => eq_term p p'
  | sHeqTrans p q, sHeqTrans p' q' => eq_term p p' && eq_term q q'
  | sHeqTransport p t, sHeqTransport p' t' => eq_term p p' && eq_term t t'
  | sCongProd B1 B2 pA pB, sCongProd B1' B2' pA' pB' =>
    eq_term B1 B1' && eq_term B2 B2' && eq_term pA pA' && eq_term pB pB'
  | sCongLambda B1 B2 t1 t2 pA pB pt, sCongLambda B1' B2' t1' t2' pA' pB' pt' =>
    eq_term B1 B1' && eq_term B2 B2' && eq_term t1 t1' && eq_term t2 t2' &&
    eq_term pA pA' && eq_term pB pB' && eq_term pt pt'
  | sCongApp B1 B2 pu pA pB pv, sCongApp B1' B2' pu' pA' pB' pv' =>
    eq_term B1 B1' && eq_term B2 B2' && eq_term pu pu' &&
    eq_term pA pA' && eq_term pB pB' && eq_term pv pv'
  | sCongEq pA pu pv, sCongEq pA' pu' pv' =>
    eq_term pA pA' && eq_term pu pu' && eq_term pv pv'
  | sCongRefl pA pu, sCongRefl pA' pu' =>
    eq_term pA pA' && eq_term pu pu'
  | sEqToHeq p, sEqToHeq p' => eq_term p p'
  | sHeqTypeEq p, sHeqTypeEq p' => eq_term p p'
  | sPack A1 A2, sPack A1' A2' => eq_term A1 A1' && eq_term A2 A2'
  | sProjT1 p, sProjT1 p' => eq_term p p'
  | sProjT2 p, sProjT2 p' => eq_term p p'
  | sProjTe p, sProjTe p' => eq_term p p'
  | sInd i, sInd i' => eq_ind i i'
  | sConstruct i k, sConstruct i' k' => eq_ind i i' && eq_nat k k'
  | sCase (ind, par) p c brs, sCase (ind', par') p' c' brs' =>
    eq_ind ind ind' && eq_nat par par' &&
    eq_term p p' && eq_term c c' &&
    forallb2 (fun '(a,b) '(a',b') => eq_term b b') brs brs'
  | _, _ => false
  end.

Lemma eq_string_refl :
  forall s, eq_string s s = true.
Proof.
  unfold eq_string.
  intros s. case (string_dec s s).
  - intro e. reflexivity.
  - intros neq. exfalso. apply neq. reflexivity.
Qed.

Lemma eq_nat_refl :
  forall n, eq_nat n n = true.
Proof.
  intro n. unfold eq_nat.
  propb. reflexivity.
Qed.

Lemma eq_ind_refl :
  forall i, eq_ind i i = true.
Proof.
  unfold eq_ind. destruct i as [i n].
  apply andb_true_intro. split.
  - apply eq_string_refl.
  - apply eq_nat_refl.
Qed.

Fact eq_term_refl :
  forall {t}, eq_term t t = true.
Proof.
  intro t. induction t using sterm_rect_list.
  all: try (cbn ; rewrite_assumptions ;
            try rewrite eq_nat_refl ;
            try rewrite eq_string_refl ;
            try rewrite eq_ind_refl ; reflexivity).
  cbn. destruct indn as [i n].
  rewrite_assumptions. rewrite eq_ind_refl. rewrite eq_nat_refl.
  cbn. induction X.
  - constructor.
  - cbn. rewrite p. cbn. apply IHX.
Qed.

Fact eq_nat_trans :
  forall {i j k},
    eq_nat i j = true ->
    eq_nat j k = true ->
    eq_nat i k = true.
Proof.
  unfold eq_nat.
  intros i j k h1 h2.
  bprop h1. bprop h2. propb. omega.
Qed.

Fact eq_string_trans :
  forall {s1 s2 s3},
    eq_string s1 s2 = true ->
    eq_string s2 s3 = true ->
    eq_string s1 s3 = true.
Proof.
  unfold eq_string.
  intros s1 s2 s3.
  case (string_dec s1 s2) ; try discriminate. intro e1.
  case (string_dec s2 s3) ; try discriminate. intros e _ _.
  subst. apply eq_string_refl.
Qed.

Fact eq_ind_trans :
  forall {i1 i2 i3},
    eq_ind i1 i2 = true ->
    eq_ind i2 i3 = true ->
    eq_ind i1 i3 = true.
Proof.
  unfold eq_ind.
  intros [i1 n1] [i2 n2] [i3 n3] h1 h2.
  repeat destruct_andb. apply andb_true_intro. split.
  - eapply eq_string_trans ; eassumption.
  - eapply eq_nat_trans ; eassumption.
Qed.

(* Fact eq_term_trans : *)
(*   forall {t u}, eq_term t u = true -> forall {v}, eq_term u v = true -> eq_term t v = true. *)
(* Proof. *)
(*   intro t. *)
(*   induction t using sterm_rect_list. *)
(*   all: intro u ; destruct u ; intro h1 ; cbn in h1 ; try discriminate h1. *)
(*   all: intro v ; destruct v ; intro h2 ; cbn in h2 ; try discriminate h2. *)
(*   all: try (cbn ; repeat destruct_andb ; *)
(*             erewrite_assumptions ; [ reflexivity | eassumption .. ]). *)
(*   - cbn. eapply eq_nat_trans ; eassumption. *)
(*   - cbn. eapply eq_nat_trans ; eassumption. *)
(*   - cbn. eapply eq_ind_trans ; eassumption. *)
(*   - cbn. repeat destruct_andb. apply andb_true_intro. split. *)
(*     + eapply eq_ind_trans ; eassumption. *)
(*     + eapply eq_nat_trans ; eassumption. *)
(*   - cbn. repeat destruct_andb. *)
(*     destruct indn as [i1 n1]. destruct indn1 as [i2 n2]. *)
(*     destruct indn0 as [i3 n3]. *)
(*     assert (eq_nat n1 n2 = true) by (eapply eq_nat_trans ; eassumption). *)
(*     assert (eq_ind i1 i2 = true) by (eapply eq_ind_trans ; eassumption). *)
(*     erewrite_assumptions ; [ idtac | eassumption .. ]. cbn. *)
(*     induction X. *)
(*     + destruct brs0 ; inversion H5. *)
(*       destruct brs1 ; inversion H0. *)
(*       constructor. *)
(*     + destruct brs0 ; inversion H5. *)
(*       destruct brs1 ; inversion H0. cbn. *)
(*       destruct x as [m1 c1]. *)
(*       destruct p1 as [m2 c2]. *)
(*       destruct p0 as [m3 c3]. *)
(*       repeat destruct_andb. rewrite_assumptions. *)
(* Abort. *)


(* Common lemmata *)

Definition max_sort := max.

Lemma max_id :
  forall s, max_sort s s = s.
Proof.
  intro s. unfold max_sort. auto with arith.
Defined.

Definition succ_sort := S.

Lemma max_succ_id :
  forall s, max_sort (succ_sort s) s = succ_sort s.
Proof.
  intro s. unfold max_sort, succ_sort.
  auto with arith.
Defined.

Definition sapp_context (Γ Γ' : scontext) : scontext := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (sapp_context Γ Γ') (at level 25, Γ' at next level, left associativity) : s_scope.

Fact cat_nil :
  forall {Γ}, Γ ,,, [] = Γ.
Proof.
  induction Γ ; easy.
Defined.

Fact nil_cat :
  forall {Γ}, [] ,,, Γ = Γ.
Proof.
  induction Γ ; try easy.
  cbn. f_equal. assumption.
Defined.

Fact length_cat :
  forall {A} {Γ Δ : list A}, #|Γ ++ Δ| = (#|Γ| + #|Δ|)%nat.
Proof.
  intros A Γ. induction Γ ; intro Δ.
  - cbn. reflexivity.
  - cbn. f_equal. apply IHΓ.
Defined.

Fact safe_nth_S :
  forall {A n} {a : A} {l isdecl},
    ∑ isdecl',
      safe_nth (a :: l) (exist _ (S n) isdecl) =
      safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intros a l isdecl.
  - cbn. eexists. reflexivity.
  - eexists. cbn. reflexivity.
Defined.

Lemma eq_safe_nth' :
  forall {Γ : scontext} {n a isdecl isdecl'},
    safe_nth (a :: Γ) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ. induction Γ ; intros n A isdecl isdecl'.
  - easy.
  - destruct n.
    + reflexivity.
    + destruct (@safe_nth_S _ (S n) A (a :: Γ) isdecl')
        as [isecl0 eq].
      rewrite eq.
      destruct (@safe_nth_S _ n a Γ isdecl)
        as [isecl1 eq1].
      rewrite eq1.
      apply IHΓ.
Defined.

Lemma eq_safe_nth :
  forall {Γ n x A isdecl isdecl'},
    safe_nth (Γ ,, svass x A) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ n x A isdecl isdecl'.
  apply eq_safe_nth'.
Defined.

Fact safe_nth_irr :
  forall {A n} {l : list A} {isdecl isdecl'},
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intro l ; destruct l ; try easy ; intros isdecl isdecl'.
  cbn. eapply IHn.
Defined.

Fact safe_nth_cong_irr :
  forall {A n m} {l : list A} {isdecl isdecl'},
    n = m ->
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ m isdecl').
Proof.
  intros A n m l isdecl isdecl' e.
  revert isdecl isdecl'.
  rewrite e. intros isdecl isdecl'.
  apply safe_nth_irr.
Defined.

Fact safe_nth_ge :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n - #|Δ| < #|Γ| },
    n >= #|Δ| ->
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) isdecl').
Proof.
  intros Γ Δ.
  induction Δ ; intros n isdecl isdecl' h.
  - cbn in *. revert isdecl'.
    replace (n - 0) with n by omega.
    intros isdecl'. apply safe_nth_irr.
  - destruct n.
    + cbn in *. inversion h.
    + cbn. apply IHΔ. cbn in *. omega.
Defined.

Definition ge_sub {Γ Δ n} (isdecl : n < #|Γ ,,, Δ|) :
  n >= #|Δ| ->  n - #|Δ| < #|Γ|.
Proof.
  intro h.
  rewrite length_cat in isdecl. omega.
Defined.

Fact safe_nth_ge' :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } (h : n >= #|Δ|),
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) (ge_sub isdecl h)).
Proof.
  intros Γ Δ n isdecl h.
  eapply safe_nth_ge. assumption.
Defined.

Fact safe_nth_lt :
  forall {n Γ Δ} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n < #|Δ| },
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Δ (exist _ n isdecl').
Proof.
  intros n. induction n ; intros Γ Δ isdecl isdecl'.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. reflexivity.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. eapply IHn.
Defined.

(* Copy of global_contexts

   In some cases we just keep the TemplateCoq version (TC).
*)

Record sone_inductive_body := {
  sind_name : ident;
  sind_type : sterm;
  sind_kelim : list sort_family; (* TC *)
  sind_ctors : list (ident * sterm * nat);
  sind_projs : list (ident * sterm)
}.

Record smutual_inductive_body := {
  sind_npars : nat;
  sind_bodies : list sone_inductive_body ;
  sind_universes : universe_context }.

Inductive sglobal_decl :=
| SConstantDecl : kername -> constant_body -> sglobal_decl (* TC *)
| SInductiveDecl : kername -> smutual_inductive_body -> sglobal_decl.

Definition sglobal_declarations := list sglobal_decl.

(* We leave the graph for compatibility.
   Hopefully it isn't too heavy.
 *)
Definition sglobal_context : Type := sglobal_declarations * uGraph.t.

(* Operations for inductives *)

Definition sglobal_decl_ident d :=
  match d with
  | SConstantDecl id _ => id
  | SInductiveDecl id _ => id
  end.

Fixpoint slookup_env (Σ : sglobal_declarations) (id : ident) : option sglobal_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if ident_eq id (sglobal_decl_ident hd) then Some hd
    else slookup_env tl id
  end.


Definition sdeclared_minductive Σ mind decl :=
  slookup_env Σ mind = Some (SInductiveDecl mind decl).

Definition sdeclared_inductive Σ ind univs decl :=
  ∑ decl', (sdeclared_minductive Σ (inductive_mind ind) decl') *
           (univs = decl'.(sind_universes)) *
           (List.nth_error decl'.(sind_bodies) (inductive_ind ind) = Some decl).

Definition sdeclared_constructor Σ cstr univs decl :=
  let '(ind, k) := cstr in
  ∑ decl', (sdeclared_inductive Σ ind univs decl') *
           (List.nth_error decl'.(sind_ctors) k = Some decl).

Definition sinds ind (l : list sone_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => sInd (mkInd ind n) :: aux n
      end
  in aux (List.length l).

Definition inspect {A} (x : A) : { y : A | y = x } := exist _ x eq_refl.
Require Import Equations.NoConfusion.
Equations stype_of_constructor (Σ : sglobal_declarations)
  (c : inductive * nat) (univs : universe_context)
  (decl : ident * sterm * nat)
  (H : sdeclared_constructor Σ c univs decl) : sterm :=
  stype_of_constructor Σ c univs decl H <= inspect (slookup_env Σ (inductive_mind (fst c))) => {
    | exist (Some (SInductiveDecl _ decl')) _ :=
      let '(id, trm, args) := decl in
      substl (sinds (inductive_mind (fst c)) decl'.(sind_bodies)) trm ;
    | exist decl H := !
  }.
Next Obligation.
  subst decl.
  destruct H as [d [H H']].
  destruct H as [decl' [[H'' H''''] H''']].
  unfold sdeclared_minductive in H''. rewrite <- H0 in H''.
  noconf H''.
Qed.
Next Obligation.
  subst decl.
  destruct H as [d [H H']].
  destruct H as [decl' [[H'' H''''] H''']].
  unfold sdeclared_minductive in H''. rewrite <- H0 in H''. discriminate.
Qed.

Fact declared_inductive_eq :
  forall {Σ : sglobal_context} {ind univs1 decl1 univs2 decl2},
    sdeclared_inductive (fst Σ) ind univs1 decl1 ->
    sdeclared_inductive (fst Σ) ind univs2 decl2 ->
    decl1 = decl2.
Proof.
  intros Σ ind univs1 decl1 univs2 decl2 is1 is2.
  destruct is1 as [d1 [[h1 i1] j1]].
  destruct is2 as [d2 [[h2 i2] j2]].
  unfold sdeclared_minductive in h1, h2.
  rewrite h1 in h2. inversion h2. subst.
  rewrite j1 in j2. now inversion j2.
Defined.

Fact stype_of_constructor_irr :
  forall {Σ ind n univs decl}
    {is1 is2 : sdeclared_constructor Σ (ind, n) univs decl},
    stype_of_constructor Σ (ind, n) univs decl is1 =
    stype_of_constructor Σ (ind, n) univs decl is2.
Proof.
  intros Σ ind n univs decl is1 is2.
  funelim (stype_of_constructor Σ (ind, n) univs decl is1) ; try bang.
  funelim (stype_of_constructor Σ (ind, n) univs decl is2) ; try bang.
  reflexivity.
Defined.

Fact stype_of_constructor_eq :
  forall {Σ ind n u1 u2 d1 d2}
    {is1 : sdeclared_constructor Σ (ind, n) u1 d1}
    {is2 : sdeclared_constructor Σ (ind, n) u2 d2},
    stype_of_constructor Σ (ind, n) u1 d1 is1 =
    stype_of_constructor Σ (ind, n) u2 d2 is2.
Proof.
  intros Σ ind n u1 u2 d1 d2 is1 is2.
  assert (hh : (u1 = u2) * (d1 = d2)).
  { destruct is1 as [? [[d1' [[hd1' ?] hn1']] hn1]].
    destruct is2 as [? [[d2' [[hd2' ?] hn2']] hn2]].
    unfold sdeclared_minductive in *.
    rewrite hd1' in hd2'. inversion hd2'. subst.
    rewrite hn1' in hn2'. inversion hn2'. subst.
    split ; [ reflexivity |].
    rewrite hn1 in hn2. inversion hn2. subst.
    reflexivity.
  }
  destruct hh. subst.
  apply stype_of_constructor_irr.
Defined.

(* Lifting of context *)

Definition lift_decl n k d : scontext_decl :=
  {| sdecl_name := sdecl_name d ;
     sdecl_body := option_map (lift n k) (sdecl_body d) ;
     sdecl_type := lift n k (sdecl_type d)
  |}.

Fixpoint lift_context n Γ : scontext :=
  match Γ with
  | nil => nil
  | A :: Γ => (lift_decl n #|Γ| A) :: (lift_context n Γ)
  end.

Fact lift_decl0 :
  forall {d k}, lift_decl 0 k d = d.
Proof.
  intros d k.
  destruct d as [x b A].
  unfold lift_decl. cbn. rewrite lift00. f_equal.
  destruct b.
  - cbn. rewrite lift00. reflexivity.
  - reflexivity.
Defined.

Fact lift_context0 :
  forall {Γ}, lift_context 0 Γ = Γ.
Proof.
  intro Γ. induction Γ.
  - reflexivity.
  - cbn. rewrite lift_decl0. rewrite IHΓ. reflexivity.
Defined.

Fact lift_decl_svass :
  forall na A n k,
    lift_decl n k (svass na A) = svass na (lift n k A).
Proof.
  intros na A n k.
  reflexivity.
Defined.

Fact lift_context_length :
  forall {k Ξ}, #|lift_context k Ξ| = #|Ξ|.
Proof.
  intros k Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_lift_context :
  forall {Γ Δ : scontext} {n isdecl isdecl'},
    sdecl_type (safe_nth (lift_context #|Γ| Δ) (exist _ n isdecl)) =
    lift #|Γ| (#|Δ| - n - 1) (sdecl_type (safe_nth Δ (exist _ n isdecl'))).
Proof.
  intros Γ Δ. induction Δ.
  - cbn. easy.
  - intro n. destruct n ; intros isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Fact lift_context_ex :
  forall {Δ Ξ : scontext} {n isdecl isdecl'},
    lift0 (S n) (sdecl_type (safe_nth (lift_context #|Δ| Ξ) (exist _ n isdecl))) =
    lift #|Δ| #|Ξ| (lift0 (S n) (sdecl_type (safe_nth Ξ (exist _ n isdecl')))).
Proof.
  intros Δ Ξ n isdecl isdecl'.
  erewrite safe_nth_lift_context.
  rewrite <- liftP2 by omega.
  cbn.
  replace (S (n + (#|Ξ| - n - 1)))%nat with #|Ξ|.
  - reflexivity.
  - revert n isdecl isdecl'. induction Ξ ; intros n isdecl isdecl'.
    + cbn. easy.
    + cbn. f_equal.
      destruct n.
      * cbn. omega.
      * cbn. apply IHΞ.
        -- cbn in *. omega.
        -- cbn in *. omega.
Defined.

(* Substitution in context *)

Definition subst_decl n u d : scontext_decl :=
  {| sdecl_name := sdecl_name d ;
     sdecl_body := option_map (subst u n) (sdecl_body d) ;
     sdecl_type := (sdecl_type d){ n := u }
  |}.

Fixpoint subst_context u Δ :=
  match Δ with
  | nil => nil
  | A :: Δ => (subst_decl #|Δ| u A) :: (subst_context u Δ)
  end.

Fact subst_decl_svass :
  forall na A n u,
    subst_decl n u (svass na A) = svass na (A{ n := u }).
Proof.
  intros na A n u.
  reflexivity.
Defined.

Fact subst_context_length :
  forall {u Ξ}, #|subst_context u Ξ| = #|Ξ|.
Proof.
  intros u Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_subst_context :
  forall {Δ : scontext} {n u isdecl isdecl'},
    sdecl_type (safe_nth (subst_context u Δ) (exist _ n isdecl)) =
    (sdecl_type (safe_nth Δ (exist _ n isdecl'))) { #|Δ| - S n := u }.
Proof.
  intro Δ. induction Δ.
  - cbn. easy.
  - intro n. destruct n ; intros u isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.
From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import util SAst SInduction SLiftSubst Equality.

Definition scontext := list sterm.

Definition ssnoc (Γ : scontext) (d : sterm) := d :: Γ.

Notation " Γ ,, d " := (ssnoc Γ d) (at level 20, d at next level) : s_scope.
Delimit Scope s_scope with s.

Record squash (A : Set) : Prop := { _ : A }.

(* Named list of terms
   (to be used in the *reverse* order when compared to contexts)
 *)
Definition nctx := list (name * sterm).

Definition nlctx : nctx -> scontext := rev_map snd.

(* The idea is if Γ ⊢ T then ⊢ Prods Γ T *)
Fixpoint Prods (Γ : nctx) (T : sterm) : sterm :=
  match Γ with
  | (nx,A) :: Γ => sProd nx A (Prods Γ T)
  | [] => T
  end.

(* If Γ ⊢ t : T then ⊢ Lams Γ T t : Prods Γ T *)
(* Fixpoint Lams (Γ : nctx) (T t : sterm) : sterm := *)
(*   match Γ with *)
(*   | (nx,A) :: Γ => sLambda nx A (Prods Γ T) (Lams Γ T t) *)
(*   | [] => t *)
(*   end. *)

(* Definition lift_nctx n k (L : nctx) := *)
(*   map_i (fun i '(nx,A) => (nx, lift n (k+i) A)) L. *)

Definition lift_nctx n k (L : nctx) :=
  map_i_aux (fun i '(nx,A) => (nx, lift n i A)) k L.

Definition subst_nctx u (L : nctx) :=
  map_i (fun i '(nx, A) => (nx, A{ i := u })) L.

Definition substn_nctx u n (L : nctx) :=
  map_i_aux (fun i '(nx, A) => (nx, A{ i := u })) n L.

(* If ⊢ f : Prods Γ T and ⊢ l : Γ then ⊢ Apps f Γ T l : T[l] *)
Fixpoint Apps (f : sterm) (Γ : nctx) (T : sterm) (l : list sterm) : sterm :=
  match Γ, l with
  | (nx,A) :: Γ, u :: l =>
    Apps (sApp f A (Prods Γ T) u) (subst_nctx u Γ) (T{ #|Γ| := u }) l
  | _,_ => f
  end.

(* Decomposing a term by removing Products in head *)
Fixpoint decompose_Prods (t : sterm) : nctx * sterm :=
  match t with
  | sProd nx A B =>
    let '(Γ, T) := decompose_Prods B in
    ((nx, A) :: Γ, T)
  | _ => ([], t)
  end.

Fact decompose_Prods_spec :
  forall {t},
    let '(Γ, u) := decompose_Prods t in
    t = Prods Γ u.
Proof.
  intros t.
  induction t.
  all: try (cbn ; reflexivity).
  cbn. rewrite <- IHt2. reflexivity.
Defined.

Fact Prods_inj :
  forall {Γ A Δ B},
    Prods Γ A = Prods Δ B ->
    #|Γ| = #|Δ| ->
    (Γ = Δ) * (A = B).
Proof.
  intros Γ. induction Γ as [| [nx T'] Γ ih ] ; intros A Δ B eq hl.
  - destruct Δ ; cbn in hl ; try discriminate hl.
    cbn in eq. split ; auto.
  - destruct Δ as [| [ny T] Δ] ; cbn in hl ; try discriminate hl.
    inversion hl as [ hl' ].
    cbn in eq. inversion eq. subst.
    destruct ih with (1 := H2) (2 := hl'). subst.
    split ; auto.
Defined.

(* isapp u f l means that u is actually f applied to
   the list of arguments l (in the reverse order).
*)
Inductive isapp : sterm -> sterm -> list sterm -> Type :=
| isapp_refl t : isapp t t []
| isapp_app u f l A B v :
    isapp u f l ->
    isapp (sApp u A B v) f (v :: l).

Lemma dec_ind :
  forall ind t, dec (∑ l, isapp t (sInd ind) l).
Proof.
  intros ind t.
  induction t.
  all: try (right ; intros [l bot] ; inversion bot ; fail).
  - destruct IHt1 as [[l h] | h].
    + left. exists (t4 :: l). constructor. assumption.
    + right. intros [l bot]. inversion bot. subst.
      apply h. eexists. eassumption.
  - destruct (inductive_dec ind0 ind).
    + subst. left. exists []. constructor.
    + right. intros [l bot]. inversion bot.
      apply n. auto.
Defined.


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

Definition sapp_context (Γ Γ' : scontext) : scontext := (Γ' ++ Γ).
Notation " Γ  ,,, Γ' " :=
  (sapp_context Γ Γ')
  (at level 25, Γ' at next level, left associativity) : s_scope.

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

Fact nlctx_cat :
  forall {L1 L2},
    nlctx (L1 ++ L2) = nlctx L1 ,,, nlctx L2.
Proof.
  intros L1 L2. unfold nlctx, sapp_context.
  apply rev_map_app.
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
  forall {Γ n A isdecl isdecl'},
    safe_nth (Γ ,, A) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ n A isdecl isdecl'.
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
  sind_ctors : list (ident * sterm * nat * sterm);
  sind_projs : list (ident * sterm);
  (* I add the following, to recover info later. *)
  sind_indices : nctx;
  sind_sort : sort
}.

Record smutual_inductive_body := {
  sind_params : nctx ; (* The context of parameters, replaces ind_npar by its
                          length *)
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
  ∑ decl',
    (sdeclared_minductive Σ (inductive_mind ind) decl') *
    (univs = decl'.(sind_universes)) *
    (List.nth_error decl'.(sind_bodies) (inductive_ind ind) = Some decl).

Definition sdeclared_constructor Σ cstr univs decl :=
  let '(ind, k) := cstr in
  ∑ decl', (sdeclared_inductive Σ ind univs decl') *
           (List.nth_error decl'.(sind_ctors) k = Some decl).

Lemma declared_inductive_constructor :
  forall {Σ ind univs decl},
    sdeclared_inductive Σ ind univs decl ->
    forall {n d},
      nth_error decl.(sind_ctors) n = Some d ->
      sdeclared_constructor Σ (ind, n) univs d.
Proof.
  intros Σ ind univs decl isdecl n d h.
  exists decl. split ; assumption.
Defined.

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
  (decl : ident * sterm * nat * sterm)
  (H : sdeclared_constructor Σ c univs decl) : sterm :=
  stype_of_constructor Σ c univs decl H <= inspect (slookup_env Σ (inductive_mind (fst c))) => {
    | exist (Some (SInductiveDecl _ decl')) _ :=
      let '(id, trm, args, _) := decl in
      substl (sinds (inductive_mind (fst c)) decl'.(sind_bodies)) trm ;
    | exist decl H := !
  }.
Next Obligation.
  subst decl.
  destruct H as [d [H H']].
  destruct H as [decl' [[H'' H''''] H''']].
  unfold sdeclared_minductive in H''. rewrite <- H0 in H''.
  noconf H''.
Defined.
Next Obligation.
  subst decl.
  destruct H as [d [H H']].
  destruct H as [decl' [[H'' H''''] H''']].
  unfold sdeclared_minductive in H''. rewrite <- H0 in H''. discriminate.
Defined.

(* We add one version that still substitutes the inductive types but keeps the
   parameters in the context.
 *)
Equations paramless_type_of_constructor (Σ : sglobal_declarations)
  (c : inductive * nat) (univs : universe_context)
  (decl : ident * sterm * nat * sterm)
  (H : sdeclared_constructor Σ c univs decl) : sterm :=
  paramless_type_of_constructor Σ c univs decl H
  <= inspect (slookup_env Σ (inductive_mind (fst c))) => {
    | exist (Some (SInductiveDecl _ decl')) _ :=
      let '(id, _, args, trm) := decl in
      substln (sinds (inductive_mind (fst c)) decl'.(sind_bodies))
              #|decl'.(sind_params)| trm ;
    | exist decl H := !
  }.
Next Obligation.
  subst decl.
  destruct H as [d [H H']].
  destruct H as [decl' [[H'' H''''] H''']].
  unfold sdeclared_minductive in H''. rewrite <- H0 in H''.
  noconf H''.
Defined.
Next Obligation.
  subst decl.
  destruct H as [d [H H']].
  destruct H as [decl' [[H'' H''''] H''']].
  unfold sdeclared_minductive in H''. rewrite <- H0 in H''. discriminate.
Defined.

Inductive even (x : bool) : nat -> Type :=
| evenO : even x 0
| evenS n : odd true n -> even x (S n)

with odd (x : bool) : nat -> Type :=
| oddS n : even true n -> odd x (S n).

Quote Recursively Definition event := even.

Scheme even_rect' := Induction for even Sort Type.

Quote Recursively Definition ter := even_rect'.

(* [ sRel (start + count) ; ... ; sRel start ] *)
Fixpoint lrel start count :=
  match count with
  | 0 => []
  | S n => sRel (start + n)%nat :: lrel start n
  end.

(* [ sRel start ; ... ; sRel (start + count) ] *)
(* Fixpoint lrel start count := *)
(*   match count with *)
(*   | 0 => [] *)
(*   | S n => sRel start :: lrel (S start) n *)
(*   end. *)

(* TODO MOVE *)
Definition forall_list {A B} l :
  (forall (x : A) n, nth_error l n = Some x -> B) ->
  list B.
Proof.
  intros f. induction l.
  - exact [].
  - refine (_ :: _).
    + apply (f a 0). cbn. reflexivity.
    + apply IHl. intros x n h.
      apply (f x (S n)). cbn. assumption.
Defined.

Equations indpars Σ ind univs decl
          (isdecl : sdeclared_inductive Σ ind univs decl)
  : nctx :=
  indpars Σ ind univs decl isdecl
  <= inspect (slookup_env Σ (inductive_mind ind)) => {
  | exist (Some (SInductiveDecl _ d)) _ := d.(sind_params) ;
  | exist d' H := !
  }.
Next Obligation.
  destruct isdecl as [? [[hm ?] ?]].
  unfold sdeclared_minductive in hm.
  rewrite <- H in hm. discriminate hm.
Defined.
Next Obligation.
  destruct isdecl as [? [[hm ?] ?]].
  unfold sdeclared_minductive in hm.
  rewrite <- H in hm. discriminate hm.
Defined.

Arguments indpars {Σ ind univs decl} isdecl.

Fact indpars_def :
  forall {Σ ind univs decl d}
    (h1 : sdeclared_minductive Σ (inductive_mind ind) d)
    (h2 : univs = sind_universes d)
    (h3 : nth_error (sind_bodies d) (inductive_ind ind) = Some decl),
    indpars {| pi1 := d; pi2 := (h1, h2, h3) |} = d.(sind_params).
Proof.
  intros Σ ind univs decl d h1 h2 h3.
  funelim (indpars {| pi1 := d; pi2 := (h1, h2, h3) |}) ; try bang.
  unfold sdeclared_minductive in h1. rewrite <- H in h1.
  inversion h1. subst. reflexivity.
Defined.

(* Instance of an inductive in context nlctx (pars ++ indices) *)
Definition indInst {Σ ind univs decl} isdecl :=
  let si := decl.(sind_sort) in
  let pars := @indpars Σ ind univs decl isdecl in
  let indices := decl.(sind_indices) in
  (* Granted, the two following lines could easily mix into one. *)
  let irels := lrel 0 #|indices| in
  let prels := lrel #|indices| #|pars| in
  (Apps (sInd ind) (pars ++ indices) (sSort si) (prels ++ irels)).

(* Type of the predicate of the eliminator (sElim ind s) *)
Definition elimPty {Σ ind univs decl} isdecl s :=
  let si := decl.(sind_sort) in
  let indices := decl.(sind_indices) in
  let indinst := @indInst Σ ind univs decl isdecl in
  Prods (indices ++ [ (nAnon, indinst) ]) (sSort s).

(* List of types of paramless constructors, each in context [pars] *)
Definition pl_ctors_ty {Σ ind univs decl} isdecl :=
  forall_list decl.(sind_ctors) (fun cd i h =>
    paramless_type_of_constructor
      Σ (ind, i) univs cd
      (declared_inductive_constructor isdecl h)
   ).

(* Deduce the applied predicate corresponding to an inductive instance.
   If [ty] is a type in context [pars,, elimPty ,, Γ]
   with #|Γ| = off and isapp ty (sInd ind) l
   then the result is a type in this context extended by [ty].
 *)
Definition elimPapp {Σ ind univs decl} isdecl s l off :=
  let pars := @indpars Σ ind univs decl isdecl in
  let indices := decl.(sind_indices) in
  let indices := lift_nctx (S (S off)) 0 indices in
  let indinst := lift (S (S off)) #|indices| (indInst isdecl) in
  let l := rev l in
  let ipars := firstn #|pars| l in
  let iindices := skipn #|pars| l in
  let iindices := map (lift 1 0) iindices in
  Apps (sRel (S off))
       (indices ++ [ (nAnon, indinst) ])
       (sSort s)
       (iindices ++ [ sRel 0 ]).

Equations type_of_elim Σ ind univs decl (s : sort)
  (isdecl : sdeclared_inductive Σ ind univs decl) : sterm :=
  type_of_elim Σ ind univs decl s isdecl
  <= inspect (slookup_env Σ (inductive_mind ind)) => {
  | exist (Some (SInductiveDecl _ d)) _ :=
    let pars := d.(sind_params) in
    let indices := decl.(sind_indices) in
    (* Granted, the two following lines could easily mix into one. *)
    let irels := lrel 0 #|indices| in
    let prels := lrel #|indices| #|pars| in
    let si := decl.(sind_sort) in
    let indinst := indInst isdecl in
    let Pty := elimPty isdecl s in
    let P := (nNamed "P", Pty) in
    (* The list of paramless constructor types. *)
    let pcs := pl_ctors_ty isdecl in
    (* The list of arguments of the eliminator *)
    let fl :=
      map_i (fun i ty =>
        let '(l, T) := decompose_Prods ty in
        let '(l',off) :=
          fold_left
            (fun '(acc, off) '(nx, ty) =>
               match dec_ind ind ty with
               | inleft {| pi1 := l ; pi2 := h |} =>
                 (* Have an operation for this. *)
                 (* First we need to decompose the list in two. *)
                 let l := rev l in
                 let ipars := firstn #|pars| l in
                 let iindices := skipn #|pars| l in
                 let apP :=
                   Apps (sRel off)
                        (indices ++ [ (nAnon, indinst) ])
                        (sSort s)
                        iindices
                        (* We need to get the constructor itself
                           an apply it to the right things.
                         *)
                        (* (iindices ++ [ ?? ]) *)
                 in
                 let apP := (nAnon, lift0 off apP) in
                 let t := (nx, lift0 off ty) in
                 (apP :: t :: acc, S off)
               | inright _ =>
                 ((nx, lift0 off ty) :: acc, off)
               end
            ) l ([], 0) (* Maybe it should be one to account for P? *)
        in
        (* Do the same operation on T *)
        let T' :=
          match dec_ind ind T with
          | inleft {| pi1 := l ; pi2 := h |} =>
            T
          | inright _ => T
          end
        in
        lift0 i (Prods (rev l') (lift0 off T'))
      ) pcs
    in
    let fl := map (fun ty => (nNamed "f", ty)) fl in
    let irels := lrel 0 #|indices| in
    let prels := lrel (1 + #|indices| + #|fl|)%nat #|pars| in
    let indinst :=
      (Apps (sInd ind) (pars ++ indices) (sSort si) (prels ++ irels))
    in
    let predinst :=
      Apps (sRel (1 + #|indices| + #|fl|))%nat
           (indices ++ [ (nAnon, indinst) ]) (sSort s)
           (lrel 0 (S #|indices|))
    in
    Prods (pars ++ P :: fl ++ indices ++ [ (nAnon, indinst) ]) predinst ;
  | exist decl' H := !
  }.
Next Obligation.
  destruct isdecl as [? [[hm ?] ?]].
  unfold sdeclared_minductive in hm.
  rewrite <- H in hm. discriminate hm.
Defined.
Next Obligation.
  destruct isdecl as [? [[hm ?] ?]].
  unfold sdeclared_minductive in hm.
  rewrite <- H in hm. discriminate hm.
Defined.

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

Fact declared_inductive_dec Σ ind :
  dec (∑ univs decl, sdeclared_inductive Σ ind univs decl).
Proof.
  case_eq (slookup_env Σ (inductive_mind ind)).
  - intros d mdecl.
    destruct d as [? ? | mind d].
    + right. intros [_ [decl [decl' [[bot _] _]]]].
      unfold sdeclared_minductive in bot.
      rewrite bot in mdecl. inversion mdecl.
    + case_eq (nth_error (sind_bodies d) (inductive_ind ind)).
      * intros decl h. left.
        exists (sind_universes d), decl, d.
        unfold sdeclared_minductive.
        repeat split ; try assumption.
        clear - mdecl.
        induction Σ.
        -- cbn in mdecl. discriminate.
        -- cbn.
           case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident a)).
           ++ intros e. cbn in mdecl. rewrite e in mdecl.
              destruct a.
              ** cbn in *. inversion mdecl.
              ** cbn in *.
                 case_eq (string_dec (inductive_mind ind) k).
                 --- intros. subst. inversion mdecl. subst. reflexivity.
                 --- intros neq eq. unfold ident_eq in e. rewrite eq in e.
                     discriminate.
           ++ intros e. cbn in mdecl. rewrite e in mdecl.
              apply IHΣ. assumption.
      * intros h. right.
        intros [univs [decl [decl' [[mdecl' _] hnth]]]].
        unfold sdeclared_minductive in mdecl'.
        rewrite mdecl' in mdecl. inversion mdecl. subst.
        rewrite hnth in h. discriminate.
  - intro h.
    right. intros [univs [decl [decl' [[mdecl' _] hnth]]]].
    unfold sdeclared_minductive in mdecl'. rewrite mdecl' in h.
    discriminate.
Defined.

Fact declared_constructor_dec Σ ind i :
  dec (∑ univs decl, sdeclared_constructor Σ (ind, i) univs decl).
Proof.
  case (declared_inductive_dec Σ ind).
  - intros [univs [decl isdecl]].
    case_eq (nth_error (sind_ctors decl) i).
    + intros d hi.
      left. exists univs, d, decl. split ; assumption.
    + intros h. right.
      intros [u [d [dd [[d' [[md' _] hd']] bot]]]].
      destruct isdecl as [d'' [[md'' _] hd'']].
      unfold sdeclared_minductive in md', md''.
      rewrite md'' in md'. clear md''. inversion md'. subst.
      rewrite hd'' in hd'. clear hd''. inversion hd'. subst.
      rewrite h in bot. discriminate.
  - intros ndecl. right.
    intros [u [d [dd [[d' [[md' ?] hd']] bot]]]].
    apply ndecl.
    exists u, dd, d'. repeat split ; assumption.
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

Fixpoint lift_context n Γ : scontext :=
  match Γ with
  | nil => nil
  | A :: Γ => (lift n #|Γ| A) :: (lift_context n Γ)
  end.

Fact lift_context0 :
  forall {Γ}, lift_context 0 Γ = Γ.
Proof.
  intro Γ. induction Γ.
  - reflexivity.
  - cbn. rewrite lift00. rewrite IHΓ. reflexivity.
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
    safe_nth (lift_context #|Γ| Δ) (exist _ n isdecl) =
    lift #|Γ| (#|Δ| - n - 1) (safe_nth Δ (exist _ n isdecl')).
Proof.
  intros Γ Δ. induction Δ.
  - cbn. easy.
  - intro n. destruct n ; intros isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Fact lift_context_ex :
  forall {Δ Ξ : scontext} {n isdecl isdecl'},
    lift0 (S n) (safe_nth (lift_context #|Δ| Ξ) (exist _ n isdecl)) =
    lift #|Δ| #|Ξ| (lift0 (S n) (safe_nth Ξ (exist _ n isdecl'))).
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

Fixpoint subst_context u Δ :=
  match Δ with
  | nil => nil
  | A :: Δ => (A{ #|Δ| := u }) :: (subst_context u Δ)
  end.

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
    (safe_nth (subst_context u Δ) (exist _ n isdecl)) =
    (safe_nth Δ (exist _ n isdecl')) { #|Δ| - S n := u }.
Proof.
  intro Δ. induction Δ.
  - cbn. easy.
  - intro n. destruct n ; intros u isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Definition substln_context l Ξ :=
  List.fold_left (fun Γ u => subst_context u Γ) l Ξ.
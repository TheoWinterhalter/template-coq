(* -*- coq-prog-args: ("-emacs" "-type-in-type") -*- *)

(* Example of the whole translation *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
From Translation Require Import SAst SLiftSubst SCommon ITyping
                                ITypingLemmata ITypingAdmissible XTyping
                                Translation Reduction FinalTranslation
                                ExamplesUtil.

Open Scope string_scope.

(*! EXAMPLE 1:
    λ A B e x ⇒ x : ∀ (A B : Type), A = B → A → B
    It uses reflection to be well-typed.
    It gets translated to
    λ A B e x ⇒ transport e x : ∀ (A B : Type), A = B → A → B.
*)

(* We begin with an ETT derivation *)

Definition tyl :=
  [ sSort 0 ;
    sSort 0 ;
    sEq (sSort 0) (sRel 1) (sRel 0) ;
    sRel 2 ;
    sRel 2
  ].

Definition ty : sterm := multiProd tyl.

Definition tm : sterm := multiLam tyl (sRel 0).

Fact tmty : Σi ;;; [] |-x tm : ty.
Proof.
  eapply type_multiLam.
  - constructor.
  - econstructor.
    + eapply type_Sort. constructor.
    + econstructor.
      * eapply type_Sort.
        repeat econstructor.
      * econstructor.
        -- eapply type_Eq.
           ++ repeat constructor.
              ** repeat econstructor.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
        -- econstructor.
           ++ refine (type_Rel _ _ _ _ _).
              ** repeat econstructor.
              ** cbn. omega.
           ++ econstructor.
              ** refine (type_Rel _ _ _ _ _).
                 --- repeat econstructor.
                 --- cbn. omega.
              ** eapply type_conv''.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ repeat econstructor.
                     +++ cbn. omega.
                 --- cbn. eapply reflection.
                     instantiate (2 := sRel 1).
                     refine (type_Rel _ _ _ _ _).
                     +++ repeat econstructor.
                     +++ cbn. omega.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ repeat econstructor.
                     +++ cbn. omega.
  Unshelve.
  all: cbn; omega.
Defined.

(* Then we translate this ETT derivation to get an ITT term *)

Definition itt_tm : sterm.
  destruct (type_translation tmty istrans_nil) as [A [t h]].
  exact t.
Defined.

Definition itt_tm' := ltac:(let t := eval lazy in itt_tm in exact t).

(* We simplify the produced term *)

Definition red_itt_tm := reduce itt_tm'.

Definition red_itt_tm' := ltac:(let t := eval lazy in red_itt_tm in exact t).

Definition tc_red_tm : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm'.

Definition tc_red_tm' := ltac:(let t := eval lazy in tc_red_tm in exact t).

Make Definition coq_red_tm :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 2:
    λ A x ⇒ x : ∀ (A : Type), A → A
    It gets translated to itself.
*)

Definition tyl0 :=
  [ sSort 0 ;
    sRel 0 ;
    sRel 1
  ].

Definition ty0 : sterm := multiProd tyl0.

Definition tm0 : sterm := multiLam tyl0 (sRel 0).

Lemma tmty0 : Σi ;;; [] |-x tm0 : ty0.
Proof.
  eapply type_multiLam.
  - constructor.
  - econstructor.
    + repeat econstructor.
    + econstructor.
      * refine (type_Rel _ _ _ _ _).
        -- repeat econstructor.
        -- cbn. omega.
      * econstructor.
        -- refine (type_Rel _ _ _ _ _).
           ++ repeat econstructor.
           ++ cbn. omega.
        -- refine (type_Rel _ _ _ _ _).
           ++ repeat econstructor.
           ++ cbn. omega.
  Unshelve. all: cbn; omega.
Defined.

Definition itt_tm0 : sterm.
  destruct (type_translation tmty0 istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_tm0' := ltac:(let t := eval lazy in itt_tm0 in exact t).

Definition red_itt_tm0 := reduce itt_tm0.

Definition red_itt_tm0' := ltac:(let t := eval lazy in red_itt_tm0 in exact t).

Definition tc_red_tm0 : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_itt_tm0'.

Definition tc_red_tm0' := ltac:(let t := eval lazy in tc_red_tm0 in exact t).

Make Definition coq_red_tm0 :=
  ltac:(
    let t := eval lazy in
             (match tc_red_tm0' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).


(*! EXAMPLE 3:
    nat
    It gets translated to itself.
*)

Lemma natty : Σi ;;; [] |-x sAx "nat" : sSort 0.
Proof.
  ettcheck.
Defined.

Definition itt_nat : sterm.
  destruct (type_translation natty istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_nat' := ltac:(let t := eval lazy in itt_nat in exact t).

Definition red_nat := reduce itt_nat'.

Definition red_nat' := ltac:(let t := eval lazy in red_nat in exact t).

Definition tc_red_nat : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_nat'.

Definition tc_red_nat' := ltac:(let t := eval lazy in tc_red_nat in exact t).

Make Definition coq_nat :=
  ltac:(
    let t := eval lazy in
             (match tc_red_nat' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 3':
    zero
    It gets translated to itself.
*)

Lemma zeroty : Σi ;;; [] |-x sAx "zero" : sAx "nat".
Proof.
  ettcheck.
Defined.

Definition itt_zero : sterm.
  destruct (type_translation zeroty istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_zero' := ltac:(let t := eval lazy in itt_zero in exact t).

Definition red_zero := reduce itt_zero'.

Definition red_zero' := ltac:(let t := eval lazy in red_zero in exact t).

Definition tc_red_zero : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_zero'.

Definition tc_red_zero' := ltac:(let t := eval lazy in tc_red_zero in exact t).

Make Definition coq_zero :=
  ltac:(
    let t := eval lazy in
             (match tc_red_zero' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).

(*! EXAMPLE 3'':
    succ zero
    It gets translated to itself.
*)

Definition sNat := sAx "nat".
Definition sZero := sAx "zero".
Definition sSucc := sAx "succ".

Definition sOne := sApp sSucc sNat sNat sZero.

Lemma onety : Σi ;;; [] |-x sOne : sNat.
Proof.
  unfold sOne, sNat, sZero, sSucc.
  ettcheck.
Defined.

Definition itt_one : sterm.
  destruct (type_translation onety istrans_nil) as [A [t [_ h]]].
  exact t.
Defined.

Definition itt_one' := ltac:(let t := eval lazy in itt_one in exact t).

Definition red_one := reduce itt_one'.

Definition red_one' := ltac:(let t := eval lazy in red_one in exact t).

Definition tc_red_one : tsl_result term :=
  tsl_rec (2 ^ 18) Σ [] red_one'.

Definition tc_red_one' := ltac:(let t := eval lazy in tc_red_one in exact t).

Make Definition coq_one :=
  ltac:(
    let t := eval lazy in
             (match tc_red_one' with
              | Success t => t
              | _ => tSort Universe.type0
              end)
      in exact t
  ).
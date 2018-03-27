(* Utility *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.

Set Primitive Projections.
Open Scope type_scope.

Record pp_sigT {A : Type} (P : A -> Type) : Type :=
  {
    pi1 : A;
    pi2 : P pi1
  }.

(* Preamble *)
Notation "'∑'  x .. y , P" := (pp_sigT (fun x => .. (pp_sigT (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

Record pp_prod (A B : Type) : Type := mk_pp_prod
  {
    pi1_ : A;
    pi2_ : B
  }.

Arguments mk_pp_prod {_ _} _ _.


Notation "x * y" := (pp_prod x y) : type_scope.

Definition fst {A B} (p : A * B) := pi1_ A B p.
Definition snd {A B} (p : A * B) := pi2_ A B p.

Notation "( x , y , .. , z )" :=
  (mk_pp_prod .. (mk_pp_prod x y) .. z) : type_scope.



Ltac splits n :=
  match n with
  | S ?n => split ; [ splits n |]
  | _ => idtac
  end.

Ltac split_hyp :=
  match goal with
  | H : _ * _ |- _ => destruct H
  end.

Ltac split_hyps :=
  repeat split_hyp.

Ltac splits_one h :=
  match type of h with
  | _ * _ => let h1 := fresh "h" in
            let h2 := fresh "h" in
            destruct h as [h1 h2] ;
            splits_one h1 ;
            splits_one h2
  | _ => idtac
  end.



Ltac bprop' H H' :=
  match type of H with
  | (?n <=? ?m) = true => pose proof (leb_complete _ _ H) as H'
  | (?n <=? ?m) = false => pose proof (leb_complete_conv _ _ H) as H'
  | (?n <? ?m) = true => pose proof (proj1 (Nat.ltb_lt n m) H) as H'
  | (?n <? ?m) = false => pose proof (proj1 (Nat.ltb_ge n m) H) as H'
  | (?x ?= ?y) = Gt => pose proof (nat_compare_Gt_gt _ _ H) as H'
  | (?x ?= ?y) = Eq => pose proof (Nat.compare_eq _ _ H) as H'
  | (?x ?= ?y) = Lt => pose proof (nat_compare_Lt_lt _ _ H) as H'
  | (?x =? ?y) = true => pose proof (beq_nat_true x y H) as H'
  | (?x =? ?y) = false => pose proof (beq_nat_false x y H) as H'
  end.

(* Doesn't work. :( *)
Tactic Notation "brop" constr(H) "as" constr(H') := bprop' H H'.

Tactic Notation "bprop" constr(H) := let H' := fresh H in bprop' H  H'.

Ltac propb :=
  match goal with
  | |- (_ <=? _) = true => apply leb_correct
  | |- (_ <=? _) = false => apply leb_correct_conv
  | |- (_ <? _) = true => apply Nat.ltb_lt
  | |- (_ <? _) = false => apply Nat.ltb_ge
  | |- (_ ?= _) = Lt => apply Nat.compare_lt_iff
  | |- (_ ?= _) = Eq => apply Nat.compare_eq_iff
  | |- (_ ?= _) = Gt => apply Nat.compare_gt_iff
  | |- (_ =? _) = true => apply Nat.eqb_eq
  | |- (_ =? _) = false => apply beq_nat_false
  end.
(*! Common syntax to ITT and ETT *)

From Template Require Import Ast.
From Translation Require Import util.

Definition sort := nat.

Inductive sterm : Type :=
| sRel (n : nat)
| sSort (s : sort)
| sProd (nx : name) (A B : sterm)
| sLambda (nx : name) (A B t : sterm)
| sApp (u A B v : sterm)
(* Homogenous equality *)
| sEq (A u v : sterm)
| sRefl (A u : sterm)
| sJ (A u P w v p : sterm)
| sTransport (T1 T2 p t : sterm)
(* Heterogenous equality *)
| sHeq (A a B b : sterm)
| sHeqToEq (p : sterm)
| sHeqConstr (A B a b p q : sterm)
| sHeqRefl (A a : sterm) (* TODO2 REMOVE *)
| sHeqSym (p : sterm) (* TODO REMOVE *)
| sHeqTrans (p q : sterm) (* TODO REMOVE *)
| sHeqTransport (p t : sterm) (* TODO REMOVE *)
| sCongProd (B1 B2 pA pB : sterm) (* TODO REMOVE *)
| sCongLambda (B1 B2 t1 t2 pA pB pt : sterm) (* TODO REMOVE *)
| sCongApp (B1 B2 pu pA pB pv : sterm) (* TODO REMOVE *)
| sCongEq (pA pu pv : sterm) (* TODO REMOVE *)
| sCongRefl (pA pu : sterm) (* TODO REMOVE *)
| sEqToHeq (p : sterm) (* TODO2 REMOVE *)
| sHeqTypeEq (A B p : sterm)
| sHeqTermEq (A B a b p : sterm)
(* Packing *)
| sPack (A1 A2 : sterm)
| sProjT1 (p : sterm)
| sProjT2 (p : sterm)
| sProjTe (p : sterm)
(* Inductives *)
| sInd (ind : inductive)
| sConstruct (ind : inductive) (n : nat)
| sCase (indn : inductive * nat) (p c : sterm) (brs : list (nat * sterm))
(* Equality axioms *)
| sBeta (A B t u : sterm)
| sJRefl (A u P w : sterm)
| sTransportRefl (A t : sterm)
.
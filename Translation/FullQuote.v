(* Partial translation from TemplateCoq to ITT *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template
Require Import Ast utils monad_utils LiftSubst Typing Checker Template.
From Translation
Require Import util SAst SLiftSubst SCommon ITyping Quotes FinalTranslation.

Import MonadNotation.

Inductive fq_error :=
| NotEnoughFuel
| NotHandled
| TypingError (msg : string) (e : type_error) (Γ : context) (t : term)
| WrongType (wanted : string) (got : term)
.

Inductive fq_result A :=
| Success : A -> fq_result A
| Error : fq_error -> fq_result A.

Arguments Success {_} _.
Arguments Error {_} _.

Instance fq_monad : Monad fq_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc : MonadExc fq_error fq_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.

Open Scope t_scope.

Fixpoint fullquote (fuel : nat) (Σ : global_context) (Γ : context) (t : term)
         (sl : list sort) (si : sort)
         {struct fuel} : fq_result (sterm * list sort * sort) :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | tRel n => ret (sRel n, sl, si)
    | tSort u =>
      match sl with
      | s :: sl => ret (sSort 0, sl, si)
      | [] => ret (sSort si, [], succ_sort si)
      end
    | tProd nx A B =>
      A' <- fullquote fuel Σ Γ A sl si ;;
      let '(A', sl, si) := A' in
      B' <- fullquote fuel Σ (Γ ,, vass nx A) B sl si ;;
      let '(B', sl, si) := B' in
      ret (sProd nx A' B', sl, si)
    | tLambda nx A t =>
      match infer_hnf fuel Σ (Γ ,, vass nx A) t with
      | Checked B =>
        A' <- fullquote fuel Σ Γ A sl si ;;
        let '(A', sl, si) := A' in
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B sl si ;;
        let '(B', sl, si) := B' in
        t' <- fullquote fuel Σ (Γ ,, vass nx A) t sl si ;;
        let '(t', sl, si) := t' in
        ret (sLambda nx A' B' t', sl, si)
      | TypeError e => raise (TypingError "Lambda" e (Γ ,, vass nx A) t)
      end
    | tApp (tInd {| inductive_mind := "Translation.util.pp_sigT"; inductive_ind := 0 |} []) [ A ; B ] =>
      A' <- fullquote fuel Σ Γ A sl si ;;
      let '(A', sl, si) := A' in
      B' <- fullquote fuel Σ Γ B sl si ;;
      let '(B', sl, si) := B' in
      match sl with
      | s :: sl =>
        ret (sSum nAnon A' (sApp (lift0 1 B') (lift0 1 A') (sSort s) (sRel 0)), sl, si)
      | [] =>
        ret (sSum nAnon A' (sApp (lift0 1 B') (lift0 1 A') (sSort si) (sRel 0)), [], succ_sort si)
      end
    | tApp (tInd {| inductive_mind := "Translation.util.pp_prod"; inductive_ind := 0 |} []) [ A ; B ] =>
      A' <- fullquote fuel Σ Γ A sl si ;;
      let '(A', sl, si) := A' in
      B' <- fullquote fuel Σ Γ B sl si ;;
      let '(B', sl, si) := B' in
      ret (sSum nAnon A' (lift0 1 B'), sl, si)
    | tApp (tInd {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} []) [ A ; u ; v ] =>
      A' <- fullquote fuel Σ Γ A sl si ;;
      let '(A', sl, si) := A' in
      u' <- fullquote fuel Σ Γ u sl si ;;
      let '(u', sl, si) := u' in
      v' <- fullquote fuel Σ Γ v sl si ;;
      let '(v', sl, si) := v' in
      ret (sEq A' u' v', sl, si)
    | tApp u [] =>
      fullquote fuel Σ Γ u sl si
    | tApp u [ v ] =>
      match infer_hnf fuel Σ Γ u with
      | Checked (tProd nx A B) =>
        u' <- fullquote fuel Σ Γ u sl si ;;
        let '(u', sl, si) := u' in
        A' <- fullquote fuel Σ Γ A sl si ;;
        let '(A', sl, si) := A' in
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B sl si ;;
        let '(B', sl, si) := B' in
        v' <- fullquote fuel Σ Γ v sl si ;;
        let '(v', sl, si) := v' in
        ret (sApp u' A' B' v', sl, si)
      | Checked T => raise (WrongType "Prod" T)
      | TypeError e => raise (TypingError "App1" e Γ u)
      end
    | tApp u (v :: l) =>
      fullquote fuel Σ Γ (tApp (tApp u [ v ]) l) sl si
    | _ => raise NotHandled
    end
  end.

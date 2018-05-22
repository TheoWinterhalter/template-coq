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
         {struct fuel} : fq_result sterm :=
  match fuel with
  | 0 => raise NotEnoughFuel
  | S fuel =>
    match t with
    | tRel n => ret (sRel n)
    | tSort u =>
      (* For now on we only return the first universe, this will have to
         tweaked by hand. *)
      ret (sSort 0)
    | tProd nx A B =>
      A' <- fullquote fuel Σ Γ A ;;
      B' <- fullquote fuel Σ (Γ ,, vass nx A) B ;;
      ret (sProd nx A' B')
    | tLambda nx A t =>
      match infer_hnf fuel Σ (Γ ,, vass nx A) t with
      | Checked B =>
        A' <- fullquote fuel Σ Γ A ;;
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B ;;
        t' <- fullquote fuel Σ (Γ ,, vass nx A) t ;;
        ret (sLambda nx A' B' t')
      | TypeError e => raise (TypingError "Lambda" e (Γ ,, vass nx A) t)
      end
    | tApp (tInd {| inductive_mind := "Translation.util.pp_sigT"; inductive_ind := 0 |} []) [ A ; B ] =>
      A' <- fullquote fuel Σ Γ A ;;
      B' <- fullquote fuel Σ Γ B ;;
      ret (sSum nAnon A' (sApp (lift0 1 B') (lift0 1 A') (sSort 0) (sRel 0)))
    | tApp (tInd {| inductive_mind := "Translation.util.pp_prod"; inductive_ind := 0 |} []) [ A ; B ] =>
      A' <- fullquote fuel Σ Γ A ;;
      B' <- fullquote fuel Σ Γ B ;;
      ret (sSum nAnon A' (lift0 1 B'))
    | tApp (tInd {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |} []) [ A ; u ; v ] =>
      A' <- fullquote fuel Σ Γ A ;;
      u' <- fullquote fuel Σ Γ u ;;
      v' <- fullquote fuel Σ Γ v ;;
      ret (sEq A' u' v')
    | tApp u [] =>
      u' <- fullquote fuel Σ Γ u ;;
      ret u'
    | tApp u [ v ] =>
      match infer_hnf fuel Σ Γ u with
      | Checked (tProd nx A B) =>
        u' <- fullquote fuel Σ Γ u ;;
        A' <- fullquote fuel Σ Γ A ;;
        B' <- fullquote fuel Σ (Γ ,, vass nx A) B ;;
        v' <- fullquote fuel Σ Γ v ;;
        ret (sApp u' A' B' v')
      | Checked T => raise (WrongType "Prod" T)
      | TypeError e => raise (TypingError "App1" e Γ u)
      end
    | tApp u (v :: l) =>
      fullquote fuel Σ Γ (tApp (tApp u [ v ]) l)
    | _ => raise NotHandled
    end
  end.

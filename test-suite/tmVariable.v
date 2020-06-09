Require Import List Arith String.
Require Import MetaCoq.Template.All.
Import ListNotations MonadNotation.

Section test.

  MetaCoq Run (tmVariable "bla" nat).
  Check (bla : nat).
  MetaCoq Run (tmDefinition "test" bla).
  MetaCoq Run (tmDefinition "test2" 0).

  MetaCoq Run (tmVariable "toto" nat ;;
              gr <- tmLocate1 "toto" ;;
              match gr with
              | VarRef id => let term := tVar id in
                            tmPrint "Here we can get the term"
              | _ => tmFail "Something bad happened"
              end).

End test.

Check (test : nat -> nat).
Check (test2 : nat).

Section one.

  From Local Require Import ltac2_tactics tauto_solver.

  From iris.proofmode Require Import tactics intro_patterns.
  From iris.proofmode Require Import coq_tactics.
  From iris.proofmode Require Import base spec_patterns
     sel_patterns coq_tactics reduction.

  From Ltac2 Require Import Ltac2 List.
  Set Ltac2 Backtrace.

  From iris.proofmode Require Import classes notation.

  Context {PROP : sbi}.
  Implicit Types P Q R : PROP.

  Lemma test_iAssumption_coq_1 P Q : (⊢ Q) → <affine> P -∗ Q.
  Proof.
    i_start_proof ().
    Set Printing All.
    i_intro_pat @H.
    Unset Printing All.
    intro.
    i_intro_constr '(INamed "q").
    i_intro ().
    do 2 (i_intro ()).
    i_assumption_coq ().
  Qed.


  Lemma test_one (P : PROP) (Q : PROP): (<affine> P ∗ Q) ⊢ (<pers> Q) → Q ∗ P.
  Proof.
    i_start_proof ().
    i_intro_constr '(INamed "pq").
    i_intro ().
    Unset Printing All.
    i_and_destruct '(INamed "pq") '(INamed "p") '(INamed "q").
    i_split_l '(["p"; "q"]).
    i_assumption ().
    i_exact '(INamed "p").
    i_stop_proof ().

    i_start_proof ().
    i_intro_constr '(INamed "v").
    i_exact '(INamed "v").
  Qed.
End one.

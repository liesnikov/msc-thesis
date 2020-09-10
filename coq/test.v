From iris.proofmode Require Import tactics intro_patterns.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import base spec_patterns
     sel_patterns coq_tactics reduction.

Goal exists a, (a = true \/ a = false) ∧ (a = true).
  eexists.
  split.
  - eauto.
Abort.

Lemma example_1 {PROP : bi} {A : Type} (P : PROP) (Φ Ψ : A → PROP) :
  P ∗ (∃ a, Φ a ∨ Ψ a) -∗ ∃ a, (P ∗ Φ a) ∨ (P ∗ Ψ a).
Proof.
  iIntros "[HP H]". Show.
  iDestruct "H" as (x) "[H1|H2]".
  - Show. iExists x. iLeft. iSplitL "HP"; iAssumption.
  - Show. iExists x. iRight. iSplitL "HP"; iAssumption.
Qed.

From Local Require Import ltac2_tactics tauto_solver.
From Ltac2 Require Import Ltac2 List.
(*Set Ltac2 Backtrace.*)

From iris.proofmode Require Import classes notation.

Context {PROP : sbi}.
Implicit Types P Q R : PROP.


From Local Require utils.
Import utils.Iriception utils.Misc.
Lemma test_iAssumption_coq_1 P Q : (⊢ Q) → <affine> P -∗ Q.
Proof.
  i_intro_pat q.
  i_intro ().
  i_assumption_coq ().
Qed.

Lemma test_tauto (P : PROP) (Q : PROP): P ∗ Q ∗ False ⊢ Q ∗ P.
Proof.
  tauto_solver_go [].
Qed.

Lemma test_and_and (P Q : PROP): Q ∧ P ⊢ P ∧ Q.
Proof.
  tauto_solver_go [].
Qed.

Lemma test_one (P : PROP) (Q : PROP): (<affine> P ∗ Q) ⊢ (<pers> Q) → Q ∗ P.
Proof.
  i_start_proof ().
  i_intro_constr '(INamed "pq").
  i_intro_constr '(INamed "qq").
  i_and_destruct '(INamed "pq") '(INamed "p") '(INamed "q").
  i_split_l '(["q"; "qq"]).
  i_assumption ().
  i_stop_proof ().

  i_start_proof ().
  i_intro_constr '(INamed "v").
  i_exact '(INamed "v").
Qed.
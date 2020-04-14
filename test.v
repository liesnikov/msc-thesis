From iris.proofmode Require Import tactics intro_patterns.
Require Import Local.ltac2_tactics.
Set Default Proof Using "Type".

Section test.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.


Lemma test (P Q : PROP): ⊢ Q -∗ Q.
Proof.
  refine (as_emp_valid_2 (@bi_emp_valid (sbi_bi PROP) (@bi_wand (sbi_bi PROP) Q Q))
                         _ _).
  refine (proofmode.coq_tactics.tac_start _ _).
  Set Printing All.
  iIntros "q".
  iExact "q".
Qed.

Lemma test_eauto_emp_isplit_biwand P : emp ⊢ P ∗-∗ P.
Proof.
  Set Printing All.
  iStartProof.
  eauto.
Qed.

End test.

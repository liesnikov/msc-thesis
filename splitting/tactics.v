From iris.bi Require Import bi.
From iris.proofmode Require Import base spec_patterns.
From Local.splitting Require named_prop numbered_prop split_evars connection.
From Local Require Import ltac2_tactics.
From Ltac2 Require Import Ltac2.

Context {PROP : bi}.
Lemma test_and_and (P Q : PROP): Q ∧ P ⊢ P ∧ Q.
Proof.
  i_start_proof ().
  pose (Δ2 := @named_prop.Envs PROP named_prop.Enil named_prop.Enil 1).
  apply (@connection.from_named PROP _ _ _ _).
Qed.

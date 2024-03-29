From Ltac2 Require Import Ltac2.
From Local Require Import utils.
Import utils.Misc.
From iris.proofmode Require Import classes notation.
Set Default Proof Using "Type".
Context {PROP : sbi}.
Implicit Types P Q R : PROP.
From Local Require Import splitting_imatch splitting_ltac2_tactics named_prop.
Set Ltac2 Backtrace.

Lemma test1 P Q : Q ⊢ □ (<absorb> P) -∗ (* P ∗*) Q.
Proof.
  i_start_split_proof ().
  i_intro_ident '(INamed "q").
  (* i_intro_ident '(INamed "p"). *)
  i_intro_intuitionistic_ident '(INamed "p").
  (* i_split ().*)
  iLazyMatch! goal with
  | [ h : _, _ : sep, _ : sep, h1 : _ |- _] => h1
  end.

  iMatch! goal with
  | [h1 : _, h2 : (<absorb> _)%I |- ?p] =>
    i_assumption ()
  end.
Qed.

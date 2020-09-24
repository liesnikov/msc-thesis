From iris.bi Require Export bi telescopes.
From iris.proofmode Require Export base classes notation.
Set Default Proof Using "Type".

From Local Require Import splitting_ltac2_tactics splitting_imatch named_prop.
From Ltac2 Require Import Ltac2.

Ltac2 i_solver () := repeat (
  iMatch! goal with
  | [a : <?>(?p ∧ ?q) |- _ ] =>
   let b :=i_fresh_fun () in
   let c := i_fresh_fun () in
   i_and_destruct_split a b c
  | [a : <?>(?p ∗ ?q) |- _ ] =>
   let b :=i_fresh_fun () in
   let c := i_fresh_fun () in
   i_and_destruct a b c
  | [a : <?>(?p ∨ ?q) |- _ ] =>
   let b :=i_fresh_fun () in
   let c := i_fresh_fun () in
   i_or_destruct a b c
  | [ |- ((□ ?p) -∗ ?q)%I] =>
    let b :=i_fresh_fun () in
    i_intro_intuitionistic_ident b
  | [ |- (?p -∗ ?q)%I] =>
    let b :=i_fresh_fun () in
    i_intro_ident b
  | [ |- (?p -> ?q)%I] =>
    let b :=i_fresh_fun () in
    i_intro_ident b
  | [ |- (∀ _, _)] =>
    i_intro_pat ?
  | [a: _ |- _] =>
    i_assumption ()
  end).


From iris.proofmode Require Import classes notation.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.

Set Ltac2 Backtrace.

Lemma test1 P Q : Q ∧ P ⊢ □ (<absorb> P) -∗ Q.
Proof.
  i_start_split_proof ().
  i_solver ().
Qed.

From iris.bi Require Export bi telescopes.
From iris.proofmode Require Export base classes notation.
Set Default Proof Using "Type".

From Local Require Import splitting_ltac2_tactics splitting_imatch named_prop.
From Ltac2 Require Import Ltac2.
From Local Require Import utils.
Import utils.Misc.

From Ltac2 Require Import Pattern.
Ltac2 Eval (multi_goal_match0).
Ltac2 Eval i_match_goal.

Ltac2 i_solver () := i_start_split_proof (); solve [repeat (
  orelse (fun () => iLazyMatch! goal with
  | [a : <?>(?p ∧ ?q) |- _ ] =>
    let a' := ipm_id a in
    let b := i_fresh_fun () in
    let c := i_fresh_fun () in
    i_and_destruct_split a' b c
  | [a : <?>(?p ∗ ?q) |- _ ] =>
    let a' := ipm_id a in
    let b := i_fresh_fun () in
    let c := i_fresh_fun () in
    i_and_destruct a' b c
  | [ |- (?p ∗ ?q)%I] =>
    i_sep_split ()
  | [ |- (?p ∧ ?q)%I] =>
    i_and_split ()
  | [ |- ((□ ?p) -∗ ?q)%I] =>
    let b := i_fresh_fun () in
    i_intro_intuitionistic_ident b
  | [ |- (?p -∗ ?q)%I] =>
    let b := i_fresh_fun () in
    i_intro_ident b
  | [ |- (?p → ?q)%I] =>
    let b :=i_fresh_fun () in
    i_intro_ident b
  | [ |- (∀ _, _)%I] =>
    i_intro_pat ?
  | [ |- (∃ _, _)%I] =>
    i_exists_one '(_)
  | [ |- (<pers> _)%I] =>
    i_mod_intro ()
  | [ |- (<affine> _)%I] =>
    i_mod_intro ()
  | [ |- (□ _)%I ]=>
    i_mod_intro ()
  | [ |- (▷ _)%I] =>
    i_mod_intro ()
  end)
  (fun _ => iMultiMatch! goal with
  | [a : <?>(?p ∨ ?q) |- _ ] =>
    let a' := ipm_id a in
    let b := i_fresh_fun () in
    let c := i_fresh_fun () in
    i_or_destruct a' b c
  | [a : <?>(∃ _, _) |- _ ] =>
    let a' := ipm_id a in
    (i_exist_destruct a' as ? a')
  | [ |- (?p ∨ ?q)%I] =>
    or i_left i_right
  | [ |- (⌜ _ ⌝)%I] =>
    i_pure_intro (); auto
  | [a : <?>(?p -∗ ?q) |- _] =>
    let a' := ipm_id a in
    i_apply_ident a'
  | [|- _] =>
    i_assumption ()
   end))].

From iris.proofmode Require Import classes notation.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.

Set Ltac2 Backtrace.

Lemma test1 P Q : Q ∧ P ⊢ □ (<absorb> P) -∗ Q.
Proof.
  i_solver ().
Qed.

Lemma test2 P Q : ⊢ (□ Q) -∗ (((∃ (x : nat), P) -∗ P) ∗ Q).
Proof.
  i_solver ().
Qed.

Lemma test4 P1 P2 P3 :
  P1 ∗ P2 ∗ P3 -∗ P1 ∗ ▷ (P2 ∗ ∃ x, (P3 ∧ ⌜x = 0⌝) ∨ P3).
Proof.
  i_solver ().
Qed.

From iris.proofmode Require Import tactics intro_patterns.
Set Default Proof Using "Type".

Lemma test3 P1 P2 P3 P4 Q (P5 : nat → PROP) `{!Affine P4, !Absorbing P2} :
  P2 ∗ (P3 ∗ Q) ∗ True ∗ P1 ∗ P2 ∗ (P4 ∗ (∃ x:nat, P5 x ∨ P3)) ∗ emp -∗
    P1 -∗ (True ∗ True) -∗
  (((P2 ∧ False ∨ P2 ∧ ⌜0 = 0⌝) ∗ P3) ∗ Q ∗ P1 ∗ True) ∧
     (P2 ∨ False) ∧ (False → P5 0).
Proof.
  ltac1:(time "timer" ltac2:(i_solver ())).
  (* takes a minute. really *)
  (* if we swap orelse for try (first); try (second) it will be down to 45 *)
Qed.


Lemma test_iFrame_persistent (P Q : PROP) :
  □ P -∗ Q -∗ <pers> (P ∗ P) ∗ (P ∗ Q ∨ Q).
Proof.
  i_solver ().
Qed.

Lemma test_specialize_very_nested (φ : Prop) P P2 Q R1 R2 :
  φ →
  P -∗ P2 -∗
  (⌜ φ ⌝ -∗ P2 -∗ Q) -∗
  (P -∗ Q -∗ R1) -∗
  (R1 -∗ True -∗ R2) -∗
  R2.
Proof.
  i_solver ().
Qed.


Lemma test_specialize_very_very_nested P1 P2 P3 P4 P5 :
  □ P1 -∗
  □ (P1 -∗ P2) -∗
  (P2 -∗ P2 -∗ P3) -∗
  (P3 -∗ P4) -∗
  (P4 -∗ P5) -∗
  P5.
Proof.
  i_solver ().
Qed.

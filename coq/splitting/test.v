From Ltac2 Require Import Ltac2.

From iris.proofmode Require Import tactics intro_patterns.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import base spec_patterns
     sel_patterns coq_tactics reduction.

From Local Require ltac2_tactics.
From Local Require Import utils.
Import utils.Evars.

Inductive Id {A} (a : A) : Type := C : Id a.


Goal True.
Proof.
  let v := new_evar_with_cast '(nat) in
  let q := new_evar_with_cast '(bool) in
  assert (Id $v /\ ($q && false)= true).
  admit.
  cbn in H.
  match! goal with
  | [|- Id ?v /\ ?q = _] =>
    Message.print (utils.Misc.os "worked");
      unify $v 1;
    match! q with
    | (andb ?a ?b) => orelse (fun () => unify true $a) (fun e => Control.throw e)
    | _ => Message.print (utils.Misc.os "couldn't match andb")
    end
  | [|- _] => Message.print (utils.Misc.os "didn't work")
  end.
  let a := Std.eval_red '(1 + 1) in
  Message.print (utils.Misc.oc a).

  let _ := new_evar '(nat) in ().
  admit.
Admitted.

From Local Require Import tactics.
Set Default Proof Using "Type".

Context {PROP : bi}.
Implicit Types P Q R : PROP.

Lemma test_zero (P : PROP) (Q : PROP): ⊢ Q -∗ Q.
Proof.
  ltac2_tactics.i_start_proof ().
  refine '(connection.from_named _ _ _).
  i_intro_named "qq".
  i_exact_spatial '(INamed "qq").
Qed.

Lemma test_one (P Q R : PROP): ⊢ (R ∗ Q) -∗ P -∗ P ∗ (Q ∗ R).
Proof.
  i_start_split_proof ().
  i_intro_ident '(INamed "rq").
  i_intro_ident '(INamed "pp").
  i_split (); ltac1: (revgoals).
  - i_and_destruct '(INamed "rq") '(INamed "r") '(INamed "q").
    i_split ().
    + i_exact_spatial '(INamed "q").
    + i_cleanup (). i_exact_spatial '(INamed "r").
  - i_cleanup (). i_exact_spatial '(INamed "pp").
Qed.

Lemma test_two (P Q : PROP): (P ∧ Q) -∗ P.
Proof.
  i_start_split_proof ().
  i_intro_ident '(INamed "pq").
  i_and_destruct_split '(INamed "pq") '(INamed "p") '(INamed "q").
  i_exact_spatial '(INamed "p").
Qed.

Lemma test_three (P Q : PROP): (P ∨ Q) -∗ (emp ∗ (Q ∨ P)).
  i_start_split_proof ().
  i_intro_ident '(INamed "pq").
  i_split () >
  [ ()
  | i_or_destruct '(INamed "pq") '(INamed "p") '(INamed "q") >
    [ i_right (); i_exact_spatial '(INamed "p")
    | i_left (); i_exact_spatial '(INamed "q")]].
  i_emp_intro ().
Qed.

Lemma test_four (P Q : PROP): (⊢ P) -> ⊢ P.
  i_start_split_proof ().
  i_intro_pat p.
  i_assumption_coq ().
Qed.

Lemma test_five (P Q : PROP) : □ P ⊢ □ P.
Proof.
  i_start_split_proof ().
  i_intro_intuitionistic_ident '(INamed "p").
  i_mod_intro ().
  i_assumption ().
Qed.

Lemma test_six P Q : Q ⊢ □ (<absorb> P) -∗ (* P ∗*) Q.
Proof.
  i_start_split_proof ().
  i_intro_ident '(INamed "q").
  i_intro_ident '(INamed "p").
  (* i_split ().*)
  iLazyMatch! goal with
  | [h1 : <?> ?p |- _] => Message.print (Misc.oc p)
  end.

  iMatch! goal with
  | [h1 : _, h2 : (<absorb> _)%I |- ?p] =>
    i_assumption ()
  end.
Qed.

Lemma test_seven P Q R : Q ⊢ (Q -∗ P -∗ R) -∗ P -∗ (emp ∗ R).
  i_start_split_proof ().
  i_intro_ident '(INamed "q").
  i_intro_ident '(INamed "f").
  i_intro_ident '(INamed "p").
  i_split ().
  Focus 2.
  i_specialize '(INamed "f") '(INamed "q") '(INamed "fq").
  i_specialize '(INamed "fq") '(INamed "p") '(INamed "r").
  i_assumption (). i_emp_intro ().
Qed.

Lemma test_eight : ⊢@{PROP} ∃ x, ⌜x = true⌝.
Proof.
  i_start_split_proof ().
  i_exists_one '(true).
  i_pure_intro ().
  reflexivity.
Qed.

Lemma test_nine : ⌜1 = 2⌝ ⊢@{PROP} True.
Proof.
  i_start_split_proof ().
  i_intro_ident '(INamed "p").
  i_pure '(INamed "p") as p.
  discriminate.
Qed.

Lemma test_ten P Q R : Q ⊢ (Q -∗ R) -∗ (emp ∗ R).
Proof.
  i_start_split_proof ().
  i_intro_ident '(INamed "q").
  i_intro_ident '(INamed "f").
  i_split ().
  Focus 2.
  i_apply_ident '(INamed "f"). i_assumption ().
  i_emp_intro ().
Qed.


Lemma test_eleven P Q R : Q ⊢ (Q -∗ P -∗ R) -∗ P -∗ (emp ∗ R).
Proof.
  i_start_split_proof ().
  i_intro_ident '(INamed "q").
  i_intro_ident '(INamed "f").
  i_intro_ident '(INamed "p").
  i_split (). Focus 2.
  i_specialize_assert '(INamed "f").
  Focus 2.
  i_specialize_assert '(INamed "f").
  Focus 2.
  i_assumption ().
  i_assumption ().
  i_assumption ().
  i_emp_intro ().
Qed.

Lemma test_twelve P Q R : Q ⊢ (Q -∗ P -∗ R) -∗ P -∗ (emp ∗ R).
  i_start_split_proof ().
  i_intro_ident '(INamed "q").
  i_intro_ident '(INamed "f").
  i_intro_ident '(INamed "p").
  i_split (). Focus 2.
  i_apply_ident '(INamed "f").
  i_assumption ().
  i_assumption ().
  i_emp_intro ().
Qed.

Lemma test_thirteen P x : (x = true) -> P ⊢ emp ∗ P ∗ ⌜x = true⌝.
Proof.
  intros.
  i_intro_ident '(INamed "p").
  i_split ().
  Focus 2.
  i_frame_hyp '(INamed "p").
  i_frame_pure H.
  Undo 2.
  i_frame ().
  i_frame_any_pure ().
  i_emp_intro ().
Qed.

Lemma test_fourteen (P : nat -> PROP) : (∃ x, P (x - 1)) ⊢ ∃ x, P (x).
  i_intro_ident '(INamed "p").
  (i_exist_destruct '(INamed "p") as [|] '(INamed "p"));;
  i_exists _ ;; i_assumption ().
Qed.

Lemma test_fifteen P Q :  P ∧ Q ⊢ Q ∧ P.
Proof.
  i_intro_ident '(INamed "pq").
  i_split ();;
  i_and_destruct_split '(INamed "pq") '(INamed "p") '(INamed "q");;
  i_assumption ().
Qed.


Lemma test_sixteen {A : Type} (P : PROP) (Φ Ψ : A → PROP) :
  P ∗ (∃ a, (Φ a) ∨ (Ψ a)) -∗ ∃ a, (P ∗ Φ a) ∨ (P ∗ Ψ a).
Proof.
  i_intro_named "H".
  i_and_destruct '(INamed "H") '(INamed "HP") '(INamed "HE").
  i_exist_destruct '(INamed "HE") as x '(INamed "HE").
  i_or_destruct '(INamed "HE") '(INamed "H1") '(INamed "H2") ;; i_exists x.
  - i_left (). i_split () ;; i_assumption ().
  - i_right (). i_split () ;; i_assumption ().
Qed.

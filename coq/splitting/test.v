Goal True.
Proof.
  assert True as H.
  Proof.
    exact I.
  exact H.
Qed.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Control.

From Local Require Import utils.
Import utils.Misc utils.Evars.

Definition hey := 1.

Ltac2 n () := '(_).

Ltac2 Eval n ().

Goal nat.
  evar (t2 : nat).
  exact t2.
  Unshelve.
  constructor.
Qed.

Goal nat.
Proof.
  evar (t2 : nat).
  Ltac2 Eval ((Control.hyps ())).
  Fail Ltac2 Eval (Env.get [ident_of_string "Coq.Init.Datatypes.S"]).
  Ltac2 Eval (match! (Control.hyp (ident_of_string "t2")) with
              | true => "hey"
              | false => "ho"
              | _ => "hoy"
              end).
  auto. Unshelve. constructor.
Admitted.

From iris.proofmode Require Import tactics intro_patterns.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import base spec_patterns
     sel_patterns coq_tactics reduction.

From Local Require ltac2_tactics.
From Local Require Import utils.
Import utils.Evars.

Inductive Id {A} (a : A) : Type := C : Id a.
Set Ltac2 Backtrace.


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

  new_evar '(nat).
  admit.
Admitted.

From Local Require Import splitting_tactics splitting_ltac2_tactics.
From Local Require connection.

Context {PROP : bi}.
Implicit Types P Q R : PROP.
Set Default Proof Using "Type".

Lemma test_zero (P : PROP) (Q : PROP): ⊢ Q -∗ Q.
Proof.
  ltac2_tactics.i_start_proof ().
  refine '(connection.from_named _ _ _).
  i_intro_ident '(INamed "qq").
  i_exact_spatial '(INamed "qq").
Qed.

Lemma test_one (P Q R : PROP): ⊢ (R ∗ Q) -∗ P -∗ P ∗ (Q ∗ R).
Proof.
  i_start_split_proof ().
  i_intro_ident '(INamed "rq").
  i_intro_ident '(INamed "pp").
  i_split ().
  Focus 2.
  i_and_destruct '(INamed "rq") '(INamed "r") '(INamed "q").
  i_split ().
  i_exact_spatial '(INamed "q").
  i_exact_spatial '(INamed "r").
  i_exact_spatial '(INamed "pp").
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
  | i_or_destruct '(INamed "pq") '(INamed "p") '(INamed "q")].
  Focus 2. i_right (). i_exact_spatial '(INamed "p").
  Focus 2. i_left (). i_exact_spatial '(INamed "q").
  i_emp_intro ().
Qed.

Lemma test_four (P Q : PROP): (⊢ P) -> ⊢ P.
  i_start_split_proof ().
  i_intro_pat p.
  Ltac2 Notation "test" s(assert) := s.
  Ltac2 Eval (test (FromAssumption true P P) as fr).
  let fr := fresh () in
  lazy_match! goal with
  | [h : (⊢ ?p) |- named_prop.envs_entails _ ?q] =>
    Std.assert (Std.AssertType
                  (Some (Std.IntroNaming (Std.IntroIdentifier (fr))))
                  '(FromAssumption true $p $q)
                  None) > [i_solve_tc ()|];
    refine '(tac_assumption_coq _ $p $q _ _ _) >
    [ ()
    | ()
    | pm_reduce (); i_solve_tc () ]
    (* assert (FromAssumption true $p $q) as fr > [i_solve_tc ()|] *)
    (* refine '(tac_assumption_coq _ $p $q h fr _) *)
  end.
  Ltac2 Eval (Control.hyp ident:(p)).

  Focus 2.
  i_intro_intuitionistic_ident '(INamed "p").
  tac_assumption

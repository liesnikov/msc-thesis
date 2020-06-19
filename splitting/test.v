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

From Local Require Import splitting_tactics.
From Local Require connection.


Context {PROP : bi}.
Implicit Types P Q R : PROP.
Set Default Proof Using "Type".

Lemma test_zero (P : PROP) (Q : PROP): ⊢ Q -∗ Q.
Proof.
  ltac2_tactics.i_start_proof ().
  refine '(connection.from_named _ _ _).
  i_intro_constr '(INamed "qq").
  i_exact_spatial '(INamed "qq").
Qed.

Lemma test_one (P : PROP) (Q : PROP): ⊢ Q -∗ P -∗ P ∗ Q.
Proof.
  ltac2_tactics.i_start_proof ().
  refine '(connection.from_named _ _ _).
  i_intro_constr '(INamed "qq").
  i_intro_constr '(INamed "pp").
  i_split ().
  i_exact_spatial '(INamed "pp").
  i_exact_spatial '(INamed "qq").
Qed.

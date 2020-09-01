From iris.bi Require Export bi telescopes.
From iris.proofmode Require Export base classes notation.
Set Default Proof Using "Type".

From Local Require Import named_prop.
From Local Require Import connection.

From Ltac2 Require Import Ltac2.

From Local Require utils.
Import utils.Misc utils.Iriception utils.Evars.

From Local Require ltac2_tactics.
From Local Require Import splitting_tactics.


Require Import Ltac2.Std.

(* getting them from
  Ltac2 Notation "test" s(strategy) := s.
  Ltac2 Eval (test). *)

Ltac2 Type ident_ltac2 := constr.
Ltac2 red_flags_default := { rBeta := true; rMatch := true; rFix := true; rCofix := true; rZeta := true; rDelta := true; rConst := [] }.

Ltac2 new_constraint () := new_evar_with_cast '(bool).

Ltac2 rec unify_with_bool (e : constr) (b : bool) :=
  let er := Std.eval_cbn red_flags_default e in
  lazy_match! er with
  | negb ?b0 => unify_with_bool b0 (Bool.neg b)
  | andb ?b1 ?b2 =>
    unify_with_bool b1 b;
    match b with
    | true => unify_with_bool b2 true
    | false => ()
    end
  | orb ?b1 ?b2 =>
    match b with
    | false => unify_with_bool b1 false
    | true => unify_with_bool b1 true; unify_with_bool b1 true
    end
  | ?b0 =>
     let br := match b with true => '(true) | false => '(false) end in
     unify0 b0 br
  end.

Ltac2 rec unify_constr_true (e : constr) := unify_with_bool e true.


Ltac2 rec unify_constr_false (e : constr) := unify_with_bool

Ltac2 pm_reduce () :=
  cbv [named_prop.get_ident
       connection.translate_envs connection.translate_env
       named_prop.env_lookup named_prop.env_lookup_with_constr
       named_prop.env_lookup_true
       named_prop.env_delete
       named_prop.env_app named_prop.env_replace
       named_prop.env_intuitionistic named_prop.env_spatial
       named_prop.env_counter named_prop.env_spatial_is_nil
       named_prop.env_Forall
       named_prop.envs_lookup named_prop.envs_lookup_with_constr
       named_prop.envs_lookup_true
       named_prop.envs_delete
       named_prop.envs_snoc named_prop.envs_app
       named_prop.envs_simple_replace named_prop.envs_replace
       named_prop.envs_split named_prop.envs_clear_spatial
       named_prop.envs_clear_intuitionistic named_prop.envs_incr_counter
       named_prop.envs_split];
  ltac2_tactics.pm_reduce ().

Ltac2 pm_reflexivity () :=
  pm_reduce (); exact eq_refl.

Ltac2 pm_prettify () :=
  ltac2_tactics.pm_prettify ().

Ltac2 i_solve_tc := ltac2_tactics.i_solve_tc.

Ltac2 i_start_split_proof () :=
  let apply_named () := refine '(from_named _ _ _) > [ pm_reduce ()] in
  lazy_match! goal with
  | [|- @environments.envs_entails _ _ _] => apply_named ()
  | [|- @envs_entails _ _ _] => ()
  | [|- ?p ] => ltac2_tactics.i_start_proof (); apply_named ()
  end.


Ltac2 i_fresh_fun () :=
  i_start_split_proof ();
  lazy_match! goal with
   | [|- @envs_entails ?pr1 (@Envs ?pr2 ?p ?s ?c) ?q] =>
    (ltac1:(pr1 pr2 p s c q |-
           let c1 := (eval vm_compute in (Pos.succ c)) in
           change_no_check (@envs_entails pr1 (@Envs pr2 p s c1) q))
           (Ltac1.of_constr pr1) (Ltac1.of_constr pr2) (Ltac1.of_constr p) (Ltac1.of_constr s) (Ltac1.of_constr c) (Ltac1.of_constr q));
     constr:(IAnon $c)
end.

Ltac2 i_intro_pat' (x : Std.intro_pattern) :=
  or (fun () => failwith (fun () => intros0 false [x]) "couldn't use intro")
     (fun () =>
      failwith i_start_split_proof "couldn't start proof in i_intro_pat";
      lazy_match! goal with
      | [|- @envs_entails _ _ _] =>
        refine '(tac_forall_intro _ _ _ _ _) >
        [ () | ()
        | orelse i_solve_tc
          (fun e => lazy_match! goal with
           | [|- FromForall ?p _ : _] =>
             Control.zero (Iriception
                             ((Message.of_string "iIntro: cannot turn ") ++
                              (Message.of_constr p) ++
                              (Message.of_string " into a universal quantifier")))
           end)
        | pm_prettify (); intros0 false [x] ]
      end).

Ltac2 Notation "i_intro_pat" p(intropattern) := i_intro_pat' p.

Ltac2 i_intro_ident (x: ident_ltac2) :=
  failwith (i_start_split_proof) "Couldn't start splitting proof in intro_constr";
  or
    (fun () => refine '(@tac_impl_intro _ _ $x _ _ _ _ _ _ _ _) >
            [() | () | ()
            | i_solve_tc ()
            | pm_reduce (); ltac2_tactics.i_solve_tc ()
            | i_solve_tc ()
            | pm_reduce ();
              lazy_match! goal with
              | [|- False] => Control.zero (Iriception (os "i_intro " ++ oc x ++ os " not fresh"))
              | [|- _] => ()
               end])
    (fun () => refine '(@tac_wand_intro _ _ $x _ _ _ _ _) >
            [ () | ()
            | i_solve_tc ()
            | pm_reduce ()]).

Ltac2 i_intro_intuitionistic_ident (x : ident_ltac2) :=
  failwith (i_start_split_proof)
           "Couldn't start splitting proof in intro_constr";
    or (fun () =>
        refine '(tac_impl_intro_intuitionistic _ $x _ _ _ _ _ _ _) >
        [ () | () | ()
        | i_solve_tc () | i_solve_tc ()
        | pm_reduce ()])
     (fun () =>
        refine '(tac_wand_intro_intuitionistic _ $x _ _ _ _ _ _ _ _) >
        [ () | () | ()
        | i_solve_tc () | i_solve_tc ()
        | i_solve_tc () | pm_reduce ()]).

Ltac2 i_exact_spatial h :=
  let rec list_from_env e :=
      match! e with
      | Esnoc ?gg (?b,?j) ?pp =>
        match (Constr.equal h j) with
        | true => unify_constr_true b; list_from_env gg
        | false => b :: list_from_env gg
        end
      | Enil => []
      end in
  lazy_match! goal with
  | [|- @envs_entails _ (@Envs _ ?gp ?gs _) ?q] =>
    let list_of_constr := list_from_env gs in
    List.iter (fun b => unify_constr_false b) list_of_constr
  end;
  refine '(tac_assumption _ $h _ _ _ _ _ _) >
  [() | () | pm_reflexivity ()
  | i_solve_tc ()
  | pm_reduce (); i_solve_tc ()].

Ltac2 i_and_destruct (x : ident_ltac2)
                     (y : ident_ltac2)
                     (z : ident_ltac2) :=
  refine '(tac_and_destruct _ $x _ $y $z _ _ _ _ _ _ _ _).


Ltac2 rec env_length (x : constr) :=
  lazy_match! x with
  | Enil => 0
  | Esnoc ?x _ _ => Int.add 1 (env_length x)
  end.

Ltac2 i_split () :=
  let n :=
    lazy_match! goal with
    | [|- @envs_entails _ (@Envs _ ?gp ?gs _) ?q] => env_length gs
    end in
  let rec gen_list n :=
    match (Int.equal 0 n) with
    | true => '(nil)
    | false =>
      let v := new_constraint () in
      let tl := gen_list (Int.sub n 1) in
      '($v :: $tl)
    end in
  let bs := gen_list n in
  match! goal with
  | [|- @envs_entails _ ?g ?q] =>
    refine '(tac_sep_split $g $bs _ _ _ _ _) >
    [ () | ()
    | i_solve_tc ()
    | pm_reduce ();
      lazy_match! goal with
      | [ |- False] => iriception "couldn't split the context"
      | [ |- _] => split > [() | ()]
      end]
  | [|- _] => iriception "the goal isn't bi entailment"
  end.

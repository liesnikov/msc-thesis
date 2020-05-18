From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import base intro_patterns spec_patterns
     sel_patterns coq_tactics reduction.
From iris.proofmode Require Import classes notation.

From iris.proofmode Require Import tactics.
From Ltac2 Require Import Ltac2.
From Ltac2 Require List.

Set Ltac2 Backtrace.


Ltac2 i_fresh () := ltac1:(iFresh).

Ltac2 Type exn ::= [ Iriception(message) ].
Ltac2 Type exn ::= [ ListExn ((message option) * (exn list)) ].
Ltac2 iriception t := Iriception (Message.of_string t).

Ltac2 failwith t s :=
    match Control.case t with
    | Val v_exn => let (v, exn) := v_exn in v
    | Err exn => Control.zero (Iriception (Message.concat
                                            (Message.concat (Message.of_string s)
                                                            (Message.of_string ": "))
                                            (Message.of_exn exn)))
    end.

Ltac2 or t1 t2 := Control.plus (t1) (fun e1 => Control.plus (t2) (fun e2 => Control.zero (ListExn (None, [e1 ; e2])))).

Ltac2 Notation x(self) "++" y(self) := Message.concat x y.
Ltac2 os (x:string) := Message.of_string x.
Ltac2 oc (x:constr) := Message.of_constr x.

Ltac2 current_hyps_names () := List.map (fun x => let (i, _, _) := x in i) (Control.hyps ()).
Ltac2 fresh () := Fresh.fresh (Fresh.Free.of_ids (current_hyps_names ())) ident:(H).


(* FIXME type class resolution*)

Ltac2 i_solve_tc () := ltac1:(iSolveTC).
(*Ltac2 i_solve_tc () :=
  solve [typeclasses_eauto].*)

Ltac2 i_start_proof () :=
  match! goal with
  | [|- @envs_entails _ _ _ ] => ()
  | [|- ?p ] => refine '(as_emp_valid_2 $p _ _) >
              [ auto using sbi_bi
              | () (* this has to be left as it is, since otherwise the next goal is instantiated with a wrong ?P *)
              | i_solve_tc ()
              | refine '(tac_start _ _)
              ]
  end.

Tactic Notation "iiStartProof" := ltac2:(i_start_proof ()).

Ltac2 i_intro_pat (x : ident) :=
  or (fun () => intros x)
     (fun () =>
      failwith i_start_proof "couldn't start proof in intro_pat";
      match! goal with
       | [|- @envs_entails _ _ _] =>
         refine '(tac_forall_intro _ _ _ _ _)>[ () | () | i_solve_tc () | ()]
                                                   (* ^match goes here *)
         (* match! goal with
           | [|- FromForall ?p _ : _] =>
             Control.zero (Iriception
                             ((Message.of_string "iIntro: cannot turn ") ++
                              (Message.of_constr p) ++
                              (Message.of_string " into a universal quantifier")))
           | [|- _] => () *)
       end).

Ltac2 i_intro_constr (x:constr) :=
  (failwith (i_start_proof) "couldn't start proof in intro_constr");
  (or
    (fun () => refine '(@tac_impl_intro _ _ $x _ _ _ _ _ _ _ _) >
     [() | () | ()
     | i_solve_tc ()
     | ltac1:(pm_reduce); i_solve_tc ()
       (* lazymatch goal with |- Persistent ?P => P end in fail 1 "iIntro: introducing non-persistent" H ":" P "into non-empty spatial context" *)
     | i_solve_tc ()
     | ltac1:(pm_reduce);
       lazy_match! goal with
       | [|- False] => Control.zero (Iriception (os "i_intro " ++ oc x ++ os " not fresh"))
       | [|- _] => ()
       end
       (* lazymatch goal with | |- False => let H := pretty_ident H in fail 1 "iIntro:" H "not fresh" | _ => idtac (* subgoal *)*)])
    (fun () => refine '(@tac_wand_intro _ _ $x _ _ _ _ _) >
     [ () | ()
     | i_solve_tc ()
     | ltac1:(pm_reduce)
(* lazymatch goal with | |- False => let H := pretty_ident H in fail 1 "iIntro:" H "not fresh" | _ => idtac (* subgoal *)*)])).


Ltac2 i_fresh_fun () :=
  i_start_proof ();
  lazy_match! goal with
   | [|- @envs_entails ?pr1 (@Envs ?pr2 ?p ?s ?c) ?q] =>
    (ltac1:(pr1 pr2 p s c q |-
           let c1 := (eval vm_compute in (Pos.succ c)) in
           convert_concl_no_check (@envs_entails pr1 (@Envs pr2 p s c1) q))
           (Ltac1.of_constr pr1) (Ltac1.of_constr pr2) (Ltac1.of_constr p) (Ltac1.of_constr s) (Ltac1.of_constr c) (Ltac1.of_constr q));
     constr:(IAnon $c)
  end.


Ltac2 i_intro_n (n : constr) :=
  lazy_match! goal with
  | [|- _ -> ?p] => intro
  | [|- _ ] =>
    i_start_proof ();
    lazy_match! goal with
    | [|- @envs_entails _ _ (@bi_wand _ _ _)] =>
        i_intro_constr n
    | [|- @envs_entails _ _ (@bi_impl _ _ _)] =>
        i_intro_constr n
    end
end.

Ltac2 i_intro () :=
  i_start_proof;
  i_intro_n (i_fresh_fun ()).

Ltac2 i_split () :=
  failwith (i_start_proof) ("couldn't start proof in i_split");
  refine '(tac_and_split _ _ _ _ _ _ _) >
  [() | () | i_solve_tc () | () | ()].

Ltac2 i_get_ctx () :=
  lazy_match! goal with
  | [|- @envs_entails _ ?d _ ]  => d
  | [|- context[ @envs_split _ _ _ ?d]] => d
end.


Ltac2 i_split_l (hs : constr) :=
  failwith (i_start_proof) ("couldn't start proof in i_split_l");
  let listed := constr:(fmap (INamed) $hs)
  in refine '(tac_sep_split _ Left $listed _ _ _ _ _) >
  [ () | ()
  | i_solve_tc ()
  | ltac1:(pm_reduce);
    lazy_match! goal with
    | [ |- False] => Control.zero (Iriception (os "hypothesis " ++
                                          oc hs ++  os "not found"))
    | [ |- _] => split > [() | ()]
    end
  ].

Ltac2 i_split_r (hs : constr) :=
  failwith (i_start_proof) ("couldn't start proof in i_split_l");
  (*let g := i_get_ctx() in*)
  refine '(tac_sep_split _ Right ($hs)) >
  [ i_solve_tc ()
  | ltac1:(pm_reduce);
    lazy_match! goal with
    | [ |- False] => Control.zero(iriception "hypotheses not found")
    | [ |- _] => split > [() | ()]
    end
  ].

Ltac2 i_and_destruct h k l :=
  refine '(tac_and_destruct _ $h _ $k $l _ _ _ _ _ _ _) >
  [() | () | () | ()
  | ltac1:(pm_reflexivity)
  | ltac1:(pm_reduce); i_solve_tc ()
  | ltac1:(pm_reduce);
    lazy_match! goal with
    | [|- False] =>
       Control.zero (Iriception (os("iAndDestruct:") ++ (oc k) ++ (os "or") ++ (oc l) ++ (os "not fresh")))
    | [|- _] => ()
    end
  ].

Ltac2 i_and_destruct_choice h d l :=
  refine '(tac_and_destruct_choice _ $h _ $d $l _ _ _ _ _ _ _) >
  [ () | () | () | ()
  | ltac1:(pm_reflexivity) | ltac1:(pm_reduce); i_solve_tc ()
  | ltac1:(pm_reduce)
  ].

Ltac2 i_exact h :=
  refine '(tac_assumption _ $h _ _ _ _ _ _) >
  [() | () | ltac1:(pm_reflexivity)
  | i_solve_tc ()
  | ltac1:(pm_reduce); i_solve_tc ()].

Ltac2 i_stop_proof () :=
  lazy_match! goal with
  | [|- @envs_entails _ _ _] => refine '(tac_stop _ _ _) > [ltac1:(pm_reduce)]
  | [|- _ : _] => Control.zero (iriception "iStopProof: proofmode not started")
  end.


Ltac2 i_assumption_coq () :=
  (*let h := fresh () in*)
  match! goal with
  | [ hn : ⊢ ?p |- envs_entails _ ?q] =>
      let (hc : constr) := Control.hyp (hn) in
      (*assert (FromAssumption true $p $q) as $h > [i_solve_tc ()|];*)
      refine '(tac_assumption_coq _ $p _ $hc _ _) >
      [ (*exact $h*) i_solve_tc ()
      | ltac1:(pm_reduce); i_solve_tc ()]
  end.

Ltac2 i_assumption () :=
  (*let h := fresh () in*)
  let rec find p g q :=
      lazy_match! g with
      | Esnoc ?gg ?j ?pp =>
        first [ (*assert (FromAssumption $p $pp $q) as $h > [i_solve_tc ()|];*)
                refine '(tac_assumption _ $j $p $pp _ _ _ _) >
                [ ltac1:(pm_reflexivity)
                | (*exact &h*) i_solve_tc ()
                | ltac1:(pm_reduce); i_solve_tc ()]
              | (*assert ($pp = False%I) as h by reflexivity;*)
                refine '(tac_false_destruct _ $j $p $pp) >
                [ ltac1:(pm_reflexivity)
                | (*exact &h*) reflexivity]
              | find p gg q]
      end
  in
  lazy_match! goal with
  | [|- @envs_entails _ (@Envs _ ?gp ?gs _) ?q] =>
     first [find '(true) gp q
           |find '(false) gs q
           |i_assumption_coq ()
           |Control.zero (Iriception (oc q ++ os " not found"))]
  end.

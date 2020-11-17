From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import base.
From iris.proofmode Require Export classes notation.
Set Default Proof Using "Type".

From Local Require Import named_prop.
From Local Require Export named_prop_notation.
From Local Require Import splitting_imatch.
From Local Require Import connection.

From Ltac2 Require Import Ltac2.

From Local Require utils.
Import utils.Misc utils.Iriception utils.Evars.

From Local Require ltac2_tactics.
From Local Require Import splitting_tactics.

Set Default Proof Using "Type".
Export ident.


Ltac2 Type ident_ltac2 := Init.constr.
Ltac2 new_constraint () := new_evar_with_cast '(bool).

Ltac2 Notation "parse_strategy" s(strategy) := s.
Ltac2 Notation red_flags_default := parse_strategy.

Ltac2 assert_as_id (c : constr) (i : ident):=
  Std.assert (Std.AssertType
               (Some (Std.IntroNaming (Std.IntroIdentifier i)))
               c
               None).

Ltac2 rec unify_with_bool (e : constr) (b : bool) :=
  let er := Std.eval_cbn red_flags_default e in
  lazy_match! er with
  | negb ?b0 => unify_with_bool b0 (Bool.neg b)
  | andb ?b1 ?b2 =>
    unify_with_bool b1 b; match b with
    | true => (unify_with_bool b2 true)
    | false => ()
    end
  | orb ?b1 ?b2 => match b with
    | true => (unify_with_bool b1 true; unify_with_bool b2 true)
    | false =>  (unify_with_bool b1 false)
    end
  | ?b0 =>
     let br := match b with true => '(true) | _ => '(false) end in
     unify0 b0 br
  end.

Ltac2 rec unify_constr_true (e : constr) := unify_with_bool e true.

Ltac2 rec unify_constr_false (e : constr) := unify_with_bool e false.

Ltac2 reduce_const () := (parse_strategy [
  fst snd (* for some reason doesn't get reduced on its own, even when introduced as match in tac_and_destruct_split *)
  base.Pos_succ base.ascii_beq base.string_beq
  base.positive_beq base.ident_beq

  connection.translate_envs connection.translate_env

  named_prop.get_ident
  named_prop.env_lookup named_prop.env_lookup_with_constr
  named_prop.env_lookup_true
  named_prop.env_delete
  named_prop.env_app named_prop.env_replace
  named_prop.env_intuitionistic named_prop.env_spatial
  named_prop.env_counter named_prop.env_spatial_is_nil
  named_prop.env_Forall

  named_prop.envs_lookup named_prop.envs_lookup_with_constr
  named_prop.envs_lookup_true  named_prop.envs_delete
  named_prop.envs_snoc named_prop.envs_app
  named_prop.envs_simple_replace named_prop.envs_replace
  named_prop.envs_simple_subst named_prop.env_subst
  named_prop.envs_split named_prop.envs_clear_spatial
  named_prop.envs_clear_intuitionistic named_prop.envs_incr_counter
  named_prop.envs_split

  pm_app pm_option_bind pm_from_option pm_option_fun].(Std.rConst)).

Ltac2 reduce_force_const () := (parse_strategy [negb andb orb]).(Std.rConst).

Ltac2 pm_reduce_force0 (force : bool) :=
  Std.cbv {
      Std.rBeta  := true;
      Std.rMatch := true;
      Std.rFix   := true;
      Std.rCofix := true;
      Std.rZeta  := true;
      Std.rDelta := false; (* rDelta true = delta all but rConst;
                          rDelta false = delta only on rConst *)
      Std.rConst := match force with
                | true => List.append (reduce_const ())
                                     (reduce_force_const ())
                | _ => reduce_const ()
                end
  } (default_on_concl None);
  ltac2_tactics.pm_reduce ().

(* pm_reduce and pm_reflexivity don't and shouldn't reduce negb,
   since we want to use them for lookups with constraints *)
Ltac2 pm_reduce () := pm_reduce_force0 false.
Ltac2 pm_reflexivity () :=
  pm_reduce (); exact eq_refl.

(* However, we need to compute when doing TC search or looking up present resources *)
Ltac2 pm_reduce_force () := pm_reduce_force0 true.
Ltac2 pm_force_reflexivity () :=
  pm_reduce_force (); exact eq_refl.

Ltac2 pm_prettify () :=
  let env_expressions :=
    failwith
    (fun () => lazy_match! goal with
    | [|- context [@envs_entails _ (@Envs _ ?gp ?gs _) _]] =>
      List.map (fun xyz => match xyz with (x,_,_) => x end)
               (List.append (env_to_list gp) (env_to_list gs))
    end) "coulnd't take apart env" in
  let check_if_evals (c : coq_boolean) :=
    let ce := Std.eval_hnf c in
    lazy_match! ce with
    | false => true
    | true => true
    | _ => false
    end in
  let _ :=
    List.map (fun c => (ltac1:(c |- let c1 := (eval compute in c) in
                                change_no_check c with c1) (Ltac1.of_constr c)))
             (List.filter check_if_evals env_expressions) in
  ltac2_tactics.pm_prettify ().

Ltac2 i_solve_tc := ltac2_tactics.i_solve_tc.

Ltac2 Type context_choice := [Spatial | Intuitionistic].

Ltac2 select_hypothesis_from_context condition selected others con :=
  let fst xy := match xy with (x,_) => x end in
  let snd xy := match xy with (_,y) => y end in
  let l := List.map (fun xyz => match xyz with (x,y,_) => (x,y) end)
                    (env_to_list con) in
  let (hh, rest) := List.partition (fun x => condition (snd x)) l in
  let _ := List.iter selected (List.map fst hh) in
  let _ := List.iter others (List.map fst rest) in
  ().

Ltac2 select_hypothesis (sel : context_choice) condition selected others e :=
  lazy_match! e with
  | (@Envs _ ?gp ?gs _) =>
    select_hypothesis_from_context condition selected others
                                   (match sel with
                                    | Spatial => gs
                                    | Intuitionistic => gp
                                   end)
  end.

Ltac2 only_selected sel condition e :=
  select_hypothesis sel
                    condition
                    (fun x => unify_constr_true x)
                    (fun x => unify_constr_false x) e.

Ltac2 try_only_selected sel condition e :=
  select_hypothesis sel
                    condition
                    (fun x => try (unify_constr_true x))
                    (fun x => try (unify_constr_false x)) e.

Ltac2 ensure_selected sel condition e :=
  select_hypothesis sel
                    condition
                    (fun x => unify_constr_true x)
                    (fun _ => ()) e.

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
     (let f :=
        ltac1:(pr1 pr2 p s c q |-
               let c1 := (eval vm_compute in (Pos.succ c)) in
               change_no_check (@envs_entails pr1 (@Envs pr2 p s c1) q)) in
     let lc := Ltac1.of_constr in
     f (lc pr1) (lc pr2) (lc p) (lc s) (lc c) (lc q));
     constr:(IAnon $c)
end.

Ltac2 i_clear_hyp (x : ident_ltac2) :=
  refine '(tac_clear _ $x _ _ _ _ _ _ _) >
  [ () | () | ()
  | pm_reflexivity ()
  | pm_reduce (); i_solve_tc ()
  | pm_reduce ()].

Ltac2 i_clear_false_hyp (x : ident_ltac2) :=
  refine '(tac_clear_false _ $x _ _ _ _ _) >
  [ () | ()
  | pm_force_reflexivity ()
  | pm_reduce ()].

Ltac2 rec i_clear_false_hyps (x : ident_ltac2 list) :=
  match x with
  | [] => ()
  | xh :: xs => i_clear_false_hyp xh; i_clear_false_hyps xs
  end.

Ltac2 i_cleanup () :=
  let env :=
    lazy_match! goal with
    | [|- @envs_entails _ (@Envs _ ?gp ?gs _) _] =>
      List.map (fun xyz => match xyz with (x,y,_) => (x,y) end)
               (List.append (env_to_list gp) (env_to_list gs))
    end in
  let check_if_false (c : coq_boolean) :=
    let ce := Std.eval_hnf c in
    match! ce with
    | false => true
    | _ => false
    end in
  let to_clean :=
      List.map
        (fun b_i => match b_i with (b,i) => i end)
        (List.filter
           (fun b_i => match b_i with (b,i) => check_if_false b end)
           env) in
  Control.enter (fun () => pm_prettify (); i_clear_false_hyps to_clean).

Ltac2 i_pure0 (h : ident_ltac2) (x : Std.intro_pattern) :=
  lazy_match! goal with
  | [|- @envs_entails _ ?g _] =>
    try_only_selected Intuitionistic (Constr.equal h) g;
    try_only_selected Spatial (Constr.equal h) g
  end;
  refine '(splitting_tactics.tac_pure _ $h _ _ _ _ _ _ _ _) >
  [ | |
  | pm_force_reflexivity ()
  | i_solve_tc ()
  | pm_reduce_force (); i_solve_tc ()
  | pm_reduce (); intros0 false [x]].

Ltac2 Notation "i_pure" h(self) "as" p(intropattern) := i_pure0 h p.

Ltac2 i_emp_intro () :=
  i_start_split_proof ();
  refine '(tac_emp_intro _ _) > [i_solve_tc ()].

Ltac2 i_pure_intro () :=
  i_start_split_proof ();
  refine '(tac_pure_intro _ _ _ _ _ _ _) >
  [ | | i_solve_tc () | pm_reduce (); i_solve_tc () | ].

(** Framing *)

Ltac2 i_frame_finish () :=
  pm_prettify ();
  try (lazy_match! goal with
      | [|- @envs_entails _ _ ((True)%I)] => now (i_pure_intro ())
      | [|- @envs_entails _ _ (emp%I)] => i_emp_intro ()
      end).

Ltac2 i_frame_pure_constr (t : constr) :=
  i_start_split_proof ();
  refine '(tac_frame_pure _ _ _ _ $t _ _) >
  [ () | i_solve_tc () | i_frame_finish ()].

Ltac2 i_frame_pure0 (i : ident) :=
  i_frame_pure_constr (Control.hyp i).

Ltac2 Notation "i_frame_pure" i(ident) :=
  i_frame_pure0 i.

Ltac2 i_frame_hyp (h : ident_ltac2) :=
  i_start_split_proof ();
  lazy_match! goal with
  | [|- @envs_entails _ ?e _] =>
    ensure_selected Spatial (Constr.equal h) e;
    ensure_selected Intuitionistic (Constr.equal h) e
  end;
  refine '(tac_frame _ $h _ _ _ _ _ _ _) >
  [ () | () | ()
  | pm_force_reflexivity ()
  | i_solve_tc ()
  | pm_reduce (); i_frame_finish ()].

Ltac2 i_frame_any_pure () :=
  repeat (match! goal with [h : _ |- _] => i_frame_pure0 h end).

Ltac2 i_frame_any_intuitionistic () :=
  i_start_split_proof ();
  let rec go ls := match ls with
    | [] => ()
    | lh :: lt => repeat (i_frame_hyp lh); go lt
    end in
  lazy_match! goal with
  | [|- @envs_entails _ (@Envs _ ?gp ?gs _) ?q] =>
     let l := List.map (fun xyz => match xyz with (_,y,_) => y end)
                       (env_to_list gp) in
     go l
  end.

Ltac2 i_frame_any_spatial () :=
  i_start_split_proof ();
  let rec go ls := match ls with
    | [] => ()
    | lh :: lt => repeat (i_frame_hyp lh); go lt
    end in
  lazy_match! goal with
  | [|- @envs_entails _ (@Envs _ ?gp ?gs _) ?q] =>
     let l := List.map (fun xyz => match xyz with (_,y,_) => y end)
                       (env_to_list gs) in
     go l
  end.

Ltac2 i_frame () := i_frame_any_spatial ().

(** * Basic introduction tactics *)
Ltac2 i_intro_pat0 (x : Std.intro_pattern) :=
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
        | pm_prettify (); intros0 false [x]]
      end).


Ltac2 Notation "i_intro_pat" p(intropattern) := i_intro_pat0 p.

Ltac2 i_intro_spatial_ident (x: ident_ltac2) :=
  failwith (i_start_split_proof) "Couldn't start splitting proof in intro_constr";
  or
    (fun () => refine '(@tac_impl_intro _ _ $x _ _ _ _ _ _ _ _) >
            [ () | () | ()
            | i_solve_tc ()
            | pm_reduce_force (); i_solve_tc ()
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
        | i_solve_tc ()
        | i_solve_tc ()
        | i_solve_tc ()
        | pm_reduce ()]).

Ltac2 i_intro_ident (x : ident_ltac2) :=
  or (fun () => i_intro_intuitionistic_ident x)
     (fun () => i_intro_spatial_ident x).

Ltac2 i_exact_spatial h :=
  lazy_match! goal with
  | [|- @envs_entails _ ?e _] =>
    only_selected Spatial (Constr.equal h) e;
    (* try to clear intuitionisctic hyps too *)
    try_only_selected Intuitionistic (fun x => false) e
  end;
  refine '(tac_assumption _ $h _ _ _ _ _ _) >
  [ () | ()
  | pm_force_reflexivity ()
  | i_solve_tc ()
  | pm_reduce_force (); i_solve_tc ()].

Ltac2 i_exact_intuitionistic h :=
  lazy_match! goal with
  | [|- @envs_entails _ ?e _] =>
    (* try remove all spatial hypothesis *)
    try_only_selected Spatial (fun x => false) e;
    ensure_selected Intuitionistic (Constr.equal h) e
  end;
  refine '(tac_assumption _ $h _ _ _ _ _ _) >
  [ () | ()
  | pm_force_reflexivity ()
  | i_solve_tc ()
  | pm_reduce_force (); i_solve_tc ()].

Ltac2 i_exact h :=
  or (fun () => i_exact_intuitionistic h)
     (fun () => i_exact_spatial h).

(* Ltac2 i_exact_name (c : constr) :=
 *  let n := constr:(INamed $c) in
 *  i_exact_spatial n.
 *
 * Ltac2 Notation "i_exact" c(constr) := i_exact_name c.
 *)

Ltac2 i_assumption_coq () :=
  let fr := fresh () in
  (* using match! instead of lazy_match since it can be that there're
     two differnt derivations in the context and we want to backtrack on
     the unfortunate attempt *)
  match! goal with
  | [h : (⊢ ?p) |- envs_entails _ ?q] =>
    assert_as_id '(FromAssumption true $p $q) fr > [i_solve_tc ()|];
    refine '(tac_assumption_coq _ $p $q _ _ _) >
    [ refine (Control.hyp h)
    | refine (Control.hyp fr)
    | pm_reduce (); i_solve_tc ()]
  end.

Ltac2 i_assumption0 () :=
  let h := fresh () in
  let rec find p gamma g q :=
    lazy_match! g with
    | Esnoc ?gg (_,?j) ?pp =>
      first [ (*assert (FromAssumption $p $pp $q) as $h > [i_solve_tc ()|];*)
              match p with
              | false => i_exact_spatial j
              | true => i_exact_intuitionistic j
              end
            | assert_as_id '($pp = False%I) h > [reflexivity];
              match p with
              | true => (* means intuitionistic *)
                only_selected Intuitionistic (Constr.equal j) gamma;
                try_only_selected Spatial (fun _ => false) gamma
              | false => (* means spatial *)
                only_selected Spatial (Constr.equal j) gamma;
                try_only_selected Intuitionistic (fun _ => false) gamma
              end;
              let pf := match p with true => '(true) | _ => '(false) end in
              refine '(tac_false_destruct _ $j $pf $pp _ _ _) >
              [ pm_force_reflexivity ()
              | refine (Control.hyp h)]
            | find p gamma gg q]
    end
  in
  lazy_match! goal with
  | [|- @envs_entails _ ?g ?q] =>
     lazy_match! g with
     | (@Envs _ ?gp ?gs _) =>
     first [ find true g gp q
           | find false g gs q
           | i_assumption_coq ()
           | Control.zero (Iriception (os "no assumption matching " ++ oc q ++ os " was found"))]
     end
end.

Ltac2 i_assumption () := Control.enter i_assumption0.
      
Ltac2 i_specialize (f : ident_ltac2) (a : ident_ltac2) (n : ident_ltac2) :=
  lazy_match! goal with
  | [|- @envs_entails _ ?e _] =>
    (* remove all spatial hypothesis *)
    select_hypothesis Spatial (fun x => Bool.or (Constr.equal f x) (Constr.equal a x))
                      unify_constr_true (fun _ => ()) e;
    select_hypothesis Intuitionistic (fun x => Bool.or (Constr.equal f x) (Constr.equal a x))
                      unify_constr_true (fun _ => ()) e
  end;
  refine '(tac_specialize_with_constr _ $a $f $n true true true _ _ _ _ _ _ _ _ _ _) >
  [ () | () | () | () | ()
  | pm_force_reflexivity ()
  | pm_force_reflexivity ()
  | i_solve_tc ()
  | pm_reduce (); i_cleanup (); pm_prettify () ].

Ltac2 i_specialize_assert (f : ident_ltac2) :=
  let n :=
    lazy_match! goal with
    | [|- @envs_entails _ (@Envs _ ?gp ?gs _) ?q] =>
        (* "f" doesn't need a new constraint *)
        Int.sub (List.length (env_to_list gs)) 1
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
  (* unify expression attached to "f" with true *)
  lazy_match! goal with
  | [|- @envs_entails _ ?e _] =>
    (* remove all spatial hypothesis *)
    ensure_selected Spatial (Constr.equal f) e;
    ensure_selected Intuitionistic (Constr.equal f) e
  end;
  refine '(tac_specialize_assert _ $f _ false $bs _ _ _ _ _ _ _ _ _) >
  [ () | () | () | () | ()
  | pm_force_reflexivity ()
  | i_solve_tc ()
  | pm_reduce (); i_solve_tc ()
  | pm_reduce (); split > [i_cleanup ()| i_cleanup ()]].

Ltac2 i_apply_one (h : ident_ltac2) :=
  lazy_match! goal with
  | [|- @envs_entails _ ?e _] =>
    (* remove all spatial hypothesis *)
    ensure_selected Spatial (Constr.equal h) e;
    ensure_selected Intuitionistic (Constr.equal h) e
  end;
  refine '(tac_apply _ $h _ _ _ _ _ _ _) >
  [ () | () | ()
  | pm_force_reflexivity ()
  | i_solve_tc ()
  | pm_reduce ()].

Ltac2 rec i_apply_loop (f : ident_ltac2) :=
  first [ i_apply_one f
        | i_specialize_assert f > [ | i_apply_loop f]].

Ltac2 i_apply_ident (f : ident_ltac2) :=
  first [ i_exact f
        | i_apply_loop f
        | Control.zero (Iriception (os "can't apply " ++ oc f))
        ].

(* TODO: tac_forall_specialize *)

(* TODO: i_pose *)

(* TODO: i_revert *)

Ltac2 i_and_destruct (x : ident_ltac2)
                     (y : ident_ltac2)
                     (z : ident_ltac2) :=
  refine '(tac_and_destruct _ $x _ $y $z _ _ _ _ _ _ _ _) >
  [ () | () | () | () | ()
  | pm_reflexivity ()
  | pm_reduce_force (); i_solve_tc ()
  | pm_reduce ()].

Ltac2 i_and_destruct_split0 (x : ident_ltac2)
                            (y : ident_ltac2)
                            (z : ident_ltac2)
                            (c : constr) :=
  refine '(tac_and_destruct_split _ $x _ $y $z _ $c _ _ _ _ _ _ _) >
  [ () | () | () | () | ()
  | pm_reflexivity ()
  | i_solve_tc ()
  | pm_reduce () ].

Ltac2 i_and_destruct_split (x : ident_ltac2)
                           (y : ident_ltac2)
                           (z : ident_ltac2) :=
  let c := new_constraint () in
  i_and_destruct_split0 x y z c.

Ltac2 i_and_destruct_left (x : ident_ltac2)
                           (y : ident_ltac2) :=
  let c := '(true) in
  let i := i_fresh_fun () in
  i_and_destruct_split0 x y i c; i_cleanup ().

Ltac2 i_and_destruct_right (x : ident_ltac2)
                           (z : ident_ltac2) :=
  let c := '(false) in
  let i := i_fresh_fun () in
  i_and_destruct_split0 x i z c; i_cleanup ().

Ltac2 i_left () :=
  refine '(tac_or_l _ _ _ _ _ _) > [() | () | i_solve_tc () | ()].

Ltac2 i_right () :=
  refine '(tac_or_r _ _ _ _ _ _) > [() | () | i_solve_tc () | ()].

Ltac2 i_or_destruct (x : ident_ltac2)
                    (y : ident_ltac2)
                    (z : ident_ltac2) :=
  refine '(tac_or_destruct _ $x _ $y $z _ _ _ _ _ _ _ _) >
  [ () | () | () | () | ()
  | pm_reflexivity ()
  | i_solve_tc ()
  | pm_reduce(); split ].

Ltac2 i_exists_one (x : constr) :=
  i_start_split_proof ();
  refine '(tac_exist _ _ _ _ _) >
  [ () | ()
  | i_solve_tc ()
  | exists0 true [(fun () => Std.ImplicitBindings ([x]))]].

Ltac2 rec i_exists0 (x : constr list) :=
  match x with
  | [] => ()
  | xh :: xs =>
    let _ := i_exists_one xh in
    i_exists0 xs
  end.

Ltac2 Notation "i_exists" x(list1(open_constr)) := i_exists0 x.

Ltac2 i_exist_destruct0 (i : ident_ltac2) (j : ident_ltac2) (x : Std.intro_pattern) :=
  refine '(splitting_tactics.tac_exist_destruct _ $i _ $j _ _ _ _ _ _) >
  [ () | () | () | ()
  | pm_force_reflexivity ()
  | i_solve_tc ()
  | intros0 false [x]; pm_reduce () ].

Ltac2 Notation "i_exist_destruct" i(self) "as" x(intropattern) j(self) :=
  i_exist_destruct0 i j x.

Ltac2 i_and_split () :=
  i_start_split_proof ();
  refine '(tac_and_split _ _ _ _ _ _ _) >
  [ () | ()
  | i_solve_tc ()
  | () | () ].

Ltac2 i_sep_split () :=
  let n :=
    lazy_match! goal with
    | [|- @envs_entails _ (@Envs _ ?gp ?gs _) ?q] => List.length (env_to_list gs)
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
  lazy_match! goal with
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

Ltac2 i_split () :=
  or (i_sep_split) (i_and_split).

Ltac2 get_modality () :=
  let fresh_id := fresh () in
  lazy_match! goal with
  | [|- @envs_entails ?prop2 _ ?p ] =>
    let prop1 := new_evar '(bi) in
    let q := new_evar prop1 in
    let m := new_evar '(modality $prop1 $prop2) in
    let selA := new_evar '(Type) in
    let sel := new_evar selA in
    let assertion () := (Std.AssertType
                           (Some (Std.IntroNaming (Std.IntroIdentifier fresh_id)))
                           '(FromModal $m $sel $p $q)
                           None) in
    enter_h true (fun _ ast => Std.assert ast) assertion
  end;
  Control.focus 1 1 i_solve_tc; (* enter just asserted goal and solve it with i_solve_tc *)
  let (_,_,v) := (* get the type of just proved goal *)
    List.find (fun xyz => match xyz with
                         (x, _, _) => Ident.equal x fresh_id
                       end)
              (Control.hyps ()) in
  Std.clear [fresh_id]; (* remove asserted goal *)
  match! v with
  | FromModal ?sel _ _ _ => sel
  end.

Ltac2 i_mod_intro () :=
  let modality := get_modality () in
  let intuitionistic_action := Std.eval_hnf '(modality_intuitionistic_action $modality) in
  let spatial_action := Std.eval_hnf '(modality_spatial_action $modality) in
  let _ := match! intuitionistic_action with
  | MIEnvIsEmpty => i_cleanup ()
  | MIEnvForall ?c => i_cleanup ()
  | MIEnvTransform ?c => i_cleanup ()
  | MIEnvClear => i_cleanup ()
  | MIEnvId => ()
  end in
  let _ := match! spatial_action with
  | MIEnvIsEmpty => i_cleanup ()
  | MIEnvForall ?c => i_cleanup ()
  | MIEnvTransform ?c => i_cleanup ()
  | MIEnvClear => i_cleanup ()
  | MIEnvId => ()
  end in
  refine '(tac_modal_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ) >
  [ | | | | | | |
  | i_solve_tc () (* FromModal ?M ?sel ?P ?Q *)
  | i_solve_tc () (* IntoModalIntuitionisticEnv *)
  | i_solve_tc () (* IntoModalSpatialEnv *)
  | pm_reduce (); i_solve_tc () (* if ?fi then Absorbing (...) else TCTrue *)
  | pm_prettify ()].

(* TODO: battle-test this *)
(* FIME: add solve_side_condition *)
Ltac2 i_mod_core (i : constr) :=
  lazy_match! goal with
  | [|- @envs_entails _ ?e _] =>
    select_hypothesis Spatial (fun x => Constr.equal x i) unify_constr_true (fun _ => ()) e;
    select_hypothesis Intuitionistic (fun x => Constr.equal x i) unify_constr_true (fun _ => ()) e
  end;
  refine '(tac_modal_elim _ $i _ _ _ _ _ _ _ _ _ _ _) >
  [ | | | | | | | |
  | pm_force_reflexivity ()
  | i_solve_tc ()
  | (*TODO: i_solve_side_conditions *)
  | pm_reduce (); pm_prettify ()].

(* TODO: iris intropatterns *)
(* Ltac2 i_intros *)

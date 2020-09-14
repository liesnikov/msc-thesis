From iris.bi Require Export bi telescopes.
From iris.proofmode Require Export base classes notation.
Set Default Proof Using "Type".

From Local Require Import named_prop.
From Local Require Import connection.

From Ltac2 Require Import Ltac2 Std.

From Local Require utils.
Import utils.Misc utils.Iriception utils.Evars.

From Local Require Import splitting_tactics splitting_ltac2_tactics.


(* Reserved Notation "⫫" (at level 10). *)
Inductive not_false :=.
(* where "⫫" := not_false. *)

Inductive sep :=.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Pattern Option.
From Local Require utils.
Import utils.Iriception utils.Misc utils.Array utils.Iriception.

Ltac2 Type kinded_pattern := (Pattern.match_kind * Pattern.t).
Ltac2 Type kinded_patterns := kinded_pattern list.

Ltac2 Type exn ::= [IMatch_failure].

Ltac2 rec env_to_list e :=
  lazy_match! e with
  | Esnoc ?gg ?j ?pp => (j,pp) :: env_to_list gg
  | _ => []
end.

Ltac2 Type iris_id := constr.
Ltac2 Type iris_prop := constr.

Ltac2 i_match_term (kpat : kinded_pattern) (term : constr) :=
  let (k, pat) := kpat in
  match k with
  | Pattern.MatchPattern =>
    orelse (fun () => (Pattern.matches_vect pat term, None))
           (fun e => Control.zero (match e with
                                | Match_failure => IMatch_failure
                                | _ => e
                                end))
  | Pattern.MatchContext =>
    orelse (fun _ => let (context, bind) := Pattern.matches_subterm_vect pat term in
                  (bind, Some context))
           (fun e => Control.zero (match e with
                                | Match_failure => IMatch_failure
                                | _ => e
                                end))
  end.

Ltac2 rec pick_match_rec
      (acc : (iris_id * iris_prop) list)
      (env : (iris_id * iris_prop) list)
      (kpat : kinded_pattern)
  :=let bogus := '(1) in (* placeholder constr *)
    match env with
    | [] => Control.zero IMatch_failure
    | eh :: et =>
      let (id, prop) := eh in
      let constraint := Std.eval_red '(fst $id) in
      let ident := Std.eval_red '(snd $id) in
      List.fold_left
        (fun x y () => Control.plus x y)
        [(** * First try to match just the PROP *)
         (fun _ => let (bins, ctxs) := i_match_term kpat prop in
                let is_false := Constr.equal (Std.eval_vm None constraint)
                                            '(false) in
                match is_false with
                | true => Control.zero (IMatch_failure)
                | false => (ident, bins, ctxs, List.append (List.rev acc) et)
                end);
         (** * Then try to match both the constraint and the prop *)
         (fun _ =>
            let (bins, ctxs) :=
                match (Control.case
                         (fun () => i_match_term kpat '($bogus, $prop))) with
                | Err _ =>
                  (* pattern for boolean constraint isn't a wildcard
                 which means it might be not_false,
                 so we should check that first *)
                  or (fun () =>
                        let (b,c) := i_match_term kpat '(not_false, $prop) in
                        let is_false := Constr.equal (Std.eval_vm None constraint)
                                                     '(false) in
                        match is_false with
                        | true => Control.zero (IMatch_failure)
                        | false => (b,c)
                        end)
                     (fun () => i_match_term kpat '($constraint, $prop))
                | Val _ =>
                  (* pattern for boolean constraint is a wildcard *)
                  i_match_term kpat '($constraint, $prop)
                end in (ident, bins, ctxs, List.append (List.rev acc) et));
         (** * Last thing - don't use this hypothesis at all *)
         (fun _ => pick_match_rec (eh :: acc) et kpat)]
        (fun () => Control.zero IMatch_failure) ()
    end.

Ltac2 pick_match (env : (iris_id * iris_prop) list) (kpat : kinded_pattern) :=
  pick_match_rec [] env kpat.

Ltac2 rec i_match_ihyps_list
      (pats : kinded_patterns)
      (env : (iris_id * iris_prop) list)
  := match pats with
     | [] => ([],[],[])
     | p :: pats' =>
       let (i, b, c, env') := pick_match env p in
       let (it, bt, ct) := i_match_ihyps_list pats' env' in
       (i:: it, b :: bt, c :: ct)
     end.

Ltac2 Type ('a, 'b, 'c) trisum := [First ('a) | Second ('b) | Third ('c)].

Ltac2 split_pat_list_with_sep plist :=
  let bogus := '(1) in (* placeholder constr *)
  let rec go acc rest :=
      match rest with
      | [] => acc
      | rh :: restl =>
        let isnt_sep () := match acc with
          | First a =>
            go (First (rh :: a)) restl
          | Second ab =>
            let (a, b) := ab in
            go (Second (rh :: a, b)) restl
          | Third abc =>
            let (a,b,c) := abc in
            go (Third (rh :: a, b, c)) restl
          end in
        (* match against bogus term to find out whether the pattern is wildcard *)
        match (Control.case (fun () => i_match_term rh bogus)) with
        | Val _ =>
          (* The pattern is a wildcard, so it's not sep *)
          isnt_sep ()
        | Err _ =>
          (* The pattern is not a wildcard *)
          or (fun () =>
                i_match_term rh '(sep);
                (* if we get here, then previous expr didn't fail,
                   so the rh pattern _is_ sep
                   then we drop it and start a new partition in acc *)
                match acc with
                | First a => go (Second ([], a)) restl
                | Second ab => let (a, b) := ab in go (Third ([], a, b)) restl
                | Third abc => iriception "more than two separators in iMatch"
                end)
             (fun e => isnt_sep ())
        end
      end in
  go (First []) (List.rev plist).

Ltac2 i_match_ihyps
      (pats : kinded_patterns)
      (penv : constr)
      (senv : constr)
  := let bogus := '(1) in (* placeholder constr *)
     let penvl := env_to_list penv in
     let senvl := env_to_list senv in
     let (ids, bins, ctxs) :=
         match (split_pat_list_with_sep pats) with
         | First pats =>
           i_match_ihyps_list pats (List.append penvl senvl)
         | Second split_pats =>
           let (ppats, spats) := split_pats in
           let (ids1, bins1, ctxs1) :=
             i_match_ihyps_list ppats penvl in
           let (ids2, bins2, ctxs2) :=
             i_match_ihyps_list spats senvl in
           (List.append ids1 ('(sep) :: ids2),
            List.append bins1 bins2,
            List.append ctxs1 (None :: ctxs2))
         | Third lll =>
           iriception "Not implemented"
         end in
     let bins' := List.flat_map (fun x => to_list x) bins in
     let ctxs' := List.flat_map (Option.map_default (fun e => [e]) []) ctxs in
     (of_list ids   bogus,
      of_list bins' bogus,
      of_list ctxs' (Pattern.empty_context())).

Ltac2 i_match_igoal conclpat concl :=
  let (knd, pat) := conclpat in
  match knd with
    | Pattern.MatchPattern =>
      let context := Pattern.empty_context () in
      let bind := Pattern.matches_vect pat concl in
      (bind, context)
    | Pattern.MatchContext =>
      let (context, bind) := Pattern.matches_subterm_vect pat concl in
      (bind, context)
    end.

Ltac2 i_matches_goal phyps pconcl :=
  lazy_match! goal with
  | [|- envs_entails (Envs ?p ?s ?c) ?q] =>
    let (hids, hsubst, hctx) := i_match_ihyps phyps p s in
    let (gsubst, gctx) := i_match_igoal pconcl q in
    let hsubstl := to_list hsubst in
    let gsubstl := to_list gsubst in
    (hids, hctx, of_list (List.append hsubstl gsubstl) '(1), gctx)
  | [|- _] => Control.zero (Tactic_failure (Some (os "The goal isn't of the right shape")))
  end.

Ltac2 i_lazy_match_goal pats :=
  let rec interp m := match m with
  | [] => Control.zero Match_failure
  | p :: mt =>
    let next _ := interp mt in
    let (pat, f) := p in
    let (phyps, pconcl) := pat in
    let cur _ :=
          let (hids, hctx, subst, cctx) := i_matches_goal phyps pconcl in
          fun () => f hids hctx subst cctx
    in Control.plus cur next
  end in
  Control.once (fun () => interp pats) ().

Ltac2 Notation "iLazyMatch!" "goal" "with" m(goal_matching) "end" :=
  i_lazy_match_goal m.

Ltac2 i_match_goal pats :=
  let rec interp m := match m with
  | [] => Control.zero Match_failure
  | p :: mt =>
    let next _ := interp mt in
    let (pat, f) := p in
    let (phyps, pconcl) := pat in
    let cur _ :=
        let (hids, hctx, subst, cctx) := i_matches_goal phyps pconcl in
        f hids hctx subst cctx
    in Control.plus cur next
  end in
  interp pats.

Ltac2 i_match_one_goal pats := Control.once (fun _ => i_match_goal pats).
Ltac2 Notation "iMatch!" "goal" "with" m(goal_matching) "end" :=
  i_match_one_goal m.

Ltac2 Notation "iMultiMatch!" "goal" "with" m(goal_matching) "end" :=
  i_match_goal m.

From iris.proofmode Require Import classes notation.
From Local Require Import ltac2_tactics.
Context {PROP : sbi}.
Implicit Types P Q R : PROP.

Set Ltac2 Backtrace.

Notation "'<' c '>' P" := (c%bool, P%I) (at level 10, c at level 0, only parsing).
Notation "'<?>' P" := (not_false, P%I) (at level 10, only parsing).
Notation "‖" := sep (only parsing).

Lemma test1 P Q : Q ⊢ □ (<absorb> P) -∗ Q.
Proof.
  i_start_split_proof ().
  i_intro_ident '(INamed "q").
  i_intro_ident '(INamed "p").
  (* i_intro_intuitionistic_ident '(INamed "p"). *)
  iLazyMatch! goal with
  | [h1 : <?> ?p |- ?p] => Message.print (oc p)
  end.

  iMatch! goal with
  | [h1 : _, h2 : (□ <absorb> _)%I |- ?p] =>
    i_clear_hyp h2; i_exact_spatial h1
  end.
Qed.

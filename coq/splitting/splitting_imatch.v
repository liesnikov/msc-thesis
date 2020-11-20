From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import base classes notation.
Set Default Proof Using "Type".

From Local Require Import named_prop.

From Ltac2 Require Import Ltac2 Std.

From Local Require utils.
Import utils.Misc utils.Iriception utils.Evars.


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
  | Esnoc ?gg (?b, ?j) ?pp => (b, j, pp) :: env_to_list gg
  | _ => []
end.

Ltac2 Type coq_boolean := constr.
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
      (acc : (coq_boolean * iris_id * iris_prop) list)
      (env : (coq_boolean * iris_id * iris_prop) list)
      (kpat : kinded_pattern)
  :=let bogus := '(1) in (* placeholder constr *)
    match env with
    | [] => Control.zero IMatch_failure
    | eh :: et =>
      let (constraint, ident, prop) := eh in
      List.fold_left
        (fun x y () => Control.plus x y)
        [(** * First try to match just the PROP *)
         (fun _ => let (bins, ctxs) := i_match_term kpat prop in
                let is_false := Constr.equal (Std.eval_vm None constraint)
                                             '(false) in
                (* If user matches just proposition, they probably don't want false props*)
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
                     which means it might be not_false, so we should check for this first *)
                  or (fun () =>
                        let (b,c) := i_match_term kpat '(not_false, $prop) in
                        let is_false := Constr.equal (Std.eval_vm None constraint)
                                                     '(false) in
                        match is_false with
                        | true => Control.zero (IMatch_failure)
                        | false => (b,c)
                        end)
                     (* pattern for boolean isn't a wildcard and isn't not_false,
                        so we just match it *)
                     (fun () => i_match_term kpat '($constraint, $prop))
                | Val _ =>
                  (* pattern for boolean constraint is a wildcard *)
                  i_match_term kpat '($constraint, $prop)
                end in (ident, bins, ctxs, List.append (List.rev acc) et));
         (** * Last thing - don't use this hypothesis at all *)
         (fun _ => pick_match_rec (eh :: acc) et kpat)]
        (fun () => Control.zero IMatch_failure) ()
    end.

Ltac2 pick_match (env : (coq_boolean * iris_id * iris_prop) list)
                 (kpat : kinded_pattern) :=
  pick_match_rec [] env kpat.

Ltac2 rec i_match_ihyps_list
      (pats : kinded_patterns)
      (env : (coq_boolean * iris_id * iris_prop) list)
  := match pats with
     | [] => ([],[],[])
     | p :: pats' =>
       let (i, b, c, env') := pick_match env p in
       let (it, bt, ct) := i_match_ihyps_list pats' env' in
       (i:: it, b :: bt, c :: ct)
     end.

Ltac2 Type ('a, 'b, 'c) trisum := [First ('a) | Second ('b) | Third ('c)].
Ltac2 Type ('a, 'b) match_ident := [CoqId ('a) | IpmId ('b) ].

Ltac2 coq_id x :=
  match x with
  | CoqId a => a
  | _ => Control.zero No_value
  end.

Ltac2 ipm_id x :=
  match x with
  | IpmId a => a
  | _ => Control.zero No_value
  end.

Ltac2 split_pat_list_with_sep plist :=
  let bogus := '(1) in (* placeholder constr *)
  let rec go acc rest :=
      match rest with
      | [] => acc
      | rh :: restl =>
        let isnt_sep_cont () := match acc with
          | First a =>
            go (First (rh :: a)) restl
          | Second ab =>
            let (a, b) := ab in
            go (Second (rh :: a, b)) restl
          | Third abc =>
            let (a,b,c) := abc in
            go (Third (rh :: a, b, c)) restl
          end in
        (* match against bogus term to find out whether the pattern is a wildcard *)
        match (Control.case (fun () => i_match_term rh bogus)) with
        | Val _ =>
          (* The pattern is a wildcard, so it's not sep *)
          isnt_sep_cont ()
        | Err _ =>
          (* The pattern is not a wildcard *)
          or (fun () =>
                let _ := i_match_term rh '(sep) in
                (* if we get here, then previous expr didn't fail,
                   so the rh pattern _is_ sep
                   then we drop it and start a new partition in acc *)
                match acc with
                | First a => go (Second ([], a)) restl
                | Second ab => let (a, b) := ab in go (Third ([], a, b)) restl
                | Third abc => iriception "more than two separators in iMatch"
                end)
             (fun e => isnt_sep_cont ())
        end
      end in
  (* the list has to be reversed since we start partitions from the right
     [coq env || intuitionistic env || spatial env] *)
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
           (* there is just one partition, match all hypotheses *)
           let (ids, bins, ctxs) := i_match_ihyps_list pats (List.append penvl senvl) in
           (List.map (fun x => IpmId x) ids, bins, ctxs)
         | Second split_pats =>
           (* two partitions, match intuitionistic and spatial envs separately *)
           let (ppats, spats) := split_pats in
           let (ids1, bins1, ctxs1) :=
             i_match_ihyps_list ppats penvl in
           let (ids2, bins2, ctxs2) :=
             i_match_ihyps_list spats senvl in
           (List.map (fun x => IpmId x) (List.append ids1 ('(sep) :: ids2)),
            List.append bins1 bins2,
            List.append ctxs1 (None :: ctxs2))
         | Third coq_intuitit_spat =>
           (* three partitions, match coq env, intuitionistic and spatial envs *)
           let (coqp, intuitp, spatp) := coq_intuitit_spat in
           let (ids1, ctxs1, bins1, _) :=
             Pattern.matches_goal false coqp (Pattern.MatchPattern, pattern:(_)) in
           let (ids2, bins2, ctxs2) :=
             i_match_ihyps_list intuitp penvl in
           let (ids3, bins3, ctxs3) :=
              i_match_ihyps_list spatp senvl in
           let coq_ids := List.map (fun x => CoqId x) (utils.Array.to_list ids1) in
           let ipm_ids := List.map (fun x => IpmId x) (List.append ('(sep) :: ids2) ('(sep) :: ids3)) in
           let ctxs_list := List.map (fun x => Some x) (utils.Array.to_list ctxs1) in
           (List.append coq_ids ipm_ids,
            List.append [bins1] (List.append bins2 bins3),
            List.append ctxs_list (List.append (None :: ctxs2) (None::ctxs3)))
         end in
     let bins' := List.flat_map (fun x => to_list x) bins in
     let ctxs' := List.flat_map (Option.map_default (fun e => [e]) []) ctxs in
     (of_list ids  (IpmId bogus),
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

Ltac2 i_matches_patterns_goal phyps pconcl :=
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
          let (hids, hctx, subst, cctx) := i_matches_patterns_goal phyps pconcl in
          fun () => f hids hctx subst cctx
    in Control.plus cur next
  end in
  Control.once (fun () => interp pats) ().

Ltac2 Notation "iLazyMatch!" "goal" "with" m(goal_matching) "end" :=
  i_lazy_match_goal m.

Ltac2 i_match_goal pats :=
  let rec interp ps := match ps with
  | [] => Control.zero Match_failure
  | ph :: pt =>
    let next _ := interp pt in
    let (pat, f) := ph in
    let (phyps, pconcl) := pat in
    let cur _ :=
        let (hids, hctx, subst, cctx) := i_matches_patterns_goal phyps pconcl in
        f hids hctx subst cctx
    in Control.plus cur next
  end in
  interp pats.

Ltac2 i_match_one_goal pats := Control.once (fun _ => i_match_goal pats).

Ltac2 Notation "iMatch!" "goal" "with" m(goal_matching) "end" :=
  i_match_one_goal m.

Ltac2 Notation "iMultiMatch!" "goal" "with" m(goal_matching) "end" :=
  i_match_goal m.

Notation "'<' c '>' P" := (c%bool, P%I) (at level 10, c at level 0, only parsing).
Notation "'<?>' P" := (not_false, P%I) (at level 10, only parsing).
Notation "‖" := sep (only parsing).

From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import base intro_patterns spec_patterns
     sel_patterns coq_tactics reduction.
From iris.proofmode Require Import classes notation.

From iris.proofmode Require Import tactics.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Pattern Option.

From Local Require utils.
Import utils.Iriception utils.Misc utils.Array utils.Iriception.

Ltac2 Type kinded_pattern := (Pattern.match_kind * Pattern.t).
Ltac2 Type kinded_patterns := kinded_pattern list.

Ltac2 Type exn ::= [IMatch_failure].

Ltac2 i_match_term (kpat : kinded_pattern) (term : constr) :=
  let (k, pat) := kpat in
  match k with
  | Pattern.MatchPattern =>
    orelse (fun () =>
              let bind := Pattern.matches_vect pat term in
              (bind, None))
           (fun e =>
              Control.zero (match e with
                            | Match_failure => IMatch_failure
                            | _ => e
                            end))
  | Pattern.MatchContext =>
    orelse (fun _ =>
              let (context, bind) := Pattern.matches_subterm_vect pat term in
              (bind, Some context))
           (fun e =>
              Control.zero (match e with
                            | Match_failure => IMatch_failure
                            | _ => e
                            end))
  end.

(* given a term, goes through patterns and tries to match one against it *)
Ltac2 rec i_match_pattern
      (pats : (bool * Pattern.match_kind * Pattern.t) array)
      (acc :  (constr * (constr array) * (Pattern.context option)) array)
      (identifer : constr)
      (term : constr)
      (n : int) (all_matched : bool) :=
  match Int.equal (Array.length pats) n with
  | true =>
    all_matched
  | false =>
    let (p_matched, k, p) := Array.get pats n in
    match p_matched with
    | true =>
      i_match_pattern pats acc identifer term (Int.add 1 n) all_matched
    | false =>
      orelse (fun () =>
                let (binders, ctx) := i_match_term (k, p) term in
                let () := Array.set pats n (true, k, p) in
                let () := Array.set acc n (identifer, binders, ctx) in
                false
             )
             (fun e => match e with
                    | IMatch_failure =>
                      (i_match_pattern pats acc identifer term (Int.add 1 n) false)
                    | _ => Control.zero e
                    end)
    end
  end.

Ltac2 i_match_ihyps
      (phyps : kinded_patterns)
      (penv : constr)
      (senv : constr)
  := (* i_match_pattern will toggle 'false' when the pattern is matched *)
    let pats := of_list (List.map (fun x => let (k,p) := x in (false, k, p)) phyps)
                       (false, Pattern.MatchPattern, pattern:(_)) in

    (* identifer of the hypothesis, matched vars and context*)
    let placeholder := ('(1), Array.make 0 '(1), None) in

    (* accumulating binders and contexts from matches *)
    let acc := Array.make (List.length phyps) placeholder in

    (* go through env and match on propositions *)
    let rec recurse_env (env : constr) :=
      lazy_match! env with
      | Esnoc ?gamma ?id ?prop =>
        let all_matched := i_match_pattern pats acc id prop 0 true in
        match all_matched with
        | true => true
        | false => recurse_env gamma
        end
      | Enil =>
        let rec check_all n :=
            match (Int.equal (Array.length pats)) n with
            | true => true
            | false =>
              let (b,_,_) := Array.get pats n in
              Bool.and b (check_all (Int.add 1 n))
            end in
        check_all 0
      | _ => iriception "The environment isn't of the right shape"
      end in

    (* actual code *)
    (* lookup in persistent environment first, then spatial *)
    let accl :=
      let p_all_matched := recurse_env penv in
      match p_all_matched with
      | true => to_list acc
      | false =>
        let s_all_matched := recurse_env senv in
        match s_all_matched with
        | true => to_list acc
        | false => Control.zero Match_failure
        end
      end in
    (* convert acc to the right type *)
    let (ids, binders, contexts) :=
        List.fold_right (fun ne ac =>
                           let (i,b,c) := ne in
                           let (iac,bac,cac) := ac in
                           let bl := to_list b in
                           let cl := Option.map_default (fun x => [x]) [] c in
                           (i::iac, List.append bl bac, List.append cl cac)
                        )
                        ([],[],[]) accl in
    (of_list ids '(1),
     of_list binders '(1),
     of_list contexts (Pattern.empty_context())).


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
  | [|- @envs_entails ?pr1 (@Envs ?pr2 ?p ?s ?c) ?q] =>
    let (hids, hsubst, hctx) := i_match_ihyps phyps p s in
    let (gsubst, gctx) := i_match_igoal pconcl q in
    let hsubstl := to_list hsubst in
    let gsubstl := to_list gsubst in
    (hids, hctx, of_list (List.append hsubstl gsubstl) '(1), gctx)
  | [|- _] => Control.zero (Tactic_failure (Some (os "The goal isn't of the right shape")))
  end.

Ltac2 i_match_goal pats :=
  let rec interp m := match m with
  | [] => Control.zero Match_failure
  | p :: m =>
    let next _ := interp m in
    let (pat, f) := p in
    let (phyps, pconcl) := pat in
    let cur _ :=
        let (hids, hctx, subst, cctx) := i_matches_goal phyps pconcl in
        f hids hctx subst cctx
    in Control.plus cur next
  end in
  match Control.case (fun _ => interp pats) with
  | Err e => Control.zero e
  | Val ans =>
    let (x,k) := ans in x
  end.

Ltac2 Notation "iMatch!" "goal" "with" m(goal_matching) "end" :=
  i_match_goal m.

From iris.proofmode Require Import classes notation.
From Local Require Import ltac2_tactics.

Context {PROP : sbi}.
Implicit Types P Q R : PROP.

Set Ltac2 Backtrace.

Lemma test_iAssumption_coq_1 P Q : Q ⊢ <affine> P -∗ Q.
Proof.
  i_start_proof ().
  i_intro_constr '(INamed "q").
  i_intro_constr '(INamed "p").
  iMatch! goal with
  | [h1: Q , h2 : _ |- ?p] => Message.print (oc h1)
  end.
  i_assumption ().
Qed.

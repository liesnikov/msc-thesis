From Ltac2 Require Import Ltac2.
From Local Require Import ltac2_tactics.
From iris.proofmode Require base.

Ltac2 rec max_destruct (n : constr) :=
  let l := i_fresh_fun () in
  let r := i_fresh_fun () in
  let () := i_and_destruct n l r in
  let ll := Control.plus (fun () => max_destruct l) (fun _ => [l]) in
  let rr := Control.plus (fun () => max_destruct r) (fun _ => [r]) in
  List.append ll rr.

Ltac2 rec max_intro () :=
  repeat (try intros);
  let f := i_fresh_fun () in
  Control.plus (fun () => i_intro_n (fun () => f);
                        let ff := orelse (fun () => max_destruct f) (fun e => [f]) in
                        let rr := max_intro () in
                        List.append ff rr)
               (fun e => f :: []).

Ltac2 rec try_all2 (s : 'a list) (action : 'a list -> 'a list -> unit) :=
  match s with
  | [] => action [] []
  | h :: t => orelse
              (fun () => try_all2 t (fun l m => action (h :: l) m))
              (fun _ => try_all2 t (fun l m => action l (h :: m)))
  end.

Ltac2 rec try_all3
      (s : 'a list)
      (action : 'a list -> 'a list -> 'a list -> unit):=
  match s with
  | [] => action [] [] []
  | h :: t => orelse
              (fun () => try_all3 t (fun l m n => action (h :: l) m n))
              (fun _ =>
                 orelse
                   (fun () => try_all3 t (fun l m n => action l (h :: m) n))
                   (fun _ => try_all3 t (fun l m n => action l m (h :: n))))
  end.

Ltac2 rec constr_list_2_list_constr (s : constr list) :=
  List.fold_left (fun t x => constr:(cons $x $t)) s constr:(@nil base.ident.ident).

Ltac2 rec tauto_solver_go (s : constr list) :=
  let names := max_intro () in
  first [ i_assumption ()
        | i_split (); Control.enter (fun () => tauto_solver_go (List.append s names))
        | try_all2 (List.append s names)
                    (fun l m =>
                       let ll := constr_list_2_list_constr l in
                       i_split_l_pure ll > [tauto_solver_go l| tauto_solver_go m])
        | let asn := List.append s names in
          let asnl := List.length asn in
          try_all3 asn
                   (fun l r n =>
                      match (Int.equal (List.length n) asnl) with
                      | true => fail0 ()
                      | false => ()
                      end;
                      let ln :=
                          List.map (fun ll =>
                                      let lln := i_fresh_fun () in
                                      i_and_destruct_choice ll '(base.Left) lln;
                                      lln) l in
                      let rn :=
                          List.map (fun rr =>
                                      let rrn := i_fresh_fun () in
                                      i_and_destruct_choice rr '(base.Right) rrn;
                                      rrn) r in
                      tauto_solver_go (List.append ln (List.append rn n)))
        ].

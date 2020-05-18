From Ltac2 Require Import Ltac2.
From Local Require Import ltac2_tactics.

Ltac2 rec max_intro () :=
  let ff := i_fresh_fun () in
  Control.plus (fun () => i_intro_n ff;
                        let rr := max_intro () in
                        ff :: rr)
               (fun e => ff :: []).

Ltac2 rec ltac2_list_2_constr_list (s : constr list) :=
  List.fold_left (fun t x => constr:(cons $x $t)) s constr:(nil).

Ltac2 rec try_all (s : 'a list) (action : 'a list -> 'a list -> unit) () :=
  match s with
  | [] => action [] []
  | h :: t => orelse
              (try_all t (fun l m => action (h :: l) m))
              (fun e => try_all t (fun l m => action l (h :: m)) ())
  end.

Ltac2 rec tauto_solver_go (s : constr list) :=
  let names := max_intro () in
  orelse (i_assumption)
         (fun e =>
            try_all (List.append s names)
                    (fun l m =>
                       let ll := ltac2_list_2_constr_list l in
                       i_split_l ll > [tauto_solver_go l| tauto_solver_go m])
                    ()
         ).

From Ltac2 Require Import Ltac2.

From Ltac2 Require Constr Bool List.
From iris_string_ident Require ltac2_string_ident.

Module Misc.
  Ltac2 Type exn ::= [ ListExn ((message option) * (exn list)) ].
  Ltac2 or0 msg t1 t2 := Control.plus (t1) (fun e1 => Control.plus (t2) (fun e2 => Control.zero (ListExn (msg, [e1 ; e2])))).
  Ltac2 or t1 t2 := or0 None t1 t2.
  Ltac2 or_msg m t1 t2 := or0 (Some m) t1 t2.

  Ltac2 Notation x(self) "++" y(self) := Message.concat x y.
  Ltac2 os (x:string) := Message.of_string x.
  Ltac2 oc (x:constr) := Message.of_constr x.
  Ltac2 oe (x:exn) := Message.of_exn x.
  Ltac2 cc := Message.concat.

  Ltac2 current_hyps_names () :=
    List.map (fun x => let (i, _, _) := x in i) (Control.hyps ()).

  Ltac2 fresh_ident0 (s : ident) :=
   Fresh.fresh (Fresh.Free.of_ids (current_hyps_names ())) s.

  Ltac2 fresh () :=
    fresh_ident0 ident:(H).

  Ltac2 ident_of_string s :=
    match Ident.of_string s with
    | None => Control.zero (No_value)
    | Some t => t
    end.
End Misc.

Module Iriception.
  Import Misc.
  Ltac2 Type exn ::= [ Iriception(message) ].
  Ltac2 iriception t := Control.zero (Iriception (Message.of_string t)).

  Ltac2 failwith t s :=
    orelse t (fun e => Control.zero
                      (Iriception (cc
                                  (cc (os s)
                                      (os ": "))
                                  (oe e)))).
End Iriception.


Module Array.
  Ltac2 to_list arr :=
    let rec go n :=
        match Int.equal (Array.length arr) n with
        | true => []
        | false => let h := Array.get arr n in
                  let t := go (Int.add 1 n) in
                  h :: t
        end in
    go 0.

  Ltac2 of_list all el :=
    let rec go (ar : 'a array) (al : 'a list) (n : int) :=
      match al with
      | [] => ar
      | h :: t => let _ := Array.set ar n h in
                 go ar t (Int.add n 1)
      end in
    match all with
    | [] => Array.make 0 el
    | h :: t => let arr := Array.make (List.length all) h in
               go arr all 0
    end.

  Ltac2 append arr brr e :=
    let al := to_list arr in
    let bl := to_list brr in
    of_list (List.append al bl).

  Ltac2 copy_into_starting (arr : 'a array) (brr : 'a array) (s : int) :=
    let rec go n :=
      match Int.equal (Array.length arr) n with
      | true => ()
      | false => let el := Array.get arr n in
                let _ := Array.set brr (Int.add s n) in
                go (Int.add 1 n)
      end in
    go 0.
End Array.


Module Evars.
  Import Constr.

  Ltac2 rec remove_all_casts t :=
    match (Unsafe.kind t) with
    | Unsafe.Cast t _ _ => remove_all_casts t
    | _ => t
    end.

  Ltac2 new_evar_with_cast type := '(_ : $type).

  Ltac2 new_evar type := remove_all_casts (new_evar_with_cast type).

  Ltac2 evar0 (name : ident) (type : constr) :=
    let p := new_evar type in
    pose ($name := $p).

  Ltac2 unify0 (term1 : constr) (term2 : constr) :=
    let p1 := '(eq_refl $term1 : $term1 = $term2) in
    ().

  Ltac2 instantiate0 (n : ident) term :=
    unify0 term (Unsafe.make (Unsafe.Var n)).

  Ltac2 is_evar (term : constr) :=
    match (Unsafe.kind (remove_all_casts term)) with
    | Unsafe.Evar _ _ => true
    | _ => false
    end.

  Import Ltac2.Bool.

  Ltac2 rec has_evar (term : constr) :=
    match (Unsafe.kind term) with
    | Unsafe.Evar _ _ => true
    | Unsafe.Cast t1 _ t2 => and (has_evar t1) (has_evar t2)
    | Unsafe.Prod _ ty te => and (has_evar ty) (has_evar te)
    | Unsafe.Lambda _ ty te => and (has_evar ty) (has_evar te)
    | Unsafe.LetIn _ t1 t2 t3 =>
      and (has_evar t1) (and (has_evar t2) (has_evar t3))
    | Unsafe.Case _ t m ct =>
      let incases := List.for_all (has_evar) (Array.to_list ct) in
      and (has_evar m) incases
    | Unsafe.Fix _ _ _ ty te =>
      let intypes := (List.for_all (has_evar) (Array.to_list ty)) in
      let interms := (List.for_all (has_evar) (Array.to_list te)) in
      and intypes interms
    | Unsafe.CoFix _ _ ty te =>
      let intypes := (List.for_all (has_evar) (Array.to_list ty)) in
      let interms := (List.for_all (has_evar) (Array.to_list te)) in
      and intypes interms
    | Unsafe.Proj _ t => has_evar t
    | _ => false
    end.
End Evars.


Module String.
  Import ltac2_string_ident.

  Ltac2 coq_string_to_ident := StringToIdent.coq_string_to_ident.
  Ltac2 ident_to_coq_string := ().
End String.

Ltac2 Notation "fresh_ident" n(ident):=
  Misc.fresh_ident0 n.

Ltac2 Notation "evar" "(" n(ident) ":" type(constr) ")" :=
  Evars.evar0 n type.

Ltac2 Notation "instantiate" "(" n(ident) ":=" t(constr) ")" :=
  Evars.instantiate0 n t.

Ltac2 Notation "unify" t1(constr) t2(constr) :=
  Evars.unify0 t1 t2.

Ltac2 Notation t1(self) ";;" t2(thunk(self)) := t1 ; Control.enter (t2).

(* Test *)
Goal nat.
Proof.
  evar (p : bool).
  instantiate (p := true).
  let p1 := Evars.new_evar '(nat) in
  let p2 := Evars.new_evar '(nat) in
  epose (q := $p1 + $p2);
  unify (1+2) &q.
  exact q.
Qed.

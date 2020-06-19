From Ltac2 Require Import Ltac2.

From Ltac2 Require Constr Bool List.

Module Misc.
  Ltac2 Type exn ::= [ ListExn ((message option) * (exn list)) ].
  Ltac2 or t1 t2 := Control.plus (t1) (fun e1 => Control.plus (t2) (fun e2 => Control.zero (ListExn (None, [e1 ; e2])))).

  Ltac2 Notation x(self) "++" y(self) := Message.concat x y.
  Ltac2 os (x:string) := Message.of_string x.
  Ltac2 oc (x:constr) := Message.of_constr x.
  Ltac2 oe (x:exn) := Message.of_exn x.
  Ltac2 cc := Message.concat.

  Ltac2 current_hyps_names () :=
    List.map (fun x => let (i, _, _) := x in i) (Control.hyps ()).
  Ltac2 fresh () :=
    Fresh.fresh (Fresh.Free.of_ids (current_hyps_names ())) ident:(H).

  Ltac2 ident_of_string s :=
    match Ident.of_string s with
    | None => Control.zero (Tactic_failure None)
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
  Ltac2 rec to_list (a : 'a array) :=
    match (Int.equal (Array.length a) 0) with
    | true => []
    | _ => let el := Array.get a 0 in
          el :: to_list a
    end.

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

  Ltac2 evar (name : ident) (type : constr) :=
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

  Import Bool.
  Ltac2 rec has_evar (term : constr) :=
    match (Unsafe.kind term) with
    | Unsafe.Evar _ _ => true
    | Unsafe.Cast t1 _ t2 => and (has_evar t1) (has_evar t2)
    | Unsafe.Prod _ t1 t2 => and (has_evar t1) (has_evar t2)
    | Unsafe.Lambda _ t1 t2 => and (has_evar t1) (has_evar t2)
    | Unsafe.LetIn _ t1 t2 t3 => and (has_evar t1) (and (has_evar t2) (has_evar t3))
    | Unsafe.Case _ t1 t2 at1 => false
    | Unsafe.Fix _ _ _ at2 at2 => false
    | Unsafe.CoFix _ _ at1 at2 => false
    | Unsafe.Proj _ t => has_evar t
    | _ => false
    end.
End Evars.

Ltac2 Notation "evar" "(" n(ident) ":" type(constr) ")" :=
  Evars.evar n type.

Ltac2 Notation "instantiate" "(" n(ident) ":=" t(constr) ")" :=
  Evars.instantiate0 n t.

Ltac2 Notation "unify" t1(constr) t2(constr) :=
  Evars.unify0 t1 t2.

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

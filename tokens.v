From iris.proofmode Require Import base tokens sel_patterns.
From Ltac2 Require Import Ltac2.

Ltac2 Type direction := [Left | Right].

Ltac2 Type sel_pat :=
  [ SelPure
  | SelIntuitionistic
  | SelSpatial
  | SelIdent(ident)
  ].

Ltac2 Type gallina_ident :=
  [ IGallinaNamed(string)
  | IGallinaAnon
  ].

Ltac2 Type rec intro_pat :=
  [ IIdent(ident)
  | IList(intro_pat, intro_pat)
  | IFresh ].
(*
  | IDrop
  | IFrame

  | IPure(gallina_ident)
  | IIntuitionistic(intro_pat)
  | ISpatial(intro_pat)
  | IModalElim(intro_pat)
  | IRewrite(direction)
  | IPureIntro(intro_pat)
  | IModalIntro(intro_pat)
  | ISimpl(intro_pat)
  | IDone(intro_pat)
  | IForall(intro_pat)
  | IAll(intro_pat)
  | IClear(sel_pat)
  | IClearFrame(sel_pat)
]. *)

Ltac2 rec tactac (x : intro_pat) :=
  match x with
  | IList x1 x2 => tactac x1; tactac x2
  | IIdent _ =>  Message.print (Message.of_string "hi1")
  | IFresh => Message.print (Message.of_string "hi2")
  end.


Lemma foo:
  True.
Proof.
  tactac (IList (IFresh) (IFresh)).

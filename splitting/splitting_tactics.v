From iris.bi Require Import bi telescopes.
Import bi.
From iris.proofmode Require Import base classes modality_instances.

From Local Require Import named_prop.
From Local Require Import connection.

From Ltac2 Require Ltac2.
From Local Require utils.

Section bi.
Context {PROP : bi}.
Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.

Lemma tac_forall_intro {A} Δ (Φ : A → PROP) Q :
  FromForall Q Φ →
  (∀ a, envs_entails Δ (Φ a)) →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq /FromForall=> <-.
  apply forall_intro.
Qed.


Lemma tac_impl_intro Δ i P P' Q R :
  FromImpl R P Q →
  (if env_spatial_is_nil Δ then TCTrue else Persistent P) →
  FromAffinely P' P →
  match envs_app false (Esnoc Enil (true, i) P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Proof.
  destruct (envs_app _ _ _) eqn:?; last done.
  rewrite /FromImpl envs_entails_eq => <- ???. destruct (env_spatial_is_nil Δ) eqn:?.
  - rewrite (env_spatial_is_nil_intuitionistically Δ) //; simpl. apply impl_intro_l.
    rewrite envs_app_singleton_sound //; simpl.
    rewrite -(from_affinely P' P) -affinely_and_lr.
    by rewrite persistently_and_intuitionistically_sep_r intuitionistically_elim wand_elim_r.
  - apply impl_intro_l. rewrite envs_app_singleton_sound //; simpl.
    by rewrite -(from_affinely P' P) persistent_and_affinely_sep_l_1 wand_elim_r.
Qed.

Lemma tac_impl_intro_intuitionistic Δ i P P' Q R :
  FromImpl R P Q →
  IntoPersistent false P P' →
  match envs_app true (Esnoc Enil (true,i) P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Proof.
  destruct (envs_app _ _ _) eqn:?; last done.
  rewrite /FromImpl envs_entails_eq => <- ??.
  rewrite envs_app_singleton_sound //=. apply impl_intro_l.
  rewrite (_ : P = <pers>?false P)%I // (into_persistent false P).
  by rewrite persistently_and_intuitionistically_sep_l wand_elim_r.
Qed.
Lemma tac_impl_intro_drop Δ P Q R :
  FromImpl R P Q → envs_entails Δ Q → envs_entails Δ R.
Proof.
  rewrite /FromImpl envs_entails_eq => <- ?. apply impl_intro_l. by rewrite and_elim_r.
Qed.

Lemma tac_wand_intro Δ i P Q R :
  FromWand R P Q →
  match envs_app false (Esnoc Enil (true,i) P) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Proof.
  destruct (envs_app _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite /FromWand envs_entails_eq => <- HQ.
  rewrite envs_app_sound //; simpl. by rewrite right_id HQ.
Qed.


Lemma tac_wand_intro_intuitionistic Δ i P P' Q R :
  FromWand R P Q →
  IntoPersistent false P P' →
  TCOr (Affine P) (Absorbing Q) →
  match envs_app true (Esnoc Enil (true,i) P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Proof.
  destruct (envs_app _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite /FromWand envs_entails_eq => <- ? HPQ HQ.
  rewrite envs_app_singleton_sound //=. apply wand_intro_l. destruct HPQ.
  - rewrite -(affine_affinely P) (_ : P = <pers>?false P)%I //
            (into_persistent _ P) wand_elim_r //.
  - rewrite (_ : P = <pers>?false P)%I // (into_persistent _ P).
    by rewrite -{1}absorbingly_intuitionistically_into_persistently
      absorbingly_sep_l wand_elim_r HQ.
Qed.

Lemma tac_assumption Δ i p P Q :
  envs_lookup_true i Δ = Some (p,P) →
  FromAssumption p P Q →
  (let Δ' := envs_delete true i p Δ in
   if env_spatial_is_nil Δ' then TCTrue
   else Absorbing Q
        (* For now not dealing with the case when the whole env can be affine *)
        (* TCOr (Absorbing Q) (AffineEnv (env_spatial Δ')) *)) →
  envs_entails Δ Q.
Proof.
  intros ?? H. rewrite envs_entails_eq envs_lookup_sound //.
  simpl in *. destruct (env_spatial_is_nil _) eqn:?.
  - by rewrite (env_spatial_is_nil_intuitionistically _) // sep_elim_l.
  - rewrite from_assumption. by rewrite sep_elim_l.
Qed.

Lemma tac_sep_split Δ bs P Q1 Q2 :
  FromSep P Q1 Q2 →
  match envs_split bs Δ with
  | None => False
  | Some (Δ1,Δ2) => envs_entails Δ1 Q1 ∧ envs_entails Δ2 Q2
  end → envs_entails Δ P.
Proof.
  destruct (envs_split _ _) as [(Δ1&Δ2)|] eqn:?; last done.
  rewrite envs_entails_eq=>? [HQ1 HQ2].
  rewrite envs_split_sound //. by rewrite HQ1 HQ2.
Qed.
End bi.


Import Ltac2.
Import utils.Misc utils.Iriception utils.Evars.

From Local Require ltac2_tactics.

Ltac2 i_start_split_proof () :=
  match! goal with
  | [|- @envs_entails _ _ _] => refine '(@from_named _ _ _) > [ () | () | cbn]
  | [|- _] => ()
  end.


Ltac2 pm_reduce () :=
  cbv [named_prop.env_spatial named_prop.env_intuitionistic named_prop.env_counter
       named_prop.env_spatial_is_nil named_prop.env_Forall
       named_prop.envs_app named_prop.envs_delete named_prop.envs_lookup_true
       named_prop.envs_split
       named_prop.env_app named_prop.env_delete named_prop.env_lookup_true
       named_prop.env_lookup  named_prop.get_ident
       connection.translate_envs connection.translate_env];
  ltac2_tactics.pm_reduce (); cbn.

Ltac2 pm_reflexivity () :=
  pm_reduce (); exact eq_refl.

Ltac2 i_intro_constr (x:constr) :=
  (failwith (i_start_split_proof) "couldn't start splitting proof in intro_constr");
  (or
    (fun () => refine '(@tac_impl_intro _ _ $x _ _ _ _ _ _ _ _) >
     [() | () | ()
     | ltac2_tactics.i_solve_tc ()
     | pm_reduce (); ltac2_tactics.i_solve_tc ()
     | ltac2_tactics.i_solve_tc ()
     | pm_reduce ();
       lazy_match! goal with
       | [|- False] => Control.zero (Iriception (os "i_intro " ++ oc x ++ os " not fresh"))
       | [|- _] => ()
       end])
    (fun () => refine '(@tac_wand_intro _ _ $x _ _ _ _ _) >
     [ () | ()
     | ltac2_tactics.i_solve_tc ()
     | pm_reduce ()])).


Print Ltac2 unify0.
Ltac2 rec unify_constr_true (e : constr) :=
  lazy_match! e with
  | andb ?b1 ?b2 => (unify0 b1 '(true)); unify_constr_true b2
  | ?e => unify0 e '(true)
end.

Ltac2 rec unify_constr_false (e : constr) :=
  lazy_match! e with
  | andb ?b1 ?b2 => (unify0 b1 '(false))
  | ?e => unify0 e '(false)
end.

Goal True.
Proof.
  let v1 := new_evar_with_cast '(bool) in
  let v2 := new_evar_with_cast '(bool) in
  assert ($v1 && ($v2 && true) = true).
  lazy_match! goal with
  | [|- ?e = true] => unify_constr_true e
  end.
  reflexivity.
  let v1 := new_evar_with_cast '(bool) in
  let v2 := new_evar_with_cast '(bool) in
  assert ($v1 && ($v2 && true) = false).
  lazy_match! goal with
  | [|- ?e = false] => unify_constr_false e
  end.
  reflexivity.
  constructor.
  Unshelve. exact false.
Qed.

Ltac2 i_exact_spatial h :=
  let rec list_from_env e :=
      match! e with
      | Esnoc ?gg (?b,?j) ?pp =>
        match (Constr.equal h j) with
        | true => unify_constr_true b; list_from_env gg
        | false => b :: list_from_env gg
        end
      | Enil => []
      end in
  lazy_match! goal with
  | [|- @envs_entails _ (@Envs _ ?gp ?gs _) ?q] =>
    let list_of_constr := list_from_env gs in
    List.iter (fun b => unify_constr_false b) list_of_constr
  end;
  refine '(tac_assumption _ $h _ _ _ _ _ _) >
  [() | () | pm_reflexivity ()
  | ltac2_tactics.i_solve_tc ()
  | pm_reduce (); ltac2_tactics.i_solve_tc ()].


Ltac2 rec env_length (x : constr) :=
  match! x with
  | Enil => 0
  | Esnoc ?x _ _ => Int.add 1 (env_length x)
  end.

Ltac2 i_split () :=
  let n :=
    lazy_match! goal with
    | [|- @envs_entails _ (@Envs _ ?gp ?gs _) ?q] => env_length gs
    end in
  let rec gen_list n :=
    match (Int.equal 0 n) with
    | true => '(nil)
    | false =>
      let v := new_evar_with_cast '(bool) in
      let tl := gen_list (Int.sub n 1) in
      '($v :: $tl)
    end in
  let bs := gen_list n in
  match! goal with
  | [|- @envs_entails _ ?g ?q] =>
    refine '(tac_sep_split $g $bs _ _ _ _ _) >
    [ () | ()
    | ltac2_tactics.i_solve_tc ()
    | pm_reduce ();
      lazy_match! goal with
      | [ |- False] => iriception "couldn't split the context"
      | [ |- _] => split > [() | ()]
      end]
  | [|- _] => iriception "the goal isn't bi entailment"
  end.

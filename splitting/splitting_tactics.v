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

Lemma tac_eval Δ Q Q' :
  (∀ (Q'':=Q'), Q'' ⊢ Q) → (* We introduce [Q''] as a let binding so that
    tactics like `reflexivity` as called by [rewrite //] do not eagerly unify
    it with [Q]. See [test_iEval] in [tests/proofmode]. *)
  envs_entails Δ Q' → envs_entails Δ Q.
Proof. intro H. by rewrite envs_entails_eq -H. Qed.

Lemma tac_eval_in Δ i p c P P' Q :
  envs_lookup_with_constr i Δ = Some (p, c, P) →
  (∀ (P'':=P'), P ⊢ P') →
  match envs_simple_replace i p (Esnoc Enil (c,i) P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_eq /=. intros ? HP ?.
  rewrite envs_simple_replace_singleton_sound_with_constr //; simpl.
  destruct c; by rewrite ?HP wand_elim_r.
Qed.

Class AffineEnv (Γ : env PROP) := affine_env : Forall Affine Γ.
Global Instance affine_env_nil : AffineEnv Enil.
Proof. constructor. Qed.
Global Instance affine_env_snoc Γ i P :
  Affine P → AffineEnv Γ → AffineEnv (Esnoc Γ i P).
Proof. destruct i as [[] i]; rewrite /AffineEnv;
       cbn [env_to_list]; by try (constructor).
Qed.

(* If the BI is affine, no need to walk on the whole environment. *)
Global Instance affine_env_bi `(BiAffine PROP) Γ : AffineEnv Γ | 0.
Proof. induction Γ; apply _. Qed.

Instance affine_env_spatial Δ :
  AffineEnv (env_spatial Δ) → Affine ([∗] env_spatial Δ).
Proof. intros H. induction H; simpl; apply _. Qed.

Lemma tac_emp_intro Δ : AffineEnv (env_spatial Δ) → envs_entails Δ emp.
Proof. intros. by rewrite envs_entails_eq (affine (of_envs Δ)). Qed.

Lemma tac_assumption Δ i p P Q :
  envs_lookup_true i Δ = Some (p,P) →
  FromAssumption p P Q →
  (let Δ' := envs_delete true i p Δ in
   if env_spatial_is_nil Δ' then TCTrue
   else TCOr (Absorbing Q) (AffineEnv (env_spatial Δ'))) →
  envs_entails Δ Q.
Proof.
  intros ?? H. rewrite envs_entails_eq envs_lookup_sound //.
  simpl in *. destruct (env_spatial_is_nil _) eqn:?.
  - by rewrite (env_spatial_is_nil_intuitionistically _) // sep_elim_l.
  - rewrite from_assumption. destruct H; by rewrite sep_elim_l.
Qed.

Lemma tac_assumption_coq Δ P Q :
  (⊢ P) →
  FromAssumption true P Q →
  (if env_spatial_is_nil Δ then TCTrue
   else TCOr (Absorbing Q) (AffineEnv (env_spatial Δ))) →
  envs_entails Δ Q.
Proof.
  rewrite /FromAssumption /bi_emp_valid /= => HP HPQ H.
  rewrite envs_entails_eq -(left_id emp%I bi_sep (of_envs Δ)).
  rewrite -bi.intuitionistically_emp HP HPQ.
  destruct (env_spatial_is_nil _) eqn:?.
  - by rewrite (env_spatial_is_nil_intuitionistically _) // sep_elim_l.
  - destruct H; by rewrite sep_elim_l.
Qed.

Lemma tac_rename Δ i j p c P Q :
  envs_lookup_with_constr i Δ = Some (p, c, P) →
  match envs_simple_replace i p (Esnoc Enil (c,j) P) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_eq=> ??. rewrite envs_simple_replace_singleton_sound_with_constr //.
  by rewrite wand_elim_r.
Qed.

Lemma tac_clear Δ i p c P Q :
  envs_lookup_with_constr i Δ = Some (p,c,P) →
  (if p then TCTrue else TCOr (TCOr (Affine P) (Absorbing Q))
                              (if c then (TCOr (Affine P) (Absorbing Q))
                                    else TCTrue)) →
  envs_entails (envs_delete true i p Δ) Q →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=> ? HT HQ. rewrite envs_lookup_sound_with_constr //. rewrite HQ. destruct p, c, HT; cbn in *; by rewrite /= ?sep_elim_r.
Qed.

(** * False *)
Lemma tac_ex_falso Δ Q : envs_entails Δ False → envs_entails Δ Q.
Proof. by rewrite envs_entails_eq -(False_elim Q). Qed.

Lemma tac_false_destruct Δ i p P Q :
  envs_lookup_true i Δ = Some (p,P) →
  P = False%I →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ??. subst. rewrite envs_lookup_sound //; simpl.
  by rewrite intuitionistically_if_elim sep_elim_l False_elim.
Qed.

(** * Pure *)
Lemma tac_pure_intro Δ Q φ a :
  FromPure a Q φ →
  (if a then AffineEnv (env_spatial Δ) else TCTrue) →
  φ →
  envs_entails Δ Q.
Proof.
  intros ???. rewrite envs_entails_eq -(from_pure a Q). destruct a; simpl.
  - by rewrite (affine (of_envs Δ)) pure_True // affinely_True_emp affinely_emp.
  - by apply pure_intro.
Qed.

Lemma tac_pure Δ i p P φ Q :
  envs_lookup_true i Δ = Some (p, P) →
  IntoPure P φ →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  (φ → envs_entails (envs_delete true i p Δ) Q) → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=> ?? HPQ HQ.
  rewrite envs_lookup_sound //; simpl. destruct p; simpl.
  - rewrite (into_pure P) -persistently_and_intuitionistically_sep_l persistently_pure.
    by apply pure_elim_l.
  - destruct HPQ.
    + rewrite -(affine_affinely P) (into_pure P) -persistent_and_affinely_sep_l.
      by apply pure_elim_l.
    + rewrite (into_pure P) -(persistent_absorbingly_affinely ⌜ _ ⌝%I) absorbingly_sep_lr.
      rewrite -persistent_and_affinely_sep_l. apply pure_elim_l=> ?. by rewrite HQ.
Qed.

Lemma tac_pure_revert Δ φ Q : envs_entails Δ (⌜φ⌝ → Q) → (φ → envs_entails Δ Q).
Proof. rewrite envs_entails_eq. intros HΔ ?. by rewrite HΔ pure_True // left_id. Qed.


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
  - rewrite (env_spatial_is_nil_intuitionistically Δ) //; apply impl_intro_l.
    rewrite envs_app_singleton_sound //;
    rewrite -(from_affinely P' P) -affinely_and_lr.
    by rewrite persistently_and_intuitionistically_sep_r intuitionistically_elim wand_elim_r.
  - apply impl_intro_l. rewrite envs_app_singleton_sound //;
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
  rewrite envs_app_sound //; simpl; by rewrite right_id HQ.
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

Lemma tac_and_destruct_split Δ i p j1 j2 c c' P P1 P2 Q :
  envs_lookup_with_constr i Δ = Some (p, c, P) →
  (IntoAnd p P P1 P2) →
  match envs_simple_replace i p (Esnoc (Esnoc Enil (negb c' && c, j2) P2)
                                       (c' && c, j1) P1) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end → envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_eq => H HP HQ.
  apply pure_elim with (envs_wf Δ).
  { rewrite of_envs_eq. apply and_elim_l. }
  move => wf. move: H HP HQ.
  destruct c.
  - rewrite envs_lookup_with_constr_envs_lookup_true; [move {wf} => H HP HQ| done].
    rewrite envs_simple_replace_sound //. destruct p.
    { rewrite (into_and _ P) HQ. destruct c'; cbn.
      + by rewrite and_elim_l and_True wand_elim_r.
      + by rewrite and_elim_r and_True wand_elim_r. }
    { rewrite (into_and _ P) HQ. destruct c'; cbn.
      + by rewrite and_elim_l sep_emp wand_elim_r.
      + by rewrite and_elim_r sep_emp wand_elim_r. }
  - destruct c'; move => H HP HQ; destruct p;
    rewrite envs_simple_replace_sound_with_constr //;
    rewrite HQ ?intuitionistically_True_emp wand_elim_r //=.
Qed.

Lemma tac_or_l Δ P Q1 Q2 :
  FromOr P Q1 Q2 → envs_entails Δ Q1 → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq=> ? ->. rewrite -(from_or P). by apply or_intro_l'.
Qed.
Lemma tac_or_r Δ P Q1 Q2 :
  FromOr P Q1 Q2 → envs_entails Δ Q2 → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq=> ? ->. rewrite -(from_or P). by apply or_intro_r'.
Qed.

Lemma tac_or_destruct Δ i p j1 j2 c P P1 P2 Q :
  envs_lookup_with_constr i Δ = Some (p, c, P) → IntoOr P P1 P2 →
  match envs_simple_replace i p (Esnoc Enil (c, j1) P1) Δ,
        envs_simple_replace i p (Esnoc Enil (c, j2) P2) Δ with
  | Some Δ1, Some Δ2 => envs_entails Δ1 Q ∧ envs_entails Δ2 Q
  | _, _ => False
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace i p (Esnoc Enil _ P1)) as [Δ1|] eqn:?; last done.
  destruct (envs_simple_replace i p (Esnoc Enil _ P2)) as [Δ2|] eqn:?; last done.
  rewrite envs_entails_eq. intros ?? (HP1&HP2).
  destruct c.
  - apply pure_elim with (envs_wf Δ).
    { rewrite of_envs_eq. apply and_elim_l. }
    move => wf. move: H. rewrite envs_lookup_with_constr_envs_lookup_true //= => H.
    rewrite envs_lookup_sound //.
    rewrite (into_or P) intuitionistically_if_or sep_or_r; apply or_elim.
    + rewrite (envs_simple_replace_singleton_sound' _ Δ1) //.
      by rewrite wand_elim_r.
    + rewrite (envs_simple_replace_singleton_sound' _ Δ2) //.
      by rewrite wand_elim_r.
  - rewrite (envs_simple_replace_sound_with_constr _ _ _ _ _ _ _ H) //.
    destruct p; rewrite ?intuitionistically_True_emp wand_elim_r //=.
Qed.

Lemma tac_exist {A} Δ P (Φ : A → PROP) :
  FromExist P Φ → (∃ a, envs_entails Δ (Φ a)) → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq => ? [a ?].
  rewrite -(from_exist P). eauto using exist_intro'.
Qed.

Lemma tac_exist_destruct {A} Δ i p j P (Φ : A → PROP) Q :
  envs_lookup_true i Δ = Some (p, P) → IntoExist P Φ →
  (∀ a,
    match envs_simple_replace i p (Esnoc Enil (true, j) (Φ a)) Δ with
    | Some Δ' => envs_entails Δ' Q
    | None => False
    end) →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ?? HΦ. rewrite envs_lookup_sound //.
  rewrite (into_exist P) intuitionistically_if_exist sep_exist_r.
  apply exist_elim=> a; specialize (HΦ a) as Hmatch.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_simple_replace_singleton_sound' //; simpl. by rewrite wand_elim_r.
Qed.

End bi.


Import Ltac2.
Import utils.Misc utils.Iriception utils.Evars.

From Local Require ltac2_tactics.

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

Ltac2 pm_prettify () :=
  ltac2_tactics.pm_prettify ().

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
    (ltac1:(pr1 pr2 p s c q |-
           let c1 := (eval vm_compute in (Pos.succ c)) in
           convert_concl_no_check (@envs_entails pr1 (@Envs pr2 p s c1) q))
           (Ltac1.of_constr pr1) (Ltac1.of_constr pr2) (Ltac1.of_constr p) (Ltac1.of_constr s) (Ltac1.of_constr c) (Ltac1.of_constr q));
     constr:(IAnon $c)
end.


Ltac2 i_solve_tc := ltac2_tactics.i_solve_tc.


Ltac2 i_intro_pat' (x : Std.intro_pattern) :=
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
        | pm_prettify (); intros0 false [x] ]
      end).

Ltac2 Notation "i_intro_pat" p(intropattern) := i_intro_pat' p.

Ltac2 i_intro_constr (x: constr) :=
  failwith (i_start_split_proof) "Couldn't start splitting proof in intro_constr";
  or
    (fun () => refine '(@tac_impl_intro _ _ $x _ _ _ _ _ _ _ _) >
            [() | () | ()
            | i_solve_tc ()
            | pm_reduce (); ltac2_tactics.i_solve_tc ()
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

Ltac2 i_intro_intuitionistic_constr (x : constr) :=
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
        | i_solve_tc () | i_solve_tc ()
        | i_solve_tc () | pm_reduce ()]).


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

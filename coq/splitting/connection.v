From iris.bi Require Export bi.
From iris.proofmode Require Import base.
From iris.proofmode Require environments.
From Local.splitting Require named_prop.

Section named_prop.
  Context {PROP : bi}.
  Variable p : PROP.

  Fixpoint translate_env (Δ : environments.env PROP) : named_prop.env PROP :=
    match Δ with
    | environments.Enil => named_prop.Enil
    | environments.Esnoc Δ j x => named_prop.Esnoc (translate_env Δ) (true, j) x
    end.

  Definition translate_envs (Δ : environments.envs PROP) : named_prop.envs PROP :=
    let (intuit, spat, count) := Δ in
    named_prop.Envs (translate_env intuit) (translate_env spat) count.


  Lemma translate_preserves_lookup (Γ : environments.env PROP) i x:
    environments.env_lookup i Γ = x ->
    named_prop.env_lookup i (translate_env Γ) = x.
  Proof.
    induction Γ; cbn; trivial.
    now destruct (ident_beq i i0).
  Qed.

  Lemma translate_preserves_env_wf (Δ : environments.env PROP) :
      environments.env_wf Δ ->
      named_prop.env_wf (translate_env Δ).
  Proof.
    induction 1; constructor; auto using translate_preserves_lookup.
  Qed.

  Lemma translate_preserves_envs_wf (Δ : environments.envs PROP) :
      environments.envs_wf Δ ->
      named_prop.envs_wf (translate_envs Δ).
  Proof.
    unfold environments.envs_wf, named_prop.envs_wf.
    destruct Δ; cbn.
    induction 1 as [ei es il].
    constructor; auto using translate_preserves_env_wf.
    intros j. destruct (il j); auto using translate_preserves_lookup.
  Qed.

  Lemma translate_preserves_to_list (Δ : environments.env PROP):
    environments.env_to_list Δ =
    named_prop.env_to_list (translate_env Δ).
  Proof.
    intros.
    induction Δ as [|Δ IH]; cbn.
    - trivial.
    - now rewrite IH.
  Qed.

  Lemma from_named (Δ : environments.envs PROP) Q:
    named_prop.envs_entails (translate_envs Δ) Q ->
    environments.envs_entails Δ Q.
  Proof.
    rewrite named_prop.envs_entails_eq environments.envs_entails_eq.
    intros.
    trans (named_prop.of_envs (translate_envs Δ)); [ | exact H].
    unfold environments.of_envs, environments.of_envs', named_prop.of_envs, named_prop.of_envs'.
    apply bi.and_intro.
    - apply bi.and_elim_l', bi.pure_elim'.
      intros.
      apply bi.pure_intro.
      fold (@named_prop.envs_wf PROP (translate_envs Δ)).
      fold (@environments.envs_wf PROP Δ) in H0.
      auto using translate_preserves_envs_wf.
    - apply bi.and_elim_r'.
      rewrite !translate_preserves_to_list.
      destruct Δ; cbn; auto.
  Qed.
End named_prop.

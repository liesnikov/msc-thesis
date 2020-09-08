From iris.bi Require Export bi.
From iris.bi Require Import tactics.
From iris.proofmode Require Import base.
From iris.algebra Require Export base.
Set Default Proof Using "Type".
Import bi.

Definition ident := positive.
Definition ident_beq := positive_beq.
Definition mrkd_ident : Type := bool * ident.

Inductive env (B : Type) : Type :=
  | Enil : env B
  | Esnoc : env B → mrkd_ident -> B -> env B.
Arguments Enil {_}.
Arguments Esnoc {_} _ _ _.
Instance: Params (@Enil) 1 := {}.
Instance: Params (@Esnoc) 1 := {}.

Fixpoint env_lookup {A} (i : ident) (Γ : env A) : option A :=
  match Γ with
  | Enil => None
  | Esnoc Γ (_,j) x => if ident_beq i j then Some x else env_lookup i Γ
  end.

Module env_notations.
  Notation "y ≫= f" := (pm_option_bind f y).
  Notation "x ← y ; z" := (y ≫= λ x, z).
  Notation "' x1 .. xn ← y ; z" := (y ≫= (λ x1, .. (λ xn, z) .. )).
  Notation "Γ !! j" := (env_lookup j Γ).
End env_notations.
Import env_notations.

Local Open Scope lazy_bool_scope.

Inductive env_wf {A} : env A → Prop :=
  | Enil_wf : env_wf Enil
  | Esnoc_wf Γ i b x : Γ !! i = None → env_wf Γ → env_wf (Esnoc Γ (b,i) x).


Fixpoint env_to_list {A} (E : env A) : list A :=
  match E with
  | Enil => []
  | Esnoc Γ (b,_) x => if b
                      then x :: env_to_list Γ
                      else env_to_list Γ
  end.
Coercion env_to_list : env >-> list.


Record envs (PROP : bi) := Envs {
  env_intuitionistic : env PROP;
  env_spatial : env PROP;
  env_counter : positive (** A counter to generate fresh hypothesis names *)
}.
Add Printing Constructor envs.
Arguments Envs {_} _ _ _.
Arguments env_intuitionistic {_} _.
Arguments env_spatial {_} _.
Arguments env_counter {_} _.

Record envs_wf' {PROP : bi} (Γp Γs : env PROP) := {
  env_intuitionistic_valid : env_wf Γp;
  env_spatial_valid : env_wf Γs;
  envs_disjoint i : Γp !! i = None ∨ Γs !! i = None
}.
Definition envs_wf {PROP : bi} (Δ : envs PROP) :=
  envs_wf' (env_intuitionistic Δ) (env_spatial Δ).

Definition of_envs' {PROP : bi} (Γp Γs : env PROP) : PROP :=
  (⌜envs_wf' Γp Γs⌝ ∧ □ [∧] Γp ∗ [∗] Γs)%I.
Instance: Params (@of_envs') 1 := {}.
Definition of_envs {PROP : bi} (Δ : envs PROP) : PROP :=
  of_envs' (env_intuitionistic Δ) (env_spatial Δ).
Instance: Params (@of_envs) 1 := {}.
Arguments of_envs : simpl never.

Definition envs_entails_aux :
  seal (λ (PROP : bi) (Γp Γs : env PROP) (Q : PROP), of_envs' Γp Γs ⊢ Q).
Proof. by eexists. Qed.
Definition envs_entails {PROP : bi} (Δ : envs PROP) (Q : PROP) : Prop :=
  envs_entails_aux.(unseal) PROP (env_intuitionistic Δ) (env_spatial Δ) Q.
Definition envs_entails_eq :
  @envs_entails = λ PROP (Δ : envs PROP) Q, (of_envs Δ ⊢ Q).
Proof. by rewrite /envs_entails envs_entails_aux.(seal_eq). Qed.
Arguments envs_entails {PROP} Δ Q%I : rename.
Instance: Params (@envs_entails) 1 := {}.

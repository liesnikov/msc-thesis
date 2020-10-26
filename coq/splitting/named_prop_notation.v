From stdpp Require Export strings.
From Local.splitting Require Import named_prop.

Set Default Proof Using "Type".
Delimit Scope proof_scope with env.
Arguments Envs _ _%proof_scope _%proof_scope _.
Arguments Enil {_}.
Arguments Esnoc {_} _%proof_scope _%string _%I.

Notation "" := Enil (only printing) : proof_scope.

Notation "Γ '⟨?⟩' H : P" := (Esnoc Γ (_, INamed H) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ  '⟨?⟩' H  :  '[' P ']' '//'", only printing) : proof_scope.
Notation "Γ '⟨?⟩_' : P" := (Esnoc Γ (_, IAnon _) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ  '⟨?⟩_'  :  '[' P ']' '//'", only printing) : proof_scope.

Notation "Γ H : P" := (Esnoc Γ (true, INamed H) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ  H  :  '[' P ']' '//'", only printing) : proof_scope.
Notation "Γ '_' : P" := (Esnoc Γ (true, IAnon _) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ  '_'  :  '[' P ']' '//'", only printing) : proof_scope.

Notation "Γ" := (Esnoc Γ (false, _) _%I)
  (at level 1, left associativity, format "Γ '//'", only printing) : proof_scope.


Notation "Γ '--------------------------------------' □ Δ '--------------------------------------' ∗ Q" :=
  (envs_entails (Envs Γ Δ _) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Γ '--------------------------------------' □ '//' Δ '--------------------------------------' ∗ '//' Q '//'", only printing) :
  stdpp_scope.
Notation "Δ '--------------------------------------' ∗ Q" :=
  (envs_entails (Envs Enil Δ _) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Δ '--------------------------------------' ∗ '//' Q '//'", only printing) : stdpp_scope.
Notation "Γ '--------------------------------------' □ Q" :=
  (envs_entails (Envs Γ Enil _) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Γ '--------------------------------------' □ '//' Q '//'", only printing)  : stdpp_scope.
Notation "'--------------------------------------' ∗ Q" := (envs_entails (Envs Enil Enil _) Q%I)
  (at level 1, Q at level 200, format "'--------------------------------------' ∗ '//' Q '//'", only printing) : stdpp_scope.

From iris.bi Require Export bi.
From iris.bi Require Import tactics.
From iris.proofmode Require Import base.
From iris.algebra Require Export base.
Set Default Proof Using "Type".
Import bi.

Definition mrkd_ident : Type := bool * ident.

Inductive env (B : Type) : Type :=
  | Enil : env B
  | Esnoc : env B → list (mrkd_ident * B) → env B.

Arguments Enil {_}.
Arguments Esnoc {_} _ _.

Fixpoint list_prod_lookup {A B} (f : A -> bool) (l : list (A * B)) : option B :=
  match l with
  | [] => None
  | h :: t => let (a,b) := h in
            if (f a) then Some b else list_prod_lookup f t
  end.

Definition list_lookup {B} (i : ident) (l : list (mrkd_ident * B)) :=
  list_prod_lookup (fun '(_, j) => ident_beq i j) l.

Fixpoint env_lookup_param {B} (f : mrkd_ident -> bool) (Γ : env B) : option B :=
  match Γ with
  | Enil => None
  | Esnoc Γ l => match list_prod_lookup f l with
                | None => env_lookup_param f Γ
                | Some x => Some x
                end
  end.


Fixpoint env_lookup {B} (i : ident) (Γ : env B) : option B :=
  env_lookup_param (fun '(_,j) => ident_beq i j) Γ.

Module env_notations.
  Notation "y ≫= f" := (pm_option_bind f y).
  Notation "x ← y ; z" := (y ≫= λ x, z).
  Notation "' x1 .. xn ← y ; z" := (y ≫= (λ x1, .. (λ xn, z) .. )).
  Notation "Γ !! j" := (env_lookup j Γ).
  Notation "l !!! j" := (list_lookup j l).
End env_notations.
Import env_notations.

Local Open Scope lazy_bool_scope.

Set Printing All.
Fixpoint env_to_list {A} (E : env A) : list A :=
  match E with
  | Enil => []
  | Esnoc Γ l => (map (fun '(_,_,v) => v)
                 (filter (fun '(b,_,_) => b = true) l)) ++ env_to_list Γ
  end.
Coercion env_to_list : env >-> list.


Inductive env_wf {B} : env B -> Prop :=
  | Enil_wf : env_wf Enil
  | Esnoc_nil_wf Γ : env_wf Γ -> env_wf (Esnoc Γ [])
  | Esnoc_cons_wf Γ l b i x : Γ !! i = None -> l !!! i = None -> env_wf (Esnoc Γ l) -> env_wf (Esnoc Γ [(b, i,x)]).

Fixpoint list_delete {A} (i : ident) (l : list (mrkd_ident * A))
  : (list (mrkd_ident * A)) * bool
  := match l with
    | [] => ([], false)
    | h :: t => let '(b, j, _) := h in
              if b && ident_beq i j
              then (t, true)
              else let (rt, rb) := (list_delete i t) in
                   (h :: rt, rb)
    end.

Fixpoint env_delete {A} (i : ident) (Γ : env A) : env A :=
  match Γ with
  | Enil => Enil
  | Esnoc Γ l =>
    let (r, b) := list_delete i l in
    if b then Esnoc Γ r else Esnoc (env_delete i Γ) l
  end.



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

Definition envs_lookup {PROP} (i : ident) (Δ : envs PROP) : option (bool * PROP) :=
  let (Γp,Γs,n) := Δ in
  match env_lookup i Γp with
  | Some P => Some (true, P)
  | None => P ← env_lookup i Γs; Some (false, P)
end.

Definition envs_delete {PROP} (remove_intuitionistic : bool)
    (i : ident) (p : bool) (Δ : envs PROP) : envs PROP :=
  let (Γp,Γs,n) := Δ in
  match p with
  | true => Envs (if remove_intuitionistic then env_delete i Γp else Γp) Γs n
  | false => Envs Γp (env_delete i Γs) n
  end.

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
(* lookup, app, delete *)

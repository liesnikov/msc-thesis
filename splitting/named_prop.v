From iris.bi Require Export bi.
From iris.bi Require Import tactics.
From iris.proofmode Require Import base.
From iris.algebra Require Export base.
Set Default Proof Using "Type".
Import bi.

Definition mrkd_ident : Type := bool * ident.
Definition get_ident (m : mrkd_ident) := snd m.

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

Fixpoint env_lookup_true {A} (i : ident) (Γ : env A) : option A :=
  match Γ with
  | Enil => None
  | Esnoc Γ (b,j) x => if ident_beq i j && b then Some x else env_lookup_true i Γ
  end.

Module env_notations.
  Notation "y ≫= f" := (pm_option_bind f y).
  Notation "x ← y ; z" := (y ≫= λ x, z).
  Notation "' x1 .. xn ← y ; z" := (y ≫= (λ x1, .. (λ xn, z) .. )).
  Notation "Γ !! j" := (env_lookup j Γ).
  Notation "Γ !!! j" := (env_lookup_true j Γ).
End env_notations.
Import env_notations.

Local Open Scope lazy_bool_scope.

Inductive env_wf {A : Type}: env A → Prop :=
  | Enil_wf : env_wf Enil
  | Esnoc_wf Γ i b x : Γ !! i = None → env_wf Γ → env_wf (Esnoc Γ (b,i) x).

Fixpoint env_to_list_all {A} (E : env A) : list A :=
  match E with
  | Enil => []
  | Esnoc Γ (_,_) x => x :: env_to_list_all Γ
  end.

Fixpoint env_to_list {A} (E : env A) : list A :=
  match E with
  | Enil => []
  | Esnoc Γ (b,_) x => if b
                      then x :: env_to_list Γ
                      else env_to_list Γ
  end.
Coercion env_to_list : env >-> list.

Fixpoint env_app {A} (Γapp : env A) (Γ : env A) : option (env A) :=
  match Γapp with
  | Enil => Some Γ
  | Esnoc Γapp i x =>
     Γ' ← env_app Γapp Γ;
     match Γ' !! (get_ident i) with None => Some (Esnoc Γ' i x) | Some _ => None end
  end.

Fixpoint env_delete {A} (i : ident) (Γ : env A) : env A :=
  match Γ with
  | Enil => Enil
  | Esnoc Γ (true,j) x => if ident_beq i j then Γ else Esnoc (env_delete i Γ) (true, j) x
  | Esnoc Γ (false,j) x => Esnoc (env_delete i Γ) (false, j) x
  end.

Fixpoint env_Forall {A} (f : bool -> A -> bool) (Δ : env A): bool :=
  match Δ with
  | Enil => true
  | Esnoc Γ (b, _) x => if f b x then env_Forall f Γ else false
  end.

Section env.
Context {A : Type}.
Implicit Types Γ : env A.
Implicit Types i : ident.
Implicit Types x : A.
Hint Resolve Esnoc_wf Enil_wf : core.

Ltac simplify :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H : context [ident_beq ?s1 ?s2] |- _ => destruct (ident_beq_reflect s1 s2)
  | |- context [ident_beq ?s1 ?s2] => destruct (ident_beq_reflect s1 s2)
  | H : context [pm_option_bind _ ?x] |- _ => destruct x eqn:?
  | |- context [pm_option_bind _ ?x] => destruct x eqn:?
  | _ => case_match
         end.

Lemma env_lookup_perm Γ i x : Γ !!! i = Some x → Γ ≡ₚ x :: env_delete i Γ.
Proof.
  induction Γ; intros; simplify; rewrite 1?Permutation_swap; try (f_equiv); eauto.
Qed.

Lemma env_app_perm Γ Γapp Γ' :
  env_app Γapp Γ = Some Γ' → env_to_list Γ' ≡ₚ Γapp ++ Γ.
Proof. revert Γ'; induction Γapp; intros; simplify; f_equal; auto. Qed.
Lemma env_app_fresh Γ Γapp Γ' i :
  env_app Γapp Γ = Some Γ' → Γapp !! i = None → Γ !! i = None → Γ' !! i = None.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.
Lemma env_app_fresh_1 Γ Γapp Γ' i x :
  env_app Γapp Γ = Some Γ' → Γ' !! i = None → Γ !! i = None.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.
Lemma env_app_disjoint Γ Γapp Γ' i :
  env_app Γapp Γ = Some Γ' → Γapp !! i = None ∨ Γ !! i = None.
Proof.
  revert Γ'.
  induction Γapp; intros; simplify; naive_solver eauto using env_app_fresh_1.
Qed.
Lemma env_app_wf Γ Γapp Γ' : env_app Γapp Γ = Some Γ' → env_wf Γ → env_wf Γ'.
Proof.
  revert Γ'. induction Γapp; intros; simplify; try(destruct m eqn: me); eauto.
Qed.

Lemma env_lookup_env_lookup_true Γ j : Γ !! j = None -> Γ !!! j = None.
Proof. induction Γ; intros; simplify; auto. Qed.
Lemma env_lookup_env_delete Γ j : env_wf Γ → (env_delete j Γ) !!! j = None.
Proof. induction 1; intros; simplify; eauto using env_lookup_env_lookup_true. Qed.
Lemma env_lookup_env_delete_ne Γ i j : i ≠ j → env_delete j Γ !! i = Γ !! i.
Proof. induction Γ; intros; simplify; eauto. Qed.
Lemma env_delete_fresh Γ i j : Γ !! i = None → env_delete j Γ !! i = None.
Proof. induction Γ; intros; simplify; eauto. Qed.

Lemma env_delete_wf Γ j : env_wf Γ → env_wf (env_delete j Γ).
Proof. induction 1; simplify; eauto using env_delete_fresh. Qed.
End env.

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


Definition env_spatial_is_nil {PROP} (Δ : envs PROP) : bool :=
  env_Forall (fun b _ => negb b) (env_spatial Δ).

Definition envs_clear_spatial {PROP} (Δ : envs PROP) : envs PROP :=
  Envs (env_intuitionistic Δ) Enil (env_counter Δ).

Definition envs_clear_intuitionistic {PROP} (Δ : envs PROP) : envs PROP :=
  Envs Enil (env_spatial Δ) (env_counter Δ).

Definition envs_incr_counter {PROP} (Δ : envs PROP) : envs PROP :=
  Envs (env_intuitionistic Δ) (env_spatial Δ) (Pos_succ (env_counter Δ)).

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

Lemma of_envs_eq {PROP : bi} {Δ : envs PROP} :
  of_envs Δ = (⌜envs_wf Δ⌝ ∧ □ [∧] env_intuitionistic Δ ∗ [∗] env_spatial Δ)%I.
Proof. done. Qed.

Definition envs_snoc {PROP} (Δ : envs PROP)
    (p : bool) (b : bool) (j : ident) (P : PROP) : envs PROP :=
  let (Γp,Γs,n) := Δ in
  if p then Envs (Esnoc Γp (b,j) P) Γs n else Envs Γp (Esnoc Γs (b,j) P) n.


Definition envs_app {PROP : bi} (p : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  let (Γp,Γs,n) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_app Γ Γp; Some (Envs Γp' Γs n)
  | false => _ ← env_app Γ Γp; Γs' ← env_app Γ Γs; Some (Envs Γp Γs' n)
end.


Definition envs_lookup_true {PROP} (i : ident) (Δ : envs PROP) : option (bool * PROP) :=
  let (Γp,Γs,n) := Δ in
  match env_lookup_true i Γp with
  | Some P => Some (true, P)
  | None => P ← env_lookup_true i Γs; Some (false, P)
  end.

Definition envs_delete {PROP} (remove_intuitionistic : bool)
    (i : ident) (p : bool) (Δ : envs PROP) : envs PROP :=
  let (Γp,Γs,n) := Δ in
  match p with
  | true => Envs (if remove_intuitionistic then env_delete i Γp else Γp) Γs n
  | false => Envs Γp (env_delete i Γs) n
  end.


Fixpoint envs_split_go {PROP}
  (bs : list bool) (Δ : env PROP) : option (env PROP * env PROP) :=
  match Δ, bs with
  | Enil, [] => Some (Enil, Enil)
  | Esnoc Δ (b,j) x, bh :: bt =>
    ''(Δ1,Δ2) ← envs_split_go bt Δ;
      mret (Esnoc Δ1 (bh && b, j) x, Esnoc Δ2 (negb bh && b, j) x)
  | _, _ => None
  end.


Definition envs_split {PROP}
  (bs : list bool) (Δ : envs PROP) : option (envs PROP * envs PROP) :=
  ''(Δ1,Δ2) ← envs_split_go bs (env_spatial Δ);
  mret (Envs (env_intuitionistic Δ) Δ1 (env_counter Δ),
        Envs (env_intuitionistic Δ) Δ2 (env_counter Δ)).

Section envs.
Context {PROP : bi}.
Implicit Types Γ Γp Γs : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.

Lemma env_spatial_is_nil_to_list Δ :
  env_spatial_is_nil Δ = true -> env_to_list (env_spatial Δ) = [].
Proof.
  destruct Δ as [d1 Δ d3]; cbn.
  intros.
  induction Δ; auto.
  - destruct m as [[|] x] eqn: e.
    + now contradict H.
    + apply IHΔ, H.
Qed.

Lemma env_spatial_is_nil_intuitionistically Δ :
  env_spatial_is_nil Δ = true → of_envs Δ ⊢ □ of_envs Δ.
Proof.
  intros. rewrite !of_envs_eq.
  apply env_spatial_is_nil_to_list in H. rewrite !H.
  destruct Δ as [? []]; simplify_eq/=;
  rewrite !right_id /bi_intuitionistically {1}affinely_and_r persistently_and;
  by rewrite persistently_affinely_elim persistently_idemp persistently_pure.
Qed.

Lemma envs_app_sound Δ Δ' p Γ :
  envs_app p Γ Δ = Some Δ' →
  of_envs Δ ⊢ (if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ'.
Proof.
  rewrite !of_envs_eq /envs_app=> ?; apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_app Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γp') //.
      rewrite big_opL_app intuitionistically_and and_sep_intuitionistically.
      solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_app Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γs') // big_opL_app. solve_sep_entails.
Qed.

Lemma envs_app_singleton_sound Δ Δ' p j Q :
  envs_app p (Esnoc Enil (true,j) Q) Δ = Some Δ' → of_envs Δ ⊢ □?p Q -∗ of_envs Δ'.
Proof. move=> /envs_app_sound. destruct p; by rewrite /= right_id. Qed.

Lemma envs_lookup_sound' Δ rp i p P :
  envs_lookup_true i Δ = Some (p,P) →
  of_envs Δ ⊢ □?p P ∗ of_envs (envs_delete rp i p Δ).
Proof.
  rewrite /envs_lookup_true /envs_delete !of_envs_eq=>?.
  apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !!! i) eqn:?; simplify_eq/=.
  - rewrite pure_True ?left_id;
    last (destruct Hwf, rp; constructor; cbn; naive_solver eauto using env_delete_wf, env_delete_fresh).
    destruct rp.
    + rewrite (env_lookup_perm Γp) //= intuitionistically_and.
      by rewrite and_sep_intuitionistically -assoc.
    + rewrite {1}intuitionistically_sep_dup {1}(env_lookup_perm Γp) //=.
      by rewrite intuitionistically_and and_elim_l -assoc.
  - destruct (Γs !!! i) eqn:?; simplify_eq/=.
    rewrite pure_True ?left_id;
    last (destruct Hwf, rp; constructor; cbn; naive_solver eauto using env_delete_wf, env_delete_fresh).
    rewrite (env_lookup_perm Γs) //=. by rewrite !assoc -(comm _ P).
Qed.

Lemma envs_lookup_sound Δ i p P :
  envs_lookup_true i Δ = Some (p,P) →
  of_envs Δ ⊢ □?p P ∗ of_envs (envs_delete true i p Δ).
Proof. apply envs_lookup_sound'. Qed.

Lemma envs_clear_spatial_sound Δ :
  of_envs Δ ⊢ of_envs (envs_clear_spatial Δ) ∗ [∗] env_spatial Δ.
Proof.
  rewrite !of_envs_eq /envs_clear_spatial /=. apply pure_elim_l=> Hwf.
  rewrite right_id -persistent_and_sep_assoc. apply and_intro; [|done].
  apply pure_intro. destruct Hwf; constructor; simpl; auto using Enil_wf.
Qed.

Lemma envs_split_go_sound Δi Δs bs Δs1 Δs2 c:
  envs_split_go bs Δs = Some (Δs1, Δs2) ->
  of_envs (Envs Δi Δs c) ⊢ of_envs (Envs Δi Δs1 c) ∗ @of_envs PROP (Envs Δi Δs2 c).
Proof.
  revert Δs1 Δs2.
  induction bs, Δs as [|Δs b j IH]=> Δs1 Δs2; cbn.
  - injection 1 => [<-] [<-] //.
    unfold of_envs, of_envs'. cbn.
    rewrite <-persistently_and_intuitionistically_sep_l at 1.
    rewrite (and_elim_l _ (emp)%I)
            persistently_and_intuitionistically_sep_r.
    rewrite <-persistently_pure at 1. rewrite -> persistently_sep_dup at 1.
    rewrite persistently_pure.
    rewrite ->intuitionistically_sep_dup at 1.
    rewrite <-sep_assoc, (sep_assoc _ (□ [∧] Δi)%I), (sep_comm _ (□ [∧] Δi)%I), ->(sep_assoc (⌜_⌝)%I _).
    admit.
  - destruct b; congruence.
  - congruence.
  - admit.
Admitted.


Lemma envs_split_sound Δ bs Δ1 Δ2 :
  envs_split bs Δ = Some (Δ1,Δ2) → of_envs Δ ⊢ of_envs Δ1 ∗ of_envs Δ2.
Proof.
  rewrite /envs_split=> Hyp.
  (* rewrite -(idemp bi_and (of_envs Δ)).
  rewrite {2}envs_clear_spatial_sound.
  rewrite (env_spatial_is_nil_intuitionistically (envs_clear_spatial _)) //.
  rewrite -persistently_and_intuitionistically_sep_l.
  rewrite (and_elim_l (<pers> _)%I)
          persistently_and_intuitionistically_sep_r intuitionistically_elim. *)
  destruct Δ as [Δi Δs c]. unfold envs_clear_spatial. cbn in *.
  destruct (envs_split_go _ _) as [[Δ1' Δ2']|] eqn:HΔ; [|done]. cbn in *.
  injection Hyp => Hyp1 Hyp2. rewrite -Hyp1 -Hyp2.
  apply (envs_split_go_sound _ _ bs). done.
Qed.
End envs.



Notation "" := Enil (only printing) : proof_scope.
Notation "Γ H : P" := (Esnoc Γ (INamed H) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ H  :  '[' P ']' '//'", only printing) : proof_scope.
Notation "Γ '_' : P" := (Esnoc Γ (IAnon _) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ '_'  :  '[' P ']' '//'", only printing) : proof_scope.

Set Default Proof Using "Type".
Delimit Scope proof_scope with env.
Arguments Envs _ _%proof_scope _%proof_scope _.
Arguments Enil {_}.
Arguments Esnoc {_} _%proof_scope _%string _%I.

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

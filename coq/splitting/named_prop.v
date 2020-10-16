From iris.bi Require Export bi.
From iris.bi Require Import tactics.
From iris.proofmode Require Import base.
From iris.algebra Require Export base.
Export ident.

Set Default Proof Using "Type".
Import bi.

Definition mrkd_ident : Type := bool * ident.
Definition get_ident (m : mrkd_ident) :=
  match m with
  | (_, i) => i
  end.

Definition negb (b : bool) := if b then false else true.

Inductive env (B : Type) : Type :=
  | Enil : env B
  | Esnoc : env B → mrkd_ident -> B -> env B.
Arguments Enil {_}.
Arguments Esnoc {_} _ _ _.
Instance: Params (@Enil) 1 := {}.
Instance: Params (@Esnoc) 1 := {}.

Fixpoint env_lookup_with_constr {A} (i : ident) (Γ : env A) : option (bool * A) :=
  match Γ with
  | Enil => None
  | Esnoc Γ (b,j) x => if ident_beq i j then Some (b,x) else env_lookup_with_constr i Γ
  end.

Fixpoint env_lookup {A} (i : ident) (Γ : env A) : option A :=
 match Γ with
  | Enil => None
  | Esnoc Γ (b,j) x => if ident_beq i j then Some x else env_lookup i Γ
  end.

Fixpoint env_lookup_true {A} (i : ident) (Γ : env A) : option A :=
  match Γ with
  | Enil => None
  | Esnoc Γ (b,j) x => if ident_beq i j then (if b then Some x else None) else env_lookup_true i Γ
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
     match Γ' !! (get_ident i) with
     | None => Some (Esnoc Γ' i x)
     | Some _ => None end
  end.

Fixpoint env_delete {A} (i : ident) (Γ : env A) : env A :=
  match Γ with
  | Enil => Enil
  | Esnoc Γ (b, j) x =>
    if ident_beq i j then Γ else Esnoc (env_delete i Γ) (b,j) x
  end.

Fixpoint env_replace {A} (i: ident) (Γi: env A) (Γ: env A) : option (env A) :=
  match Γ with
  | Enil => None
  | Esnoc Γ (b,j) x =>
    if ident_beq i j then env_app Γi Γ
    else match Γi !! j with
     | None => Γ' ← env_replace i Γi Γ; Some (Esnoc Γ' (b,j) x)
     | Some _ => None
     end
  end.

Fixpoint env_Forall {A} (f : bool -> A -> bool) (Δ : env A): bool :=
  match Δ with
  | Enil => true
  | Esnoc Γ (b, _) x => if f b x then env_Forall f Γ else false
  end.


Fixpoint env_split_go {A}
  (bs : list bool) (Δ : env A) : option (env A * env A) :=
  match Δ, bs with
  | Enil, [] => Some (Enil, Enil)
  | Esnoc Δ cj x, bh :: bt =>
    match cj with
    | (c, j) =>
      ''(Δ1,Δ2) ← env_split_go bt Δ;
      mret (Esnoc Δ1 (bh && c, j) x, Esnoc Δ2 (negb bh && c, j) x)
    end
  | _, _ => None
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

Lemma env_lookup_env_lookup_with_constr Γ i x:
  Γ !! i = Some x <-> exists b, env_lookup_with_constr i Γ = Some(b,x).
Proof.
  move : Γ. induction Γ; simplify; naive_solver.
Qed.

Lemma env_lookup_with_constr_env_lookup_true Γ i x:
  env_lookup_with_constr i Γ = Some (true, x) <-> env_lookup_true i Γ = Some x.
Proof.
  move : Γ x i. induction Γ => x i.
  - naive_solver.
  - destruct m; simplify; try (naive_solver).
Qed.

Lemma env_lookup_perm Γ i x : Γ !!! i = Some x → Γ ≡ₚ x :: env_delete i Γ.
Proof.
  induction Γ; intros; simplify; rewrite 1?Permutation_swap; try (f_equiv); eauto.
Qed.

Lemma env_lookup_with_constr_perm Γ i c x:
  env_lookup_with_constr i Γ = Some (c,x) →
  Γ ≡ₚ (if c then [x] else []) ++ env_delete i Γ.
Proof.
  destruct c.
  - rewrite env_lookup_with_constr_env_lookup_true => H.
    rewrite env_lookup_perm //=.
  - induction Γ; intros; simplify; rewrite 1?Permutation_swap; eauto.
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

Lemma env_replace_fresh Γ Γj Γ' i j :
  env_replace j Γj Γ = Some Γ' →
  Γj !! i = None → env_delete j Γ !! i = None → Γ' !! i = None.
Proof. revert Γ'. induction Γ; intros; simplify; eauto using env_app_fresh. Qed.


(* FIXME: prettify this *)
Lemma env_replace_wf Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → env_wf (env_delete i Γ) → env_wf Γ'.
Proof.
  revert Γ'. induction Γ; intros ??; [done|].
  revert H. simpl. destruct m as [b' j].
  destruct (ident_beq) eqn: ibe.
  - apply env_app_wf.
  - destruct (Γi !! j) eqn: indxe; [done|].
    destruct (env_replace) as [Γ''|] eqn: erpe; [|done].
    cbn. injection 1. move {H} => H. subst.
    inversion_clear 1.
    constructor. apply (env_replace_fresh _ _ _ _ _ erpe).
    done. done. apply IHΓ. done. done.
Qed.

Lemma env_replace_lookup Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → is_Some (Γ !! i).
Proof. revert Γ'. induction Γ; intros; simplify; eauto. Qed.
Lemma env_replace_perm Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → Γ' ≡ₚ Γi ++ env_delete i Γ.
Proof.
  revert Γ'. induction Γ as [|Γ IH j y]=>Γ' ?; simplify; auto using env_app_perm.
  rewrite -Permutation_middle -IH //.
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


Lemma env_split_same_ids (Δs Δs1 Δs2 : env A) bs:
  env_split_go bs Δs = Some (Δs1, Δs2) ->
  forall i, Δs !! i = Δs1 !! i /\  Δs !! i = Δs2 !! i.
Proof.
    move: Δs bs Δs1 Δs2.
    induction Δs as [|Δs IH] => bs Δs1 Δs2; destruct bs.
    - rewrite /env_split_go //= => [=]<- <-.
      split; constructor; done.
    - done.
    - by destruct m.
    - cbn. destruct m, (env_split_go bs Δs) as [|] eqn: ?; [|done].
      destruct p as [Δ1 Δ2].
      move => [=] <- <- j //=.
      destruct (IH _ _ _ Heqo j), (ident_beq _ _); done.
Qed.

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

Definition envs_lookup_with_constr {PROP} (i : ident) (Δ : envs PROP) : option (bool * bool * PROP) :=
  let (Γp,Γs,n) := Δ in
  match env_lookup_with_constr i Γp with
  | Some (b, P) => Some (true, b, P)
  | None => b_P ← env_lookup_with_constr i Γs; Some (false, fst b_P,  snd b_P)
  end.

Definition envs_lookup {PROP} (i : ident) (Δ : envs PROP) : option (bool * PROP) :=
  let (Γp,Γs,n) := Δ in
  match Γp !! i with
  | Some P => Some (true, P)
  | None => P ← Γs !! i; Some (false, P)
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

Definition envs_split {PROP}
  (bs : list bool) (Δ : envs PROP) : option (envs PROP * envs PROP) :=
  ''(Δ1,Δ2) ← env_split_go bs (env_spatial Δ);
  mret (Envs (env_intuitionistic Δ) Δ1 (env_counter Δ),
        Envs (env_intuitionistic Δ) Δ2 (env_counter Δ)).

Definition envs_simple_replace {PROP : bi} (i : ident) (p : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  let (Γp,Γs,n) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_replace i Γ Γp; Some (Envs Γp' Γs n)
  | false => _ ← env_app Γ Γp; Γs' ← env_replace i Γ Γs; Some (Envs Γp Γs' n)
  end.

Definition envs_replace {PROP : bi} (i : ident) (p q : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  if beq p q then envs_simple_replace i p Γ Δ
  else envs_app q Γ (envs_delete true i p Δ).

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

Lemma envs_lookup_envs_lookup_with_constr Δ i b x:
  envs_lookup i Δ = Some (b, x) <->
  exists c, envs_lookup_with_constr i Δ = Some(b, c, x).
Proof.
  destruct Δ. cbn.
  destruct (env_intuitionistic0 !! i) eqn: Hi.
  - apply env_lookup_env_lookup_with_constr in Hi.
    destruct Hi as [e ->]. naive_solver.
  - destruct env_lookup_with_constr as [[c P]|] eqn: Heqi. {
      pattern c in Heqi.
      apply ex_intro, env_lookup_env_lookup_with_constr in Heqi. congruence. }
    destruct (env_spatial0 !! i) eqn: Hs.
    + cbn. apply env_lookup_env_lookup_with_constr in Hs.
      destruct Hs as [e ->]. naive_solver.
    + destruct (env_lookup_with_constr i env_spatial0) as [[c P]|] eqn: Heqs. {
        pattern c in Heqs.
        apply ex_intro, env_lookup_env_lookup_with_constr in Heqs. congruence.
      }
      naive_solver.
Qed.

Lemma envs_lookup_with_constr_envs_lookup_true Δ i c x:
  envs_wf Δ -> envs_lookup_with_constr i Δ = Some (c, true, x) <-> envs_lookup_true i Δ = Some (c, x).
Proof.
  intros. destruct Δ as [Δi Δs]. cbn.
  destruct (Δi !!! i) eqn: Hi. {
    apply (env_lookup_with_constr_env_lookup_true _ _ _) in Hi.
    rewrite Hi; naive_solver. }
  destruct (env_lookup_with_constr i Δi) as [[[|] P]|] eqn: Heqi.
  - apply env_lookup_with_constr_env_lookup_true in Heqi; by try congruence.
  - pattern false in Heqi.
    apply ex_intro, env_lookup_env_lookup_with_constr in Heqi.
    destruct H as [_ _ disj], (disj i) as [Hd | Hd]; cbn in Hd; [congruence|].
    rewrite (env_lookup_env_lookup_true _ _ Hd). naive_solver.
  - destruct (Δs !!! i) eqn: Hs. {
      apply (env_lookup_with_constr_env_lookup_true _ _ _) in Hs.
      rewrite Hs; naive_solver. }
    destruct (env_lookup_with_constr i Δs) as [[[|] P]|] eqn: Heqs; [|naive_solver | naive_solver].
    apply env_lookup_with_constr_env_lookup_true in Heqs; by try congruence.
Qed.

Lemma envs_lookup_sound Δ i p P :
  envs_lookup_true i Δ = Some (p, P) ->
  of_envs Δ ⊢ □?p P ∗ of_envs (envs_delete true i p Δ).
Proof. apply envs_lookup_sound'. Qed.


Lemma envs_lookup_sound_with_constr Δ i p c P:
  envs_lookup_with_constr i Δ = Some (p, c, P) ->
  of_envs Δ ⊢ (if c then □?p P else emp) ∗ of_envs (envs_delete true i p Δ).
Proof.
  intro.
  apply pure_elim with (envs_wf Δ).
  { rewrite of_envs_eq. apply and_elim_l. }
  move => Hwf.
  destruct c. {
    apply envs_lookup_with_constr_envs_lookup_true in H;[|done].
    by apply envs_lookup_sound.
  }
  rewrite emp_sep !of_envs_eq.
  apply pure_elim_l=> _.
  destruct Δ as [Γp Γs], (env_lookup_with_constr i Γp) as [[p' P']|] eqn:Heq;
  cbn in H; rewrite Heq in H; simplify_eq /=.
  - rewrite pure_True ?left_id.
    + by rewrite (env_lookup_with_constr_perm Γp i) //=.
    + destruct Hwf; constructor; cbn;
      naive_solver eauto using env_delete_wf, env_delete_fresh.
  - destruct (env_lookup_with_constr i Γs) as [[p' P']|] eqn:?; simplify_eq/=.
    rewrite pure_True ?left_id.
    + by rewrite (env_lookup_with_constr_perm Γs i) //=.
    + destruct Hwf; constructor; cbn;
      naive_solver eauto using env_delete_wf, env_delete_fresh.
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

Lemma envs_app_singleton_sound_with_constr Δ Δ' p j c Q :
  envs_app p (Esnoc Enil (c,j) Q) Δ = Some Δ' → of_envs Δ ⊢ (if c then □?p Q else emp) -∗ of_envs Δ'.
Proof. move=> /envs_app_sound. destruct p, c; by rewrite ?intuitionistically_True_emp /= ?right_id. Qed.

Lemma envs_simple_replace_sound' Δ Δ' i p Γ :
  envs_simple_replace i p Γ Δ = Some Δ' →
  of_envs (envs_delete true i p Δ) ⊢ (if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ'.
Proof.
  rewrite /envs_simple_replace /envs_delete !of_envs_eq=> ?.
  apply pure_elim_l=> Hwf. destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_replace i Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γp') //.
      rewrite big_opL_app intuitionistically_and and_sep_intuitionistically.
      solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_replace i Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γs') // big_opL_app. solve_sep_entails.
Qed.

Lemma envs_simple_replace_singleton_sound' Δ Δ' i p j c Q :
  envs_simple_replace i p (Esnoc Enil (c, j) Q) Δ = Some Δ' →
  of_envs (envs_delete true i p Δ) ⊢ (if c then □?p Q else emp) -∗ of_envs Δ'.
Proof. move=> /envs_simple_replace_sound'.
       destruct p, c; by rewrite /= ?right_id ?intuitionistically_True_emp.
Qed.

Lemma envs_simple_replace_singleton_sound_with_constr Δ Δ' i p P j c c' Q :
  envs_lookup_with_constr i Δ = Some (p, c, P) →
  envs_simple_replace i p (Esnoc Enil (c', j) Q) Δ = Some Δ' →
  of_envs Δ ⊢ (if c then □?p P else emp) ∗
              ((if c' then □?p Q else emp) -∗ of_envs Δ').
Proof.
  intros.
  destruct c, c';
  by rewrite envs_lookup_sound_with_constr// envs_simple_replace_singleton_sound'//.
Qed.

Lemma envs_simple_replace_sound Δ Δ' i p P Γ :
  envs_lookup_true i Δ = Some (p, P)  → envs_simple_replace i p Γ Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ ((if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_simple_replace_sound'//. Qed.

Lemma envs_simple_replace_sound_with_constr Δ Δ' i p c P Γ:
  envs_lookup_with_constr i Δ = Some (p, c, P) →
  envs_simple_replace i p Γ Δ = Some Δ' →
  of_envs Δ ⊢ (if c then □?p P else emp) ∗ ((if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ').
Proof.
  destruct c.
  - simpl.
    move => A B. apply pure_elim with (envs_wf Δ).
    { rewrite of_envs_eq. apply and_elim_l. }
    move => wf. move: A B.
    rewrite envs_lookup_with_constr_envs_lookup_true //=. apply envs_simple_replace_sound.
  - move => H HP.
    enough (of_envs Δ ⊢ of_envs (envs_delete true i p Δ)) as HE. {
      rewrite HE emp_sep envs_simple_replace_sound' //=.
    }
    rewrite -(emp_sep (of_envs (envs_delete _ _ _ _))%I).
    by apply (envs_lookup_sound_with_constr _ _ _ false P).
Qed.

Lemma envs_clear_spatial_sound Δ :
  of_envs Δ ⊢ of_envs (envs_clear_spatial Δ) ∗ [∗] env_spatial Δ.
Proof.
  rewrite !of_envs_eq /envs_clear_spatial /=. apply pure_elim_l=> Hwf.
  rewrite right_id -persistent_and_sep_assoc. apply and_intro; [|done].
  apply pure_intro. destruct Hwf; constructor; simpl; auto using Enil_wf.
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


(* Lemma envs_take_apart Δ:
  of_envs Δ ⊢ □ (⌜envs_wf Δ⌝ ∧ □ [∧] (env_intuitionistic Δ)) ∗ [∗] (env_spatial Δ).
Proof.
  destruct Δ as [Δi Δs c].
  assert (of_envs (Envs Δi Δs c) ⊢ (⌜envs_wf' Δi Δs⌝ ∧ □ [∧] Δi) ∗ [∗] Δs). {
    rewrite of_envs_eq //=.
    apply pure_elim_l=>H1. apply sep_mono; [|done].
    apply and_intro; by try (apply pure_intro).
  }

  assert (⌜envs_wf' Δi Δs⌝ ∧ □ [∧] Δi ⊢ □ (⌜envs_wf' Δi Δs⌝ ∧ □ [∧] Δi)). {
    rewrite /bi_intuitionistically {1}affinely_and_r persistently_and;
    by rewrite persistently_affinely_elim persistently_idemp persistently_pure.
  }

  rewrite H {1}H0 /envs_wf //=.
Qed. *)


Lemma env_split_go_wf (Δi Δs Δs1 Δs2 : env PROP) bs c:
  env_split_go bs Δs = Some (Δs1, Δs2) -> envs_wf (Envs Δi Δs c) ->
  envs_wf (Envs Δi Δs1 c) /\ envs_wf (Envs Δi Δs2 c).
Proof.
  move => H. move : Δs bs Δs1 Δs2 H.
  induction Δs as [|Δs IH] => bs Δs1 Δs2; destruct bs.
  - rewrite /env_split_go //= => [=]<- <- [Hi Hs H].
    split; constructor; done.
  - done.
  - by destruct m.
  - cbn. destruct m, (env_split_go bs Δs) as [|] eqn: Heqo; [|done].
    destruct p as [Δ1 Δ2].
    move => [=] <- <- [Hi Hs H].
    destruct (IH _ _ _ Heqo).
    + constructor; [done| |]; inversion Hs.
      assumption. intros i'. destruct (H i'); [by left|right].
      cbn in *. destruct (ident_beq _ _); done.
    + split; (constructor; [done|constructor|]);
        pose (env_split_same_ids _ _ _ _ Heqo) as E;
        destruct (E i) as [R1 R2]; rewrite -?R1 -?R2 {R1 R2}.
      1,4: by inversion Hs.
      1,3: by (destruct H0; destruct H1).
      1,2: move => j; (destruct (H j) as [J|J]; [by left|]);
           right; move: J; cbn;
           destruct (ident_beq _ _), (E j) as [R1 R2];
           rewrite -?R1 -?R2 //.
Qed.

Lemma env_split_go_sound Δi Δs bs Δs1 Δs2 c:
  env_split_go bs Δs = Some (Δs1, Δs2) ->
  of_envs (Envs Δi Δs c) ⊢ of_envs (Envs Δi Δs1 c) ∗ (@of_envs PROP (Envs Δi Δs2 c)).
Proof.
  move => S.
  assert (of_envs (Envs Δi Δs c) ⊢
          (⌜envs_wf' Δi Δs⌝ ∧ □ [∧] Δi) ∗
          (⌜envs_wf' Δi Δs⌝ ∧ □ [∧] Δi) ∗ [∗] Δs) as Renvs. {
    assert (of_envs (Envs Δi Δs c) ⊢
           (⌜envs_wf' Δi Δs⌝ ∧ □ [∧] Δi) ∗ [∗] Δs) as H0. {
     rewrite of_envs_eq //=.
     apply pure_elim_l=>H1. apply sep_mono; [|done].
     apply and_intro; by try (apply pure_intro).
   }
    assert (forall A (B : PROP),
           (⌜A⌝ ∧ □ B) ⊢ □ (⌜A⌝ ∧ □ B)) as H1. {
     rewrite /bi_intuitionistically => A B.
     rewrite {1}(affinely_and_r (⌜_⌝)%I (<pers> _)%I) persistently_and.
     by rewrite persistently_affinely_elim persistently_idemp persistently_pure.
   }
   rewrite H0 {1}H1 /envs_wf.
   by rewrite intuitionistically_sep_dup intuitionistically_elim /envs_wf //= assoc.
  }

  assert ([∗] Δs ⊢ [∗] Δs1 ∗ [∗] Δs2) as M. {
    move: Δs bs Δs1 Δs2 S {Renvs}.
    induction Δs as [|Δs IH m p] => bs Δs1 Δs2.
    - destruct bs; [|done].
      move => [=] <- <-. by rewrite sep_emp.
    - destruct bs, m; [done|]. simpl.
      destruct (env_split_go _ _) as [|] eqn: ?; [|done].
      destruct p0 as [Δ1 Δ2]. move => [=]<- <-.
      destruct b0, b; simpl; rewrite IH //.
      + rewrite assoc //.
      + rewrite (comm _ ([∗] _)%I ([∗] _)%I) assoc comm //.
  }

  assert (forall (b c a : PROP), ((b ∧ c) ∗ a) ⊢ (b ∗ a) ∧ (c ∗ a)) as sep_and_dist_1. {
    intros.
    apply and_intro; apply sep_mono; try done.
    apply and_elim_l. apply and_elim_r.
  }

  rewrite Renvs M {Renvs M}.
  rewrite 2!assoc -(assoc _ _ _ ([∗] Δs1)%I)
          (comm _ _ ([∗] Δs1)%I) assoc -assoc.
  rewrite 2! (sep_and_dist_1 _ _ ([∗] _)%I ).
  rewrite -absorbingly_pure 2! sep_elim_l absorbingly_pure.
  rewrite 2! of_envs_eq 2! /envs_wf //=.
  rewrite sep_mono; [done| |];
  apply pure_elim_l=>WF;
  destruct (env_split_go_wf _ _ _ _ _ c S WF);
  (apply and_intro; [by apply pure_intro | by apply sep_mono]).
Qed.

Lemma envs_split_sound Δ bs Δ1 Δ2 :
  envs_split bs Δ = Some (Δ1,Δ2) → of_envs Δ ⊢ of_envs Δ1 ∗ of_envs Δ2.
Proof.
  rewrite /envs_split=> Hyp.
  destruct Δ as [Δi Δs c]. unfold envs_clear_spatial. cbn in *.
  destruct (env_split_go _ _) as [[Δ1' Δ2']|] eqn:HΔ; [|done]. cbn in *.
  injection Hyp => Hyp1 Hyp2. rewrite -Hyp1 -Hyp2.
  apply (env_split_go_sound _ _ bs). done.
Qed.
End envs.

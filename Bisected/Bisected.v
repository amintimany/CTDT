Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.omega.Omega.
Require Import Essentials.Notations.
Require Import Essentials.Facts_Tactics.

Local Axiom PropExt : prop_extensionality.

Delimit Scope bisected_scope with bisected.

Local Open Scope bisected_scope.

Record BiDist : Type :=
  {
    BD_agree :> nat → Prop;
    BD_decreases : ∀ n m, n ≤ m → BD_agree m → BD_agree n
  }
.

Arguments BD_agree _ _ : assert.
Arguments BD_decreases _ _ _ _ _ : assert.

Local Hint Resolve BD_decreases.

Theorem BiDist_eq_simpl (d d' : BiDist) : BD_agree d = BD_agree d' → d = d'.
Proof.
  intros H.
  destruct d; destruct d'; cbn in *.
  ElimEq.
  PIR; trivial.
Qed.  

Definition BD_bot : BiDist :=
  {|
    BD_agree := fun _ => True;
    BD_decreases := fun _ _ _ _ => I
  |}
.

Notation "⊥" := BD_bot : bisected_scope.

Definition BD_LE (d d' : BiDist) : Prop :=
  ∀ n, d' n → d n
.

Notation "d ⊑ d'" := (BD_LE d d') : bisected_scope.

Definition BD_LT (d d' : BiDist) : Prop :=
  d ⊑ d' ∧ d ≠ d'
.
                    
Notation "d ⊏ d'" := (BD_LT d d') : bisected_scope.
                            
Theorem BD_bot_LE : ∀ d, ⊥ ⊑ d.
Proof.
  intros d n.
  cbn; tauto.  
Qed.

Local Hint Resolve BD_bot_LE.

Theorem BD_LE_Refl : ∀ d, d ⊑ d.
Proof.
  intros d n; trivial.
Qed.  

Theorem BD_LE_ASym : ∀ d d', d ⊑ d' → d' ⊑ d → d = d'.
Proof.
  intros d d' H1 H2.
  apply BiDist_eq_simpl.
  extensionality n.
  specialize (H1 n).
  specialize (H2 n).
  apply PropExt; intuition.
Qed.  

Theorem BD_LE_Trans : ∀ d d' d'', d ⊑ d' → d' ⊑ d'' → d ⊑ d''.
Proof.
  intros d d' d'' H1 H2 n.
  auto.
Qed.  
                                    
Local Obligation Tactic := idtac.

Fixpoint BD_Half_pow_fun (n : nat) : nat → Prop :=
  match n with
  | O =>
    (
      fun _ => False
    )
  | S n' =>
    (
      fun m =>
        match m with
        | O => True
        | S m' => (BD_Half_pow_fun n' m')
        end
    )
  end
.

Theorem BD_Half_pow_fun_Sn_n (n : nat) : BD_Half_pow_fun (S n) n.
Proof.
  induction n; cbn; trivial.
Qed.  
  
                                           
Program Definition BD_Half_pow (n : nat) :=
  {|
    BD_agree := BD_Half_pow_fun n
  |}.

Next Obligation.
Proof.
  induction n.
  + tauto.
  + intros m m' H1 H2.
    destruct m; destruct m'; cbn in *; trivial; try omega.
    assert (Hx : m ≤ m') by omega.
    eapply (IHn _ _ Hx H2).
Qed.    

Theorem BD_approach_bot : ∀ d, (∀ d', ⊥ ⊏ d' → d ⊏ d') → d = ⊥.
Proof.
  intros d H1.
  apply BD_LE_ASym; [|apply BD_bot_LE].
  intros n H2.
  cut (d ⊏ BD_Half_pow (S n)); [intros [H31 H32]|].
  {
    apply H31.
    apply BD_Half_pow_fun_Sn_n.
  }
  {
    apply H1.
    split; auto.
    intros H3.
    apply (f_equal (fun x => BD_agree x (S n))) in H3.
    cbn in H3.
    induction n.
    + cbn in H3.
      rewrite <- H3; trivial.
    + apply IHn; trivial.
  }
Qed.
  
Program Definition BD_lub (d d' : BiDist) : BiDist :=
  {|
    BD_agree := fun n => d n ∧ d' n
  |}
.

Next Obligation.
Proof.
  cbn.
  intros d d' n m H1 H2.
  intuition eauto.
Qed.
  
Notation "x ⊔ y" := (BD_lub x y) : bisected_scope.

Theorem BD_lub_ub_l : ∀ (d d' : BiDist),
    d ⊑ (d ⊔ d').
Proof.
  intros d d' n; cbn; intuition.
Qed.

Theorem BD_lub_ub_r : ∀ (d d' : BiDist),
    d' ⊑ (d ⊔ d').
Proof.
  intros d d' n; cbn; intuition.
Qed.

Theorem BD_lub_least : ∀ (d d' d'': BiDist),
    d ⊑ d'' → d' ⊑ d'' → (d ⊔ d') ⊑ d''.
Proof.
  intros d d' d'' H1 H2 n; cbn.
  specialize (H1 n).
  specialize (H2 n).
  intuition.
Qed.

Theorem BD_LT_not_bot : ∀ d d', d ⊏ d' → d' ≠ ⊥.
Proof.
  intros d d' [H1 H2].
  intros H3.
  rewrite H3 in *.
  apply H2.
  apply BD_LE_ASym; auto.
Qed.

Program Definition BD_Half_of (d : BiDist) : BiDist :=
  {|
    BD_agree :=
      fun n =>
        match n return Prop with
        | O => True
        | S n' => d n'
        end
  |}.

Next Obligation.
Proof.
  intros d n m H1 H2; cbn in *.
  destruct n; destruct m; trivial; try omega.
  eapply (BD_decreases _ _ m); trivial; omega.
Qed.  

Theorem BD_pos_half_pos : ∀ d, ⊥ ⊏ d → ⊥ ⊏ BD_Half_of d.
Proof.
  intros d [H11 H12].
  split.
  {
    intros n H2.
    destruct n; cbn; auto.
  }
  {  
    intros H2.
    apply H12.
    apply BiDist_eq_simpl.
    extensionality n.
    apply (f_equal (fun x => BD_agree x (S n))) in H2.
    trivial.
  }
Qed.    
    
  
Theorem BD_pos_exists_less : ∀ d, ⊥ ⊏ d → BD_Half_of d ⊏ d.
Proof.
  intros d [H11 H12].
  split.
  {
    intros n H2.
    destruct n; cbn; eauto.
  }
  {
    intros H2.
    apply H12.
    apply BD_LE_ASym; auto.
    intros n _.
    induction n.
    + apply (f_equal (fun x => BD_agree x 0)) in H2.
      rewrite <- H2; cbn; trivial.
    + apply (f_equal (fun x => BD_agree x (S n))) in H2.
      rewrite <- H2.
      trivial.
  }
Qed.
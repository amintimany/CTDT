Require Import Coq.Logic.ClassicalFacts.
Require Import Essentials.Omega.
Require Import Essentials.Notations.
Require Import Essentials.Facts_Tactics Essentials.Definitions.
Require Import Lattice.PartialOrder Lattice.MLattice.
Require Import Metrics.Mappings.

Require Import Coq.Logic.Classical_Pred_Type.

(** Propositional extensionality assumed locally. *)
Local Axiom PropExt : prop_extensionality.

Delimit Scope bisected_scope with bisected.

Local Open Scope bisected_scope.

(** Bisected distance. Distances are 2⁻ⁿ for n a natural number or zero.
Intuitively, bisected distances are sequences of Prop such that whenever an element is
inhabitted then so are all elements before it. In other words, they are of the form

#
<pre>
True, True, True, True, True, True, True, ...
or
True, True, True, False, False, False, False, False, ...
|...............|
     n times
</pre>
#
where True and False are archetypal inhabitted and uninhabitted Propositions.

In this encoding, a sequence with n inhabitted elements at its beginning represents
2⁻ⁿ and the sequence of all trues represents zero (2^{-∞}).
 *)
Record BiDist : Type :=
  {
    BD_agree :> nat → Prop;
    BD_decreases : ∀ n m, n ≤ m → BD_agree m → BD_agree n
  }
.

Arguments BD_agree _ _ : assert.
Arguments BD_decreases _ _ _ _ _ : assert.

Local Hint Resolve BD_decreases.

(** Two bisected distances are equal if they are equal as sequences. *)
Theorem BiDist_eq_simpl (d d' : BiDist) : BD_agree d = BD_agree d' → d = d'.
Proof.
  intros H.
  destruct d; destruct d'; cbn in *.
  ElimEq.
  PIR; trivial.
Qed.  

(** The less than equal relation. *)
Definition BD_LE (d d' : BiDist) : Prop :=
  ∀ n, d' n → d n
.

Notation "d ⊑ d'" := (BD_LE d d') : bisected_scope.

(** The less than relation. *)
Definition BD_LT (d d' : BiDist) : Prop :=
  d ⊑ d' ∧ d ≠ d'
.
                    
Notation "d ⊏ d'" := (BD_LT d d') : bisected_scope.

(** The bottom element (zero). *)
Definition BD_bot : BiDist :=
  {|
    BD_agree := fun _ => True;
    BD_decreases := fun _ _ _ _ => I
  |}
.

Notation "⊥" := BD_bot : bisected_scope.

(** ⊥ is the least element. *)
Theorem BD_bot_LE : ∀ d, ⊥ ⊑ d.
Proof.
  intros d n.
  cbn; tauto.  
Qed.

Local Hint Resolve BD_bot_LE.

(** The top element (one). *)
Definition BD_top : BiDist :=
  {|
    BD_agree := fun _ => False;
    BD_decreases := fun _ _ _ H => False_rect _ H
  |}
.

Notation "⊤" := BD_top : bisected_scope.

(** ⊤ is the greatest element. *)
Theorem BD_LE_top : ∀ d, d ⊑ ⊤.
Proof.
  intros d n.
  cbn; tauto.  
Qed.

Local Hint Resolve BD_LE_top.

(** Reflexivity of less than equal relation. *)
Theorem BD_LE_Refl : ∀ d, d ⊑ d.
Proof.
  intros d n; trivial.
Qed.  

(** Asymmetry of less than equal relation. *)
Theorem BD_LE_ASym : ∀ d d', d ⊑ d' → d' ⊑ d → d = d'.
Proof.
  intros d d' H1 H2.
  apply BiDist_eq_simpl.
  extensionality n.
  specialize (H1 n).
  specialize (H2 n).
  apply PropExt; intuition.
Qed.  

(** Transitivity of less than equal relation. *)
Theorem BD_LE_Trans : ∀ d d' d'', d ⊑ d' → d' ⊑ d'' → d ⊑ d''.
Proof.
  intros d d' d'' H1 H2 n.
  auto.
Qed.  
                                    
Local Obligation Tactic := idtac.

(** Half of the given distance. *)
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

(** Half of is a monotone function. *)
Theorem BD_Half_of_monotone : ∀ (d d' : BiDist), d ⊑ d' → (BD_Half_of d) ⊑ (BD_Half_of d').
Proof.
  intros d d' H1 n H2.
  destruct n; cbn; trivial.
  apply H1; trivial.
Qed.

(** Half of is a non-expansive function. *)
Theorem BD_Half_of_non_expansive : ∀ (d : BiDist), (BD_Half_of d) ⊑ d.
Proof.
  intros d n H.
  destruct n; cbn; trivial.
  apply BD_decreases with (m := S n); [do 2 constructor|trivial].
Qed.
  
(** Given a positive distance, half of it is positive. *)
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

(** If an element is positive then its half is strictly smaller than it. *)
Theorem BD_pos_half_strictly_less : ∀ d, ⊥ ⊏ d → BD_Half_of d ⊏ d.
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

(** Half of any distance is less than 1. *)
Theorem BD_half_of_less_than_1 : ∀ d, BD_Half_of d ⊏ ⊤.
Proof.
  intros d.
  split.
  + intros n H; cbn in H; tauto.
  + intros H.
    cbn_rewrite <- (equal_f (f_equal BD_agree H) 0).
    trivial.
Qed.  

(** nᵗʰ power of 1/2. *)
Definition BD_Half_pow (n : nat) := iterate BD_Half_of ⊤ n.

(** The nᵗʰ element of the sequence for the (n+1)ᵗʰ power of 1/2 is inhabitted. *)
Theorem BD_Half_pow_Sn_n (n : nat) : BD_Half_pow (S n) n.
Proof.
  induction n; cbn; trivial.
Qed.

(** The kᵗʰ element (k < n) of the sequence for the nᵗʰ power of 1/2 is inhabitted. *)
Theorem BD_Half_pow_lt (n k : nat) : k < n → BD_Half_pow n k.
Proof.
  intros H.
  induction H.
  apply BD_Half_pow_Sn_n.
  apply BD_decreases with (m := S k); [do 2 constructor | trivial].
Qed.

(** The kᵗʰ element (k < n) of the sequence for the nᵗʰ power of 1/2 is inhabitted. *)
Theorem BD_Half_pow_ge (n k : nat) : n ≤ k → ¬ (BD_Half_pow n k).
Proof.
  intros H.
  induction H.
  {
    induction n; tauto.
  }
  {
    intros H'.
    contradict IHle.
    apply BD_decreases with (m := S m); [do 2 constructor | trivial].
  }
Qed.

(** nᵗʰ power of 1/2 is positive. *)
Theorem BD_Half_pow_pos (n : nat) : ⊥ ⊏ (BD_Half_pow n).
Proof.
  split; trivial.
  intros H.
  apply (BD_Half_pow_ge n (S n)); [do 2 constructor |].
  match goal with
    [|- ?A] =>
    replace A with (⊥ (S n)); cbn; trivial
  end.
  apply (equal_f (f_equal BD_agree H) (S n)).
Qed.  

(** If an element is less than all finite powers 1/2 is the least element. *)
Theorem BD_approach_bot : ∀ d, (∀ d', ⊥ ⊏ d' → d ⊏ d') → d = ⊥.
Proof.
  intros d H1.
  apply BD_LE_ASym; [|apply BD_bot_LE].
  intros n H2.
  cut (d ⊏ BD_Half_pow (S n)); [intros [H31 H32]|].
  {
    apply H31.
    apply BD_Half_pow_Sn_n.
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

(** The least upper bound. *)
Program Definition BD_lub {X : Type} (f : X → BiDist) : BiDist :=
  {|
    BD_agree := fun n => ∀ x, f x n
  |}
.

Next Obligation.
Proof.
  cbn.
  intros d d' n m H1 H2.
  intuition eauto.
Qed.
  
Notation "⊔ᵍ y" := (BD_lub y) : bisected_scope.

(** The least upper bound is an upper bound. *)
Theorem BD_lub_ub : ∀ {X : Type} (f : X → BiDist),
    ∀ x, f x ⊑ ⊔ᵍ f.
Proof.
  intros f d d' n; cbn; intuition.  
Qed.

(** The lease upper bound is indeed the least among upper bounds. *)
Theorem BD_lub_lst : ∀ {X : Type} (f : X → BiDist) (d : BiDist),
    (∀ x, f x ⊑ d) → (⊔ᵍ f) ⊑ d.
Proof.
  intros X f d H1 n H2 x; apply H1; trivial.
Qed.

(** BiDist forms a partial order. *)
Definition BiDistPO : PartialOrder :=
  {|
    PO_Carrier := BiDist;
    PO_LE := BD_LE;
    PO_Refl := BD_LE_Refl;
    PO_ASym := BD_LE_ASym;
    PO_Trans := BD_LE_Trans
  |}.

(** BiDist as a partial order has least upper bounds. *)
Program Definition BD_LUB {X : Type} (f : X → BiDist) : (@LUB BiDistPO _ f)%order :=
  {|
    lub := ⊔ᵍ f;
    lub_ub := BD_lub_ub f;
    lub_lst := BD_lub_lst f
  |}.

Inductive BD_ApprType : BiDist → Type :=
| Appr_Half_Pow : ∀ n, BD_ApprType (BD_Half_pow n)
.

Definition BD_appr_pos := fun (x : BiDistPO) (H : BD_ApprType x) =>
        match H in (BD_ApprType b) return ⊥ ⊏ b with
        | Appr_Half_Pow n => BD_Half_pow_pos n
        end.

Require Import Coq.Logic.Classical_Pred_Type
        Coq.Logic.ChoiceFacts.

Local Axiom ConstructiveIndefiniteDescription_nat : ConstructiveIndefiniteDescription_on nat.

Theorem EveryBiDistAppr_helper (b : BiDist) :
  ⊥ ⊏ b → {n : nat | (BD_Half_pow n) ⊑ b}.
Proof.
  intros H1.
  apply ConstructiveIndefiniteDescription_nat.
  cut (∃ n, ¬ b n).
  {
    intros [n H2].
    exists n.
    intros m H3.
    destruct (le_gt_dec n m) as [H4|H4].
    + contradict H2.
      apply BD_decreases with (m := m); trivial.
    + apply BD_Half_pow_lt; trivial.
  }
  {
    apply not_all_ex_not.
    intros H2.
    apply H1.
    apply BD_LE_ASym;trivial.
    intros ? ?; trivial.
  }
Qed.

(** BiDist forms an MLattice. *)
Program Definition BiDistML : MLattice :=
  {|
    ML_PO := BiDistPO;
    ML_meets := @BD_LUB;
    ML_top := ⊤;
    ML_top_top := BD_LE_top;
    ML_bot := (⊥);
    ML_bot_bottom := BD_bot_LE;
    ML_appr_cond := BD_ApprType;
    ML_appr_top := Appr_Half_Pow 0;
    ML_appr_pos := BD_appr_pos;
    ML_appr_dominate_pos := _;
    ML_bottom_dichotomy :=
      inl
        (
          fun (x : BiDistPO) (H : BD_ApprType x) =>
            existT2
              (fun y : BiDistPO => BD_ApprType y)
              (fun y : BiDistPO => (⊥ ⊏ y) ∧ (y ⊏ x)%order)
              (BD_Half_of x)
              (
                match H in (BD_ApprType b) return (BD_ApprType (BD_Half_of b)) with
                | Appr_Half_Pow n => Appr_Half_Pow (S n)
                end
              )
              (conj (BD_pos_half_pos x (BD_appr_pos x H))
                    (BD_pos_half_strictly_less x (BD_appr_pos x H)))
        );
    ML_all_approximatable :=
      fun x H =>
        existT2
          _
          _
          (BD_Half_pow (proj1_sig (EveryBiDistAppr_helper x H)))
          (proj2_sig (EveryBiDistAppr_helper x H))
          (Appr_Half_Pow _)
  |}.

Next Obligation.
Proof.
  intros x H1.
  apply BD_LE_ASym; trivial.
  intros n _.
  specialize (H1 _ (Appr_Half_Pow (S n))).
  apply H1.
  apply BD_Half_pow_Sn_n.
Qed.
  
(** Powers of 1/2 are strictly decreasing *)
Theorem BD_Half_pow_strict_decreasing (n k : nat) : k < n → BD_Half_pow n ⊏ BD_Half_pow k.
Proof.
  intros H.
  induction H.
  apply BD_pos_half_strictly_less; apply BD_Half_pow_pos.
  eapply (@LE_LT_Trans BiDistPO); [|apply IHle].
  apply BD_pos_half_strictly_less; apply BD_Half_pow_pos.
Qed.

(** half_of forms a contraction rate! *)
Program Definition Half_ContrRate : ContrRate BiDistML :=
  {|
    CR_fun := BD_Half_of;
    CR_monotone := BD_Half_of_monotone;
    CR_non_expansive := BD_Half_of_non_expansive;
    CR_contracts := BD_pos_half_strictly_less;
    CR_rate_indicator := _
  |}.

Next Obligation.
Proof.
  intros ε ε'.
  destruct ε as [ε [n]].
  destruct ε' as [ε' [n']].
  cbn.
  exists (S (n - n')).
  unfold BD_Half_pow.
  rewrite iterate_after_iterate.
  apply BD_Half_pow_strict_decreasing.
  omega.
Qed.
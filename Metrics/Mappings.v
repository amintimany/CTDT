Require Import Essentials.Notations Essentials.Definitions.
Require Import Metrics.UltraMetric.
Require Import Metrics.Limit.

Local Obligation Tactic := idtac.

Local Open Scope order_scope.
Local Open Scope lattice_scope.

Section Mappings.
  Context {L : CompleteLattice} (U U' : UltraMetric L).
  
  (** A non-expansive function is one that does not increase distance.
Here, as ultrametric spaces can have different measures, we need a
mapping from the measure of the codomain of the function to the
measure of the domain of the function.
   *)
  Record NonExpansive : Type :=
    {
      NE_fun :> U → U';
      NE_non_expansive :
        ∀ x y, (∂(NE_fun x, NE_fun y) ⊑ ∂(x, y))%order%metric
    }.

  (**
A mechanism to indicate contraction rate of a contractive mapping.
   *)
  Record ContrRate (L : CompleteLattice) : Type :=
    {
      CR_fun :> L → L;
      CR_monotone : ∀ x y, x ⊑ y → CR_fun x ⊑ CR_fun y;
      CR_non_expansive : ∀ x, CR_fun x ⊑ x;
      CR_contracts : ∀ x, ⊥ ⊏ x → CR_fun x ⊏ x;
      CR_rate_indicator :
        ∀ (ε ε' : L), ⊥ ⊏ ε → ∃ n, (iterate CR_fun ε' n) ⊑ ε
    }.

  (** A contractive function is one that does decreases distance.
Here, as ultrametric spaces can have different measures, we need a
mapping from the measure of the codomain of the function to the
measure of the domain of the function.

We also require a contraction rate.
   *)
  Record Contractive {L : CompleteLattice} (U U' : UltraMetric L) : Type :=
    {
      CN_fun :> U → U';
      CN_ContrRate : ContrRate L;
      CN_contractive :
        ∀ x y, (∂(CN_fun x, CN_fun y) ⊑ CN_ContrRate (∂(x, y)))%order%metric
    }.

End Mappings.

Arguments NE_fun {_ _ _} _ _.
Arguments NE_non_expansive {_ _ _} _ _ _.
Arguments CR_fun {_} _ _.
Arguments CR_monotone {_} _ _ _ _.
Arguments CR_non_expansive {_} _ _.
Arguments CR_contracts {_} _ _ _.
Arguments CR_rate_indicator {_} _ _ _ _.
Arguments CN_fun {_ _ _} _ _.
Arguments CN_ContrRate {_ _ _} _.
Arguments CN_contractive {_ _ _} _ _ _.

Notation "'ρ' f" := (CN_ContrRate f) : metric_scope.

Section Contr_Comp.
  Context {L : CompleteLattice}
          {U U' U'' : UltraMetric L}
  .
        
  (** Composition of non-expansive function on the right with a contractive function is
contractive. *)
  Program Definition Contr_NonExp_Contr
          (f : NonExpansive U U')
          (g : Contractive U' U'')
    :
      Contractive U U'' :=
    {|
      CN_fun := fun x => (g (f x));
      CN_ContrRate := (ρ g)%metric
    |}.

  Next Obligation.
  Proof.
    intros f g x y.
    cbn.
    eapply PO_Trans; [apply CN_contractive |].
    apply CR_monotone.
    apply NE_non_expansive.
  Qed.


  (** Composition of non-expansive function on the left with a contractive function is
contractive. *)
  Program Definition NonExp_Contr_Contr
          (f : Contractive U U')
          (g : NonExpansive U' U'')
    :
      Contractive U U'' :=
    {|
      CN_fun := fun x => (g (f x));
      CN_ContrRate := (ρ f)%metric
    |}.

  Next Obligation.
  Proof.
    intros f g x y.
    cbn.
    eapply PO_Trans; [|apply CN_contractive].
    apply NE_non_expansive.
  Qed.

End Contr_Comp.

(** Every contractive function is continuous. *)
Section Contractive_Continuous.
  Context {L : CompleteLattice}
          {U : UltraMetric L}
          (Seq : Sequence U)
          (lm : Limit Seq)
          {U' : UltraMetric L}
          (f : Contractive U U')
  .

  Program Definition Contractive_Continuous : Limit (fun n => f (Seq n)) :=
    {|
      Lim := f lm
    |}.

  Next Obligation.
  Proof.
    intros ε H1.
    destruct (Lim_limit lm ε H1) as [N H2].
    exists N.
    intros n H3.
    eapply LE_LT_Trans; [apply CN_contractive|].
    eapply LE_LT_Trans; [apply CR_non_expansive|].
    apply H2; trivial.
  Qed.

End Contractive_Continuous.

(** Every non-expansive function is continuous. *)
Section NonExpansive_Continuous.
  Context {L : CompleteLattice}
          {U : UltraMetric L}
          (Seq : Sequence U)
          (lm : Limit Seq)
          {U' : UltraMetric L}
          (f : NonExpansive U U')
  .

  Program Definition NonExpansive_Continuous : Limit (fun n => f (Seq n)) :=
    {|
      Lim := f lm
    |}.

  Next Obligation.
  Proof.
    intros ε H1.
    destruct (Lim_limit lm ε H1) as [N H2].
    exists N.
    intros n H3.
    eapply LE_LT_Trans; [apply NE_non_expansive|].
    apply H2; trivial.
  Qed.

End NonExpansive_Continuous.

(** Iterating a contractive function contracts the distance at least according to iterated ρ (ContrRate). *)
Section iterate_Contractive_LE.
  Context {L : CompleteLattice}
          {U : UltraMetric L}
          (f : Contractive U U)
          (x y : U)
  .

  Theorem iterate_Contractive_LE :
    ∀ n, (∂(iterate f x n, iterate f y n) ⊑ iterate (ρ f)%metric (∂(x, y)) n)%metric.
  Proof.
    induction n; cbn; trivial.
    eapply PO_Trans; [apply CN_contractive|].
    apply CR_monotone; trivial.
  Qed.

End iterate_Contractive_LE.

(** Iterating a contraction rate contracts more the more it is applied. *)
Section iterate_ContrRate_LE.
  Context {L : CompleteLattice}
          (f : ContrRate L)
          (x : L)
  .

  Theorem iterate_ContrRate_LE :
    ∀ n m, n ≤ m → iterate f x m ⊑ iterate f x n.
  Proof.
    intros n m H.
    induction H; cbn; trivial.
    eapply PO_Trans; [apply CR_non_expansive|]; trivial.
  Qed.

End iterate_ContrRate_LE.
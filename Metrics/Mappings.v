Require Import Essentials.Notations Essentials.Definitions.
Require Import Metrics.UltraMetric.
Require Import Metrics.Limit.

Local Obligation Tactic := idtac.

Local Open Scope order_scope.
Local Open Scope lattice_scope.

Section Mappings.
  Context {L : Complete_Lattice} (U U' : UltraMetric L).
  
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
  Record ContrRate (L : Complete_Lattice) : Type :=
    {
      CR_fun :> L → L;
      CR_monotone : ∀ x y, x ⊑ y → CR_fun x ⊑ CR_fun y;
      CR_contracts : ∀ x, CR_fun x ⊏ x;
      CR_rate_indicator :
        ∀ (ε ε' : L), ⊥ ⊏ ε → ∃ n, (iterate CR_fun ε' n) ⊑ ε
    }.

  (** A contractive function is one that does decreases distance.
Here, as ultrametric spaces can have different measures, we need a
mapping from the measure of the codomain of the function to the
measure of the domain of the function.

We also require a contraction rate.
   *)
  Record Contractive {L : Complete_Lattice} (U U' : UltraMetric L) : Type :=
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
Arguments CR_contracts {_} _ _.
Arguments CR_rate_indicator {_} _ _ _ _.
Arguments CN_fun {_ _ _} _ _.
Arguments CN_ContrRate {_ _ _} _.
Arguments CN_contractive {_ _ _} _ _ _.

Section Contr_Comp.
  Context {L : Complete_Lattice}
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
      CN_ContrRate := CN_ContrRate g
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
      CN_ContrRate := CN_ContrRate f
    |}.

  Next Obligation.
  Proof.
    intros f g x y.
    cbn.
    eapply PO_Trans; [|apply CN_contractive].
    apply NE_non_expansive.
  Qed.

End Contr_Comp.

Section Contractive_Continuous.
  Context {L : Complete_Lattice}
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
    eapply PO_Trans; [|apply (H2 n)]; trivial.
    eapply PO_Trans; [apply CN_contractive|].
    apply CR_contracts.
  Qed.

End Contractive_Continuous.
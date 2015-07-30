Require Export Lattice.PartialOrder Lattice.MLattice.

Local Open Scope lattice_scope.

(** An ultra metric space is a metric space where triangular inequality:
     ∀ x y, ∂(x, z) ≤ ∂(x, y) + ∂(y, z)
is replaced with ultrametric inequality:
     ∀ x y, ∂(x, z) ≤ max{∂(x, y), ∂(y, z)}
*)
Record UltraMetric (L : MLattice) : Type :=
  {
    UM_Carrier :> Type;
    UM_distance : UM_Carrier → UM_Carrier → L where "∂( x , y )" := (UM_distance x y);
    UM_dist_sym : ∀ x y, ∂(x, y) = ∂(y, x);
    UM_eq_zero_dist :
      ∀ x y, x = y → (∂(x, y) = ⊥);
    UM_zero_dist_eq :
      ∀ x y, (∂(x, y) = ⊥) → x = y;
    UM_ineq : ∀ x z y, (∂(x, z) ⊑ (∂(x, y) ⊔ ∂(y, z))%lattice)%order
  }.

Arguments UM_Carrier {_} _ : assert.
Arguments UM_distance {_ _} _ _.

Notation "∂( x , y )" := (UM_distance x y) : metric_scope.

(** A sequence is a function from natural numbers to the metric space. *)
Definition Sequence {L : MLattice} (U : UltraMetric L) := nat → U.
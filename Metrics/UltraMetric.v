Require Export Lattice.PartialOrder Lattice.MLattice.

Local Open Scope lattice_scope.

(** An ultra metric space is a metric space where triangular inequality:
     ∀ x y, δ(x, z) ≤ δ(x, y) + δ(y, z)
is replaced with ultrametric inequality:
     ∀ x y, δ(x, z) ≤ max{δ(x, y), δ(y, z)}
*)
Record UltraMetric (L : MLattice) : Type :=
  {
    UM_Carrier :> Type;
    UM_distance : UM_Carrier → UM_Carrier → L where "δ( x , y )" := (UM_distance x y);
    UM_dist_sym : ∀ x y, δ(x, y) = δ(y, x);
    UM_eq_zero_dist :
      ∀ x, (δ(x, x) = ⊥);
    UM_zero_dist_eq :
      ∀ x y, (δ(x, y) = ⊥) → x = y;
    UM_ineq : ∀ x z y, (δ(x, z) ⊑ (δ(x, y) ⊔ δ(y, z))%lattice)%order
  }.

Arguments UM_Carrier {_} _ : assert.
Arguments UM_distance {_ _} _ _.

Notation "δ( x , y )" := (UM_distance x y) : metric_scope.

(** A sequence is a function from natural numbers to the metric space. *)
Definition Sequence {L : MLattice} (U : UltraMetric L) := nat → U.

Identity Coercion Sq : Sequence >-> Funclass.
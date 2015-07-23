Require Import Lattice.Lattice.

Local Open Scope lattice_scope.

(** An ultra metric space is a metric space where triangular inequality:
     ∀ x y, ∂(x, z) ≤ ∂(x, y) + ∂(y, z)
is replaced with ultrametric inequality:
     ∀ x y, ∂(x, z) ≤ max{∂(x, y), ∂(y, z)}
*)
Record UltraMetric : Type :=
  {
    UM_Carrier :> Type;
    UM_Measure : Complete_Lattice;
    UM_distance : UM_Carrier → UM_Carrier → UM_Measure where "∂( x , y )" := (UM_distance x y);
    UM_dist_sym : ∀ x y, ∂(x, y) = ∂(y, x);
    UM_eq_zero_dist :
      ∀ x y, x = y → (∂(x, y) = ⊥);
    UM_zero_dist_eq :
      ∀ x y, (∂(x, y) = ⊥) → x = y;
    UM_ineq : ∀ x z y, ∂(x, z) = ∂(x, y) ⊔ ∂(y, z)
  }.

Arguments UM_Carrier _ : assert.
Arguments UM_Measure _ : assert.
Arguments UM_distance {_} _ _.

Notation "∂( x , y )" := (UM_distance x y) : metric_scope.

Notation "'μ' x" := (UM_Measure x) : metric_scope.

(** A sequence is a function from natural numbers to the metric space. *)
Definition Sequence (U : UltraMetric) := nat → U.

(** A non-expansive function is one that does not increase distance.
Here, as ultrametric spaces can have different measures, we need a
mapping from the measure of the codomain of the function to the
measure of the domain of the function.
 *)
Record NonExpansive (U U' : UltraMetric) : Type :=
  {
    NE_fun :> U → U';
    NE_Measure_conv : (Monotone (μ U') (μ U))%metric;
    NE_non_expansive :
      ∀ x y, (NE_Measure_conv (∂(NE_fun x, NE_fun y)) ⊑ ∂(x, y))%order%metric
  }.

(** A contractive function is one that does decreases distance.
Here, as ultrametric spaces can have different measures, we need a
mapping from the measure of the codomain of the function to the
measure of the domain of the function.
 *)
Record Contractive (U U' : UltraMetric) : Type :=
  {
    CN_fun :> U → U';
    CN_Measure_conv : (Monotone (μ U') (μ U))%metric;
    CN_non_expansive :
      ∀ x y, (CN_Measure_conv (∂(CN_fun x, CN_fun y)) ⊏ ∂(x, y))%order%metric
  }.
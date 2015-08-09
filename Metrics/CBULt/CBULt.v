Require Import Essentials.Notations.
Require Import Lattice.MLattice Metrics.UltraMetric
        Metrics.Mappings Metrics.Complete_UltraMetric.
Require Import Categories.Category.Category.

Section CBULt.
  Context (L : MLattice).
  
  Definition CBULt :=
    {|
      Obj := Complete_UltraMetric L;
      Hom := NonExpansive;
      compose := @NonExp_compose _;
      assoc := @NonExp_compose_assoc _;
      assoc_sym := fun _ _ _ _ _ _ _ => eq_sym (@NonExp_compose_assoc _ _ _ _ _ _ _ _);
      id := NonExp_id;
      id_unit_left := @NonExp_id_unit_left _;
      id_unit_right := @NonExp_id_unit_right _
    |}
  .
End CBULt.
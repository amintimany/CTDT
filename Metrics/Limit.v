Require Import Metrics.UltraMetric.
Require Import Lattice.Lattice.

(** Limit of a sequence in an ultra metric space. *)
Section Limit.
  Context {U : UltraMetric} (Seq : Sequence U).

  Local Open Scope order_scope.
  Local Open Scope lattice_scope.
  Local Open Scope metric_scope.
  
  Record Limit : Type :=
    {
      Lim :> U;
      Lim_limit :
        ∀ (epsilon : μ U),
          ⊥ ⊏ epsilon →
          ∃ (N : nat), ∀ (n : nat),
              ∂(Seq n, Lim) ⊑ epsilon
    }.

End Limit.
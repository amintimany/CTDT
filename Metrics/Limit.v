Require Import Essentials.Notations.
Require Import Metrics.UltraMetric.
Require Import Lattice.CompleteLattice.

(** Limit of a sequence in an ultra metric space. *)
Section Limit.
  Context {L : CompleteLattice} {U : UltraMetric L} (Seq : Sequence U).

  Local Open Scope order_scope.
  Local Open Scope lattice_scope.
  Local Open Scope metric_scope.
  
  Record Limit : Type :=
    {
      Lim :> U;
      Lim_limit :
        ∀ (epsilon : L),
          ⊥ ⊏ epsilon →
          ∃ (N : nat), ∀ (n : nat), N ≤ n →
              ∂(Seq n, Lim) ⊑ epsilon
    }.

End Limit.

Arguments Lim {_ _ _} _.
Arguments Lim_limit {_ _ _} _ _ _.
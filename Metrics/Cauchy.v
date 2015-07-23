Require Import Essentials.Notations.
Require Import Lattice.CompleteLattice.
Require Import Metrics.UltraMetric.

Section Cauchy_Sequence.
  Context {L : CompleteLattice} (U : UltraMetric L).

  Local Open Scope order_scope.
  Local Open Scope lattice_scope.
  Local Open Scope metric_scope.

  (** Wikipedia:
In mathematics, a Cauchy sequence (French pronunciation: ​[koʃi]; English pronunciation:
/ˈkoʊʃiː/ koh-shee), named after Augustin-Louis Cauchy, is a sequence whose elements become
arbitrarily close to each other as the sequence progresses.[1] More precisely, given any small
positive distance, all but a finite number of elements of the sequence are less than that given
distance from each other.
  *)
  Record Cauchy_Sequence : Type :=
    {
      CHS_seq :> Sequence U;
      CHS_cauchy :
        ∀ (epsilon : L),
          ⊥ ⊏ epsilon →
          ∃ (N : nat), ∀ (n m : nat),
              N <= n → N ≤ m → (∂(CHS_seq n, CHS_seq m)) ⊑ epsilon
    }.

End Cauchy_Sequence.
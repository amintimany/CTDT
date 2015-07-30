Require Import Coq.Arith.Compare_dec.
Require Import Essentials.Notations.
Require Import Metrics.UltraMetric.
Require Import Coq.omega.Omega.

Section Cauchy_Sequence.
  Context {L : MLattice} (U : UltraMetric L).

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
        ∀ (ε : L),
          ⊥ ⊏ ε →
          ∃ (N : nat), ∀ (n m : nat),
              N <= n → N ≤ m → (∂(CHS_seq n, CHS_seq m)) ⊑ ε
    }.

  (** An alternative condition for cauchy sequences. *)
  Theorem Cauchy_condition_simpl (seq : Sequence U) (ε : L) (N : nat) :
    (∀ n, N <= n → (∂(seq n, seq (S n))) ⊑ ε) →
    (∀ n m, N <= n → N ≤ m → (∂(seq n, seq m)) ⊑ ε).
  Proof.
    intros H.
    match goal with
      [|- ∀ n m, ?H1 → ?H2 → ?G] =>
      cut (∀ n m, H1 → H2 → n ≤ m → G)
    end.
    {
      intros Hle n m H1 H2.
      destruct (le_ge_dec n m) as [Hlg|Hlg];
        [|rewrite UM_dist_sym]; eapply Hle; eauto.
    }
    {
      intros n m H1 H2 H3.
      induction H3.
      {
        rewrite UM_eq_zero_dist; auto.
      }
      {
        apply le_lt_or_eq in H2; destruct H2 as [H2|H2]; [|omega].
        apply lt_n_Sm_le in H2.
        eapply PO_Trans; [eapply UM_ineq|].
        apply lub_lst.
        intros x Hx.
        destruct Hx.
        apply IHle; trivial.
        apply H; trivial.
      }
    }
  Qed.
    
End Cauchy_Sequence.
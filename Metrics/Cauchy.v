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
        ∀ (ε : (ApprType L)),
          {N : nat | ∀ (n m : nat),
              N <= n → N ≤ m → (∂(CHS_seq n, CHS_seq m)) ⊏ (projT1 ε)}
    }.

  Local Ltac simplify_1 :=
    match goal with
      [|- ∀ n m, ?H1 → ?H2 → ?G] =>
      cut (∀ n m, H1 → H2 → n ≤ m → G)
    end;
    [intros Hle n m H1 H2;
      destruct (le_ge_dec n m) as [Hlg|Hlg];
      [|rewrite UM_dist_sym]; eapply Hle; eauto|].
  
  (** An alternative condition for cauchy sequences. *)
  Theorem Cauchy_condition_simpl (seq : Sequence U) :
    (∀ (ε : (ApprType L)), {N : nat | ∀ n, N ≤ n → (∂(seq n, seq (S n))) ⊏ (projT1 ε)}) →
    (∀ (ε : (ApprType L)), {N : nat | ∀ n m, N <= n → N ≤ m → (∂(seq n, seq m)) ⊏ (projT1 ε)}).
  Proof.
    intros H ε.
    destruct (ML_bottom_dichotomy L) as [dicht|dicht].
    {
      destruct (dicht _ (projT2 ε)) as [y Hd1 [Hd2 Hd3]].
      destruct (H (existT _ _ Hd1)) as [N HN].
      exists N.
      simplify_1.
      {
        intros n m H1 H2 H3.
        eapply LE_LT_Trans; [|apply Hd3].
        induction H3.
        {
          rewrite UM_eq_zero_dist; trivial.
        }
        {
          apply le_lt_or_eq in H2; destruct H2 as [H2|H2]; [|omega].
          apply lt_n_Sm_le in H2.
          eapply PO_Trans; [eapply UM_ineq|].
          apply lub_lst.
          intros [|].
          apply IHle; trivial.
          apply HN; trivial.
        }
      }
    }
    {
      destruct dicht as [ab Hd1 Hd2].
      destruct (H (existT _ _ Hd1)) as [N HN].
      exists N.
      simplify_1.
      {
        intros n m H1 H2 H3.
        induction H3.
        {
          rewrite UM_eq_zero_dist; trivial.
          apply ML_appr_pos.
          exact (projT2 ε).
        }
        {
          apply le_lt_or_eq in H2; destruct H2 as [H2|H2]; [|omega].
          apply lt_n_Sm_le in H2.
          eapply LE_LT_Trans; [eapply (UM_ineq _ _ _ _ (seq m))|].
          rewrite (Hd2 _ (HN _ H2)).
          rewrite lub_bot.
          apply IHle; trivial.
        }
      }
    }
  Qed.
    
End Cauchy_Sequence.
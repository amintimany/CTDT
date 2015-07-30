Require Import Coq.Program.Tactics.
Require Import Essentials.Notations Essentials.Definitions.
Require Import Metrics.UltraMetric Metrics.Cauchy Metrics.Mappings
        Metrics.Limit Metrics.Complete_UltraMetric
.

Section Banach.
  Context {L : MLattice}
          (CU : Complete_UltraMetric L)
          (x : CU)
          (f : Contractive CU CU).

  Local Obligation Tactic := idtac.
  
  Program Definition iterate_f_cauchy : Cauchy_Sequence CU :=
    {|
      CHS_seq := iterate f x
    |}.

  Next Obligation.
  Proof.
    apply Cauchy_condition_simpl; trivial.
    intros ε H1.
    destruct (CR_rate_indicator (CN_ContrRate f) ε (∂(x, f x))%metric H1) as [N H2].
    exists N.
    intros n H3.
    rewrite iterate_Sn_n.
    eapply LE_LT_Trans; [apply iterate_Contractive_LE|].
    eapply LE_LT_Trans; [|apply H2].
    apply iterate_ContrRate_LE; trivial.
  Qed.

  Theorem Banach_is_FixedPoint : is_FixedPoint f (CUM_complete _ iterate_f_cauchy).
  Proof.
    unfold is_FixedPoint.
    match goal with
      [|- ?A = ?B] =>
      change A with (Lim (Contractive_Continuous _ (CUM_complete _ iterate_f_cauchy) f))
    end.
    change (fun n : nat => f (CHS_seq _ iterate_f_cauchy n))
    with (fun n : nat => (CHS_seq _ iterate_f_cauchy (S n))).
    symmetry.
    apply Limit_of_SubSeq.
  Qed.

  Local Open Scope order_scope.
  Local Open Scope metric_scope.
  Local Open Scope lattice_scope.

  Theorem Banach_unique : ∀ l l', is_FixedPoint f l → is_FixedPoint f l' → l = l'.
  Proof.
    intros l l' H1 H2.
    destruct (ML_bottom_dichotomy L) as [dicht|dicht].
    {
      apply UM_zero_dist_eq.
      apply ML_strict_bot.
      intros y H3.
      destruct (dicht _ H3) as [z [Hd1 Hd2]].
      destruct (CR_rate_indicator (ρ f)%metric z (∂( l, l')) Hd1) as [n H4].
      rewrite <- (is_FixedPoint_iterate _ _ H1 n).
      rewrite <- (is_FixedPoint_iterate _ _ H2 n).
      eapply LE_LT_Trans; [apply iterate_Contractive_LE|].
      eapply LE_LT_Trans; [apply H4|].
      trivial.
    }
    {
      destruct dicht as [ab [Hd1 Hd2]].
      destruct (CR_rate_indicator (ρ f)%metric ab (∂( l, l')) Hd1) as [n H4].
      apply UM_zero_dist_eq.
      apply Hd2.
      rewrite <- (is_FixedPoint_iterate _ _ H1 n).
      rewrite <- (is_FixedPoint_iterate _ _ H2 n).
      eapply LE_LT_Trans; [apply iterate_Contractive_LE|trivial].
    }
  Qed.

End Banach.
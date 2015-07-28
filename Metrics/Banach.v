Require Import Coq.Program.Tactics.
Require Import Essentials.Notations Essentials.Definitions.
Require Import Metrics.UltraMetric Metrics.Cauchy Metrics.Mappings
        Metrics.Limit Metrics.Complete_UltraMetric
.

Section Banach.
  Context {L : CompleteLattice}
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
    intros ε H1.
    destruct (CR_rate_indicator (CN_ContrRate f) ε (∂(x, f x))%metric H1) as [N H2].
    exists N.
    apply Cauchy_condition_simpl.
    intros n H3.
    rewrite iterate_Sn_n.
    eapply PO_Trans; [apply iterate_Contractive_LE|].
    eapply PO_Trans; [|apply H2].
    apply iterate_ContrRate_LE; trivial.
  Qed.

  Theorem Banach_is_FixedPoint : is_FixedPoint f (CUM_complete _ iterate_f_cauchy).
  Proof.
    unfold is_FixedPoint.
    match goal with
      [|- ?A = ?B] =>
      change A with (Lim (Contractive_Continuous _ (CUM_complete _ iterate_f_cauchy) f))
    end.
    Set Printing All.
    idtac.
    
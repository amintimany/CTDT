Require Import Essentials.Notations.
Require Import Metrics.UltraMetric Metrics.Limit Metrics.Cauchy.

(** A complete ultra metric space is an ultra metric space that is cauchy complete, i.e.,
all cauchy sequences have a limit.
 *)
Record Complete_UltraMetric (L : Complete_Lattice) : Type :=
  {
    CUM_UM :> UltraMetric L;
    CMU_complete :
      ∀ (chs : Cauchy_Sequence CUM_UM), Limit chs
  }.
Require Import Essentials.Notations.
Require Export Metrics.UltraMetric Metrics.Limit Metrics.Cauchy.

(** A complete ultra metric space is an ultra metric space that is cauchy complete, i.e.,
all cauchy sequences have a limit.
 *)
Record Complete_UltraMetric (L : MLattice) : Type :=
  {
    CUM_UM :> UltraMetric L;
    CUM_complete :
      ∀ (chs : Cauchy_Sequence CUM_UM), Limit chs
  }.

Arguments CUM_UM {_} _.
Arguments CUM_complete {_} _ _.
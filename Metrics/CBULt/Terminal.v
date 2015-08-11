Require Import Essentials.Notations Essentials.Arith Essentials.Types.
Require Import Lattice.MLattice Metrics.UltraMetric
        Metrics.Cauchy Metrics.Limit
        Metrics.Mappings Metrics.Complete_UltraMetric.
Require Import Categories.Category.Category
        Categories.Basic_Cons.Terminal.

Require Import Metrics.CBULt.CBULt.

Section CBULt_Terminal.
  Context {L : MLattice}.

  Program Definition Terminal_UM : UltraMetric L :=
    {|
      UM_Carrier := Unit;
      UM_distance := fun x y => (⊥)%lattice
    |}.

  Next Obligation.
  Proof.
    apply Unit_Singleton.
  Qed.

  Program Definition Terminal_CUM : Complete_UltraMetric L :=
    {|
      CUM_UM := Terminal_UM;
      CUM_complete :=
        fun chs =>
          {|
            Lim := TT
          |}
    |}.

  Next Obligation.
  Proof.
    exists 0.
    intros n H.
    apply ML_appr_pos.
    apply (projT2 ε).
  Qed.    

  Local Hint Extern 1 => apply NonExpansive_eq_simplify.
  Local Hint Extern 1 => apply Unit_Singleton.
  
  Program Instance CBULt_Terminal : Terminal (CBULt L) :=
    {|
      terminal := Terminal_CUM;
      t_morph := fun A => {|NE_fun := fun _ => TT|}
    |}.

End CBULt_Terminal.
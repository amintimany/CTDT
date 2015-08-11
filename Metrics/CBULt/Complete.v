Require Import Lattice.MLattice.
Require Import Metrics.CBULt.CBULt Metrics.CBULt.GenProd Metrics.CBULt.Equalizer.
Require Import Categories.Limits.Limit Categories.Limits.GenProd_Eq_Limits.

Section Complete.
  Context (L : MLattice).
  
  Instance CBULt_Complete :
  Complete (CBULt L) := @GenProd_Eq_Complete (CBULt L) (@CBULt_GenProd L) (@CBULt_Equalizer L).

End Complete.
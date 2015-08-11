Require Import Essentials.Notations Essentials.Arith.
Require Import Lattice.MLattice.
Require Import Categories.Basic_Cons.CCC.

Require Import
        Metrics.CBULt.CBULt
        Metrics.CBULt.Terminal
        Metrics.CBULt.Product
        Metrics.CBULt.Exponential.

Program Instance CBULt_CCC (L : MLattice) : CCC (CBULt L) := {|CCC_term := @CBULt_Terminal L|}.
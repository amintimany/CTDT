Require Import
        Essentials.Facts_Tactics
        Essentials.Notations
        Essentials.Arith.
Require Import Lattice.MLattice Metrics.UltraMetric
        Metrics.Cauchy Metrics.Limit
        Metrics.Mappings Metrics.Complete_UltraMetric.
Require Import Categories.Category.Category
        Categories.Basic_Cons.Equalizer.

Require Import Metrics.CBULt.CBULt.


Section CBULt_Equalzier.
  Context (L : MLattice) {X Y : CBULt L} (f g : (X –≻ Y)%morphism).

  Program Definition Equalzier_UM : UltraMetric L :=
    {|
      UM_Carrier := {x : X | f x = g x};
      UM_distance := fun x y => (δ(proj1_sig x, proj1_sig y))%metric
    |}.

  Next Obligation.
  Proof.
    apply UM_dist_sym.
  Qed.

  Next Obligation.
  Proof.
    apply UM_eq_zero_dist.
  Qed.
  
  Next Obligation.
  Proof.
    match goal with
      [|- exist _ ?A _ = exist _ ?B _] =>
      destruct (UM_zero_dist_eq _ _ A B); auto
    end.
  Qed.    

  Next Obligation.
  Proof.  
    apply UM_ineq.
  Qed.

  Program Definition Separated_Cauchy (chs : Cauchy_Sequence Equalzier_UM)
    :
      Cauchy_Sequence X :=
    {|
      CHS_seq := fun n => proj1_sig (chs n)
    |}.

  Next Obligation.
  Proof.
    apply (CHS_cauchy _ chs).
  Qed.

  
    
  Program Definition Equalzier_CUM : Complete_UltraMetric L :=
    {|
      CUM_UM := Equalzier_UM;
      CUM_complete :=
        fun chs =>
          {|
            Lim := exist _ (CUM_complete X (Separated_Cauchy chs)) _
          |}
    |}.

  Next Obligation.
  Proof.
    match goal with
      [|- (NE_fun ?f) (Lim ?A) = (NE_fun ?g) (Lim ?A)] =>
      change (f (Lim A)) with (Lim (NonExpansive_Continuous _ A f));
        change (g (Lim A)) with (Lim (NonExpansive_Continuous _ A g))
    end.
    apply Eq_Seq_Eq_Limits.
    FunExt.
    apply (proj2_sig (chs _)).
  Qed.    

  Next Obligation.
  Proof.
    apply (Lim_limit (CUM_complete X (Separated_Cauchy chs))).
  Qed.      

  Local Hint Extern 1 => apply NonExpansive_eq_simplify.
  
  Program Definition CBULt_Equalizer : Equalizer f g :=
    {|
      equalizer := Equalzier_CUM;
      equalizer_morph := {|NE_fun := fun x => proj1_sig x|};
      equalizer_morph_ex :=
        fun A h H =>
          {|NE_fun := fun x => exist _ (h x) (equal_f (f_equal NE_fun H) x)|}
    |}.

  Next Obligation.
  Proof.
    apply NonExpansive_eq_simplify.
    extensionality x.
    apply (proj2_sig x).
  Qed.    

  Next Obligation.
  Proof.
    apply NE_non_expansive.
  Qed.

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros e' eqm H1 u u' H2 H3; cbn in *.
    rewrite <- H3 in H2; clear H3.
    apply NonExpansive_eq_simplify.
    extensionality x.
    apply sig_proof_irrelevance.
    apply (equal_f (f_equal NE_fun H2) x).
  Qed.
    
End CBULt_Equalzier.
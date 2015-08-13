Require Import
        Essentials.Types
        Essentials.Facts_Tactics
        Essentials.Notations
        Essentials.Arith.
Require Import Lattice.MLattice Metrics.UltraMetric
        Metrics.Cauchy Metrics.Limit
        Metrics.Mappings Metrics.Complete_UltraMetric.
Require Import
        Categories.Category.Category
        Categories.Basic_Cons.Exponential.

Require Import Metrics.CBULt.CBULt Metrics.CBULt.Product.


Section CBULt_Exp.
  Context {L : MLattice} (A B: CBULt L).

  Program Definition Exp_UM : UltraMetric L :=
    {|
      UM_Carrier := NonExpansive A B;
      UM_distance := fun f g => (⊔ᵍ (fun u => ∂(f u, g u)))%metric%lattice
    |}.

  Next Obligation.
  Proof.
    f_equal.
    + intros H; rewrite H; trivial.
    + FunExt.
      rewrite UM_dist_sym.
      trivial.
  Qed.

  Next Obligation.
  Proof.
    ElimEq.
    apply LE_Bottom_Bottom.
    apply lub_lst.
    intros u.
    rewrite UM_eq_zero_dist; trivial.
  Qed.

  Local Obligation Tactic := idtac.

  Next Obligation.
  Proof.
    cbn; intros u v H.
    apply NonExpansive_eq_simplify.
    extensionality w.
    apply UM_zero_dist_eq.
    apply LE_Bottom_Bottom.
    rewrite <- H.
    apply (lub_ub (fun w : _ => (∂( u w, v w))%metric)).
  Qed.    

  Next Obligation.
  Proof.  
    intros u v z; cbn.
    apply lub_lst; intros w.
    (eapply PO_Trans; [apply UM_ineq|]).
    apply lub_lst; intros [|].
    eapply PO_Trans; [|
                      (apply (lub_ub (fun u : bool => if u then _ else _) _ true))
                     ].
    apply (lub_ub (fun w : _ => (∂(u w, z w))%metric)).
    eapply PO_Trans; [|
                      (apply (lub_ub (fun u : bool => if u then _ else _) _ false))
                     ].
    apply (lub_ub (fun w : _ => (∂(z w, v w))%metric)).
  Qed.

  Program Definition Separated_Cauchy (chs : Cauchy_Sequence Exp_UM)
          (x : A) :
    Cauchy_Sequence B :=
    {|
      CHS_seq := fun n => chs n x
    |}.

  Next Obligation.
  Proof.
    intros CHS x ε.
    destruct (CHS_cauchy _ CHS ε) as [n H].
    exists n.
    intros k k' H1 H2.
    specialize (H k k' H1 H2).
    eapply LE_LT_Trans; [|apply H].
    apply (lub_ub (fun u : _ => (∂( CHS k u, CHS k' u))%metric)).
  Qed.

  (** We need classical logic facts to prove that the limit of separated 
cauchy sequences are indeed non-expansive. The reason is that we need
to know if the distance of the inputs is already zero.
If so, we prove that the distance of limits is also zero.
If the distance is not zero, then we can use the fact that
if two sequences have their distance bounded by a distance,
then their limits also have a distance bounded by that distance.
Note that this latter Lemma, uses ML_all_approximatable which is not
generally provable constractively. E.g., it is not constructively provable
for bisected spaces. *)
  Require Import Coq.Logic.Classical.
  
  Program Definition Separated_Cauchy_NonExp (chs : Cauchy_Sequence Exp_UM)
    : NonExpansive A B :=
    {|
      NE_fun := fun x => (CUM_complete B (Separated_Cauchy chs x))
    |}.

  Next Obligation.
  Proof.
    intros chs x y; cbn.
    destruct (classic (⊥ = (∂( x, y))%metric)%lattice) as [H|H].
    {
      rewrite <- H.
      replace y with x.
      rewrite UM_eq_zero_dist; trivial.
      apply UM_zero_dist_eq; auto.
    }
    {
      apply Distance_of_Limits.
      + split; trivial.
      + intros n.
        apply NE_non_expansive.
    }
  Qed.    
    
  Program Definition Exp_CUM : Complete_UltraMetric L :=
    {|
      CUM_UM := Exp_UM;
      CUM_complete :=
        fun chs =>
          {|
            Lim := Separated_Cauchy_NonExp chs
          |}
    |}.

  Next Obligation.
  Proof.
    intros chs ε.
    destruct (ML_bottom_dichotomy L) as [dict|dict].
    {
      destruct (dict _ (projT2 ε)) as [ε' Hd1 [Hd2 Hd3]].
      destruct (CHS_cauchy _ chs (existT _ _ Hd1)) as [N H].
      cut (∀ (x : A) (n : nat), N ≤ n → ((∂(chs n x, CUM_complete B (Separated_Cauchy chs x)))%metric ⊑ ε')%order).
      {
        intros H2.
        exists N.
        intros n H3.
        eapply LE_LT_Trans; [|apply Hd3].
        apply lub_lst.
        intros x.
        apply H2; trivial.
      }
      {
        intros x n H2.
        assert (H3 := proj2_sig (Lim_limit (CUM_complete B (Separated_Cauchy chs x)) (existT _ _ Hd1)) (max (proj1_sig
         (Lim_limit (CUM_complete B (Separated_Cauchy chs x))
            (existT (ML_appr_cond L) ε' Hd1))) n) (l_le_max _ _) ).
        eapply PO_Trans; [apply UM_ineq|].
        apply lub_lst.
        intros []; [|apply H3].
        eapply PO_Trans; [|apply H].
        + apply (lub_ub ((fun u : A => (∂( chs _ u, chs _ u))%metric))%lattice).
        + trivial.
        + etransitivity; [apply H2|apply r_le_max].
      }
    }      
    {      
      destruct dict as [ab Hd1 Hd2].      
      destruct (CHS_cauchy _ chs (existT _ _ Hd1)) as [N H].
      exists N.
      intros n H2.
      match goal with
        [|- (?A ⊏ _)%order] =>
        cutrewrite (A = ⊥%lattice); [apply ML_appr_pos; apply (projT2 ε)|]
      end.
      apply LE_Bottom_Bottom.
      apply lub_lst.
      intros x.
      assert (H3 := Hd2 _ (proj2_sig (Lim_limit (CUM_complete B (Separated_Cauchy chs x)) (existT _ _ Hd1)) (max (proj1_sig
         (Lim_limit (CUM_complete B (Separated_Cauchy chs x))
                    (existT (ML_appr_cond L) _ Hd1))) n) (l_le_max _ _)) ).      
        eapply PO_Trans; [apply UM_ineq|].
        apply lub_lst.
        intros []; [|rewrite <- H3; apply PO_Refl].
        match goal with
          [|- (?A ⊑ _)%order] =>
          cutrewrite (A = ⊥%lattice); [trivial|]
        end.
        apply Hd2.
        eapply LE_LT_Trans; [|apply H].
        + apply (lub_ub ((fun u : A => (∂( chs _ u, chs _ u))%metric))%lattice).
        + trivial.
        + etransitivity; [apply H2|apply r_le_max].
    }
  Qed.      

  Local Obligation Tactic := basic_simpl; auto.

  Local Hint Extern 1 => apply NonExpansive_eq_simplify.

  Program Definition CBULt_Exp : @Exponential (CBULt L) (CBULt_Has_Products _) A B :=
    {|
      exponential := Exp_CUM;
      eval := {|NE_fun := fun fx => ((fst fx) (snd fx))|};
      Exp_morph_ex := fun C h => {|NE_fun := fun z => {| NE_fun := fun x => h (z, x) |}|}
    |}.

  Next Obligation.
  Proof.
    eapply PO_Trans; [apply UM_ineq|].
    apply lub_lst; intros [].
    {
      eapply PO_Trans; [|apply (lub_ub (fun u : bool => if u then _ else _) _ true)].
      eapply PO_Trans; [|apply (lub_ub (fun u : A => ∂(_, _) )%metric)].
      apply PO_Refl.
    }
    {
      eapply PO_Trans; [apply NE_non_expansive|].
      eapply PO_Trans; [|apply (lub_ub (fun u : bool => if u then _ else _) _ false)]; trivial.
    }
  Qed.

  Next Obligation.
  Proof.
    eapply PO_Trans; [apply NE_non_expansive|].
    apply lub_lst; intros []; cbn; trivial.
    rewrite UM_eq_zero_dist; trivial.
  Qed.

  Next Obligation.
  Proof.
    apply lub_lst; intros w.
    eapply PO_Trans; [apply NE_non_expansive|].
    apply lub_lst; intros []; cbn; trivial.
    rewrite UM_eq_zero_dist; trivial.
  Qed.

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros z f u u' H1 H2.
    rewrite H2 in H1; clear H2.
    apply NonExpansive_eq_simplify.
    extensionality w.
    apply NonExpansive_eq_simplify.
    extensionality w'.
    symmetry.
    apply (f_equal (fun f : NonExpansive (product_UM z A) B => NE_fun f (w, w')) H1).
  Qed.

End CBULt_Exp.

Instance CBULt_Has_Exponentials (L : MLattice) : Has_Exponentials (CBULt L) := CBULt_Exp.
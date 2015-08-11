Require Import Essentials.Notations Essentials.Arith.
Require Import Lattice.MLattice Metrics.UltraMetric
        Metrics.Cauchy Metrics.Limit
        Metrics.Mappings Metrics.Complete_UltraMetric.
Require Import Categories.Category.Category
        Categories.Basic_Cons.Product.

Require Import Metrics.CBULt.CBULt.

Local Hint Extern 1 => apply (lub_ub (fun u : bool => if u then _ else _) _ true).
Local Hint Extern 1 => apply (lub_ub (fun u : bool => if u then _ else _) _ false).

Section CBULt_Product.
  Context {L : MLattice} (A B : CBULt L).

  Program Definition product_UM : UltraMetric L :=
    {|
      UM_Carrier := (UM_Carrier A) * (UM_Carrier B);
      UM_distance := fun x y => (∂(fst x, fst y) ⊔ ∂(snd x, snd y))%metric%lattice
    |}.

  Next Obligation.
  Proof.
    rewrite (UM_dist_sym _ A).
    rewrite (UM_dist_sym _ B).
    trivial.
  Qed.

  Next Obligation.
  Proof.
    do 2 rewrite UM_eq_zero_dist.
    apply LE_Bottom_Bottom.
    apply lub_lst.
    intros []; trivial.
  Qed.

  Next Obligation.
  Proof.
    match goal with
      [|- (?a, ?b) = (?c, ?d)] =>
      cutrewrite (a = c); [cutrewrite (b = d)|]; trivial
    end;
    match goal with
      [|- ?a = ?b] =>
      cut (∂(a, b) = ⊥%lattice)%metric;
        [
          intros H1; apply UM_zero_dist_eq; trivial |
          apply LE_Bottom_Bottom; rewrite <- H; auto
        ]
    end.
  Qed.    

  Next Obligation.
  Proof.  
    apply lub_lst; intros [];
    (eapply PO_Trans; [apply UM_ineq|]);
    apply lub_lst; intros [|];
    let tac a b :=
        (eapply PO_Trans; [|
                          (apply (lub_ub (fun u : bool => if u then _ else _) _ a))
                         ];
        apply (lub_ub (fun u : bool => if u then _ else _) _ b))
    in
    tac true true + tac true false + tac false true + tac false false
    .
  Qed.

  Local Obligation Tactic := idtac.

  Program Definition Separated_Cauchy_fst (chs : Cauchy_Sequence product_UM)
    :
      Cauchy_Sequence A :=
    {|
      CHS_seq := fun n => fst (chs n)
    |}.
  
  Next Obligation.
  Proof.
    intros CHS ε.
    destruct (CHS_cauchy _ CHS ε) as [n H].
    exists n.
    intros k k' H1 H2.
    specialize (H k k' H1 H2).
    eapply LE_LT_Trans; [|apply H]; auto.
  Qed.

  Program Definition Separated_Cauchy_snd (chs : Cauchy_Sequence product_UM)
    :
      Cauchy_Sequence B :=
    {|
      CHS_seq := fun n => snd (chs n)
    |}.

  Next Obligation.
  Proof.
    intros CHS ε.
    destruct (CHS_cauchy _ CHS ε) as [n H].
    exists n.
    intros k k' H1 H2.
    specialize (H k k' H1 H2).
    eapply LE_LT_Trans; [|apply H]; auto.
  Qed.
  
  Program Definition product_CUM : Complete_UltraMetric L :=
    {|
      CUM_UM := product_UM;
      CUM_complete :=
        fun chs =>
          {|
            Lim :=
              (CUM_complete A (Separated_Cauchy_fst chs),
               CUM_complete B (Separated_Cauchy_snd chs))
          |}
    |}.

  Next Obligation.
  Proof.
    intros chs ε.
    destruct (ML_bottom_dichotomy L) as [dict|dict].
    {
      destruct (dict _ (projT2 ε)) as [ε' Hd1 [Hd2 Hd3]].
      destruct (CHS_cauchy _ chs (existT _ _ Hd1)) as [N H].
      cut (∀ (n : nat),
              N ≤ n →
              ((∂(fst (chs n), CUM_complete A (Separated_Cauchy_fst chs)))%metric ⊑ ε')%order
              ∧
              ((∂(snd (chs n), CUM_complete B (Separated_Cauchy_snd chs)))%metric ⊑ ε')%order
          ).
      {
        intros H2.
        exists N.
        intros n H3.
        eapply LE_LT_Trans; [|apply Hd3].
        apply lub_lst.
        intros []; apply H2; trivial.
      }
      {
        intros n H2; split.
        {
          assert (H3 := proj2_sig (Lim_limit (CUM_complete A (Separated_Cauchy_fst chs)) (existT _ _ Hd1)) (max (proj1_sig
         (Lim_limit (CUM_complete A (Separated_Cauchy_fst chs))
            (existT (ML_appr_cond L) ε' Hd1))) n) (l_le_max _ _) ).
          eapply PO_Trans; [apply UM_ineq|].
          apply lub_lst.
          intros []; [|apply H3].
          eapply PO_Trans; [|apply H]; auto.
          etransitivity; [apply H2|apply r_le_max].
        }
        {
          assert (H3 :=
                    proj2_sig
                      (Lim_limit (CUM_complete B (Separated_Cauchy_snd chs)) (existT _ _ Hd1))
                      (max
                         (proj1_sig (Lim_limit
                                       (CUM_complete B (Separated_Cauchy_snd chs))
                                       (existT (ML_appr_cond L) ε' Hd1)
                                    )
                         )
                         n
                      )
                      (l_le_max _ _)
                 ).
          eapply PO_Trans; [apply UM_ineq|].
          apply lub_lst.
          intros []; [|apply H3].
          eapply PO_Trans; [|apply H]; auto.
          etransitivity; [apply H2|apply r_le_max].
        }
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
      intros [].
      {
        assert (H3 :=
                  Hd2
                    _
                    (proj2_sig
                       (Lim_limit (CUM_complete A (Separated_Cauchy_fst chs)) (existT _ _ Hd1))
                       (max
                          (proj1_sig (Lim_limit
                                        (CUM_complete A (Separated_Cauchy_fst chs))
                                        (existT (ML_appr_cond L) _ Hd1)
                                     )
                          )
                          n
                       )
                       (l_le_max _ _))
               ).
        eapply PO_Trans; [apply UM_ineq|].
        apply lub_lst.
        intros []; [|rewrite <- H3; apply PO_Refl].
        match goal with
          [|- (?A ⊑ _)%order] =>
          cutrewrite (A = ⊥%lattice); [trivial|]
        end.
        apply Hd2.
        eapply LE_LT_Trans; [|apply H]; auto.
        etransitivity; [apply H2|apply r_le_max].
      }
      {
        assert (H3 :=
                  Hd2
                    _
                    (proj2_sig
                       (Lim_limit (CUM_complete B (Separated_Cauchy_snd chs)) (existT _ _ Hd1))
                       (max
                          (proj1_sig (Lim_limit
                                        (CUM_complete B (Separated_Cauchy_snd chs))
                                        (existT (ML_appr_cond L) _ Hd1)
                                     )
                          )
                          n
                       )
                       (l_le_max _ _))
               ).
        eapply PO_Trans; [apply UM_ineq|].
        apply lub_lst.
        intros []; [|rewrite <- H3; apply PO_Refl].
        match goal with
          [|- (?A ⊑ _)%order] =>
          cutrewrite (A = ⊥%lattice); [trivial|]
        end.
        apply Hd2.
        eapply LE_LT_Trans; [|apply H]; auto.
        etransitivity; [apply H2|apply r_le_max].
      }
    }
  Qed.

  Local Obligation Tactic := basic_simpl; auto.

  Local Hint Extern 1 => apply NonExpansive_eq_simplify.
  
  Program Definition CBULt_Product : Product A B :=
    {|
      product := product_CUM;
      Pi_1 := {| NE_fun := fst |};
      Pi_2 := {| NE_fun := snd |};
      Prod_morph_ex := fun C f g => {| NE_fun := fun x => (f x, g x) |}
    |}.

  Next Obligation.
  Proof.  
    apply lub_lst; intros []; apply NE_non_expansive.
  Qed.    

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros p' r1 r2 f g H1 H2 H3 H4.
    rewrite <- H3 in H1; rewrite <- H4 in H2; clear H3 H4.
    apply NonExpansive_eq_simplify.
    extensionality x.
    set (H1' := f_equal (fun f => NE_fun f x) H1); clearbody H1'; clear H1.
    set (H2' := f_equal (fun f => NE_fun f x) H2); clearbody H2'; clear H2.
    cbn in *.
    destruct (f x); destruct (g x); auto.    
  Qed.

End CBULt_Product.

Instance CBULt_Has_Products (L : MLattice) : Has_Products (CBULt L) := CBULt_Product.
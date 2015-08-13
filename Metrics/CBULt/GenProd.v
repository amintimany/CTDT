Require Import
        Essentials.Facts_Tactics
        Essentials.Notations
        Essentials.Arith.
Require Import Lattice.MLattice Metrics.UltraMetric
        Metrics.Cauchy Metrics.Limit
        Metrics.Mappings Metrics.Complete_UltraMetric.
Require Import
        Categories.Essentials.Notations
        Categories.Category.Category
        Categories.Limits.GenProd_GenSum
        Categories.KanExt.Local
        Categories.Functor.Main
        Categories.NatTrans.Main
.

Require Import Metrics.CBULt.CBULt.


Section CBULt_GenProd.
  Context (L : MLattice) {A : Type} (f : A → CBULt L).

  Program Definition prod_UM : UltraMetric L :=
    {|
      UM_Carrier := ∀ x, (UM_Carrier (f x));
      UM_distance := fun x y => (⊔ᵍ (fun u => ∂(x u, y u)))%metric%lattice
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
    cbn; intros x y H.
    extensionality u.
    cut (∂(x u, y u) = ⊥%lattice)%metric;
      [
        intros H1; apply UM_zero_dist_eq; trivial |
        apply LE_Bottom_Bottom; rewrite <- H;
        apply (lub_ub (fun u => (∂(x u, y u))%metric))
      ].
  Qed.    

  Next Obligation.
  Proof.  
    intros x y z; cbn.
    apply lub_lst; intros u.
    (eapply PO_Trans; [apply UM_ineq|]).
    apply lub_lst; intros [|].
    eapply PO_Trans; [|
                      (apply (lub_ub (fun u : bool => if u then _ else _) _ true))
                     ];
    apply (lub_ub (fun u : _ => (∂(x u, z u))%metric)).
    eapply PO_Trans; [|
                      (apply (lub_ub (fun u : bool => if u then _ else _) _ false))
                     ];
    apply (lub_ub (fun u : _ => (∂(z u, y u))%metric)).
  Qed.

  Program Definition Separated_Cauchy (chs : Cauchy_Sequence prod_UM)
          (x : A) :
    Cauchy_Sequence (f x) :=
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
    
  Program Definition prod_CUM : Complete_UltraMetric L :=
    {|
      CUM_UM := prod_UM;
      CUM_complete :=
        fun chs =>
          {|
            Lim := fun x => (CUM_complete (f x) (Separated_Cauchy chs x))
          |}
    |}.

  Next Obligation.
  Proof.
    intros chs ε.
    destruct (ML_bottom_dichotomy L) as [dict|dict].
    {
      destruct (dict _ (projT2 ε)) as [ε' Hd1 [Hd2 Hd3]].
      destruct (CHS_cauchy _ chs (existT _ _ Hd1)) as [N H].
      cut (∀ (x : A) (n : nat), N ≤ n → ((∂(chs n x, CUM_complete (f x) (Separated_Cauchy chs x)))%metric ⊑ ε')%order).
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
        assert (H3 := proj2_sig (Lim_limit (CUM_complete (f x) (Separated_Cauchy chs x)) (existT _ _ Hd1)) (max (proj1_sig
         (Lim_limit (CUM_complete (f x) (Separated_Cauchy chs x))
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
      assert (H3 := Hd2 _ (proj2_sig (Lim_limit (CUM_complete (f x) (Separated_Cauchy chs x)) (existT _ _ Hd1)) (max (proj1_sig
         (Lim_limit (CUM_complete (f x) (Separated_Cauchy chs x))
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
    
  Program Definition CBULt_GenProd : GenProd f :=
    {|
      LRKE :=
        {|
          cone_apex :=
            {|
              FO := fun _ => prod_CUM;
              FA := fun a b h => id (CBULt L) _
            |};
          cone_edge :=
            {|
              Trans :=
                fun c =>
                  {|
                    NE_fun := fun F => F c
                  |}
            |}
        |};
      LRKE_morph_ex :=
        fun Cn =>
          {|
            cone_morph :=
              {|
                Trans :=
                  fun c =>
                    {|
                      NE_fun :=
                        (fun H x =>
                           (fun F =>
                              F x
                                (match c as u return
                                       ((Cn _o)%object u → _)
                                 with
                                 | tt => fun H0 : (Cn _o)%object tt => H0
                                 end H)
                           )
                             (fun d : Discr.Discr_Cat A => Trans Cn d))
                          
                        
                    |}
              |}
          |}
    |}.

  Next Obligation.
  Proof.
    intros []; trivial.
  Qed.

  Next Obligation.
    intros [] [] [] _ _; auto.
  Qed.

  Next Obligation.
  Proof.
    cbn.
    intros c x y.
    apply (lub_ub (fun u : A => (∂( x u, y u))%metric)).
  Qed.    

  Next Obligation.
  Proof.
    cbn.
    intros c c' h.
    ElimEq.
    rewrite NonExp_id_unit_left.
    rewrite NonExp_id_unit_right.
    trivial.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply CBULt_GenProd_obligation_4.
  Qed.

  Next Obligation.
  Proof.
    intros Cn [] x y.
    apply lub_lst.
    intros.
    apply (fun d => NE_non_expansive (Trans Cn d)).
  Qed.

  Next Obligation.
  Proof.
    intros Cn [] [] [].
    apply NonExpansive_eq_simplify.
    extensionality u; extensionality u'.
    cbn.
    apply (equal_f (f_equal NE_fun (@Trans_com _ _ _ _ Cn u' u' eq_refl))).
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply CBULt_GenProd_obligation_7.
  Qed.

  Next Obligation.
  Proof.
    intros Cn.
    apply NatTrans_eq_simplify.
    FunExt.
    apply NonExpansive_eq_simplify.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    intros Cn h h'.
    apply NatTrans_eq_simplify.
    extensionality x.
    destruct x.
    apply NonExpansive_eq_simplify.
    extensionality u.
    extensionality w.
    set (hc := (cone_morph_com h')).
    rewrite (cone_morph_com h) in hc.
    cbn in *.
    apply (f_equal
                  (fun c : ((Cn
                               ∘ Cat_Terminal.Functor_To_1_Cat
                               (Discr.Discr_Cat A))
                              –≻ (@Discr.Discr_Func (CBULt L) _ f))%nattrans =>
                     NE_fun (Trans c w) u
                  )
                  hc
        ).
  Qed.

End CBULt_GenProd.
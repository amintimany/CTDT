Require Import Coq.Arith.Compare_dec.

Require Import
        Essentials.Facts_Tactics
        Essentials.Notations
        Essentials.Types
        Essentials.Omega.
Require Import Metrics.Mappings Metrics.Cauchy.
Require Import Metrics.Complete_UltraMetric.
Require Import
        Categories.Category.Main
        Categories.Functor.Main
        Categories.Archetypal.Discr.Discr
        Categories.Archetypal.PreOrder_Cat.OmegaCat
        Categories.Limits.Limit
.
Require Import MCat.MCat MCat.Opposite MCat.Product MCat.MFunc.
Require Import MCat.IncreasingCauchyTower.IncreasingCauchyTower
        MCat.IncreasingCauchyTower.Related_CoCone_Cone_Limit
        MCat.IncreasingCauchyTower.Cone_Limit_Related_CoCone
.

Local Open Scope order_scope.
Local Open Scope metric_scope.
Local Open Scope lattice_scope.


(** In this section define shifting of increasing cauchy towers (ICTs) and
show that if a cone is the limit of an ICT, there is a cone (with the same apex)
that is the limit of the shifted version. *)
Section Shift_One.
  Context {L : MLattice} {M : MCat L} (ICT : IncreasingCauchyTower M).


  (** The increasing cauchy tower obtained by shifting the given cauchy tower by one. 
In other words,

#
<pre>
              f₀        f₁
            ————→     ————→      ......>
       A₀          A₁        A₂  ...... 
            ←————     ←————      <......
              g₀        g₁
</pre>
#

is turned into:

#
<pre>
              f₁        f₂
            ————→     ————→      ......>
       A₁          A₂        A₃  ...... 
            ←————     ←————      <......
              g₁        g₂
</pre>
#

*)
  Program Definition ICT_Shift_One : IncreasingCauchyTower M :=
    {|
      ICT_Objs := fun n => ICT (S n);
      ICT_fs := fun n => ICT_fs ICT (S n);
      ICT_gs := fun n => ICT_gs ICT (S n);
      ICT_gs_split_epi := fun n => ICT_gs_split_epi ICT (S n);
      ICT_approach_id :=
        fun ε : ApprType L =>
          let (N, Hε) := ICT_approach_id ICT ε in
          exist
            _
            _
            (fun m H =>
               Hε (S m)
                 (Nat.le_trans _ _ _ (le_S _ _ (le_n N)) (le_S _ _ H)))
    |}.

  (** Interaction of ICT_Funct with its shifted counterpart. *)
  Theorem ICT_Func_Shift_One {m n : nat} (h : m ≤ n) (h' : S m ≤ S n) :
    ((ICT_Func ICT) _a h' = (ICT_Func ICT_Shift_One) _a h)%morphism.
  Proof.
    cbn.
    induction (le_Tle h) as [|u t IHt].
    {
      replace h' with (le_n (S m)) by apply proof_irrelevance.
      rewrite le_Tle_n.
      trivial.
    }
    {
      dependent destruction h'.
      + exfalso; eapply Not_S_Tle; eauto.
      + rewrite le_Tle_S.
        cbn.
        rewrite (IHt (Tle_le t)).
        trivial.
    }
  Qed.

  (** Interaction of ICT_inv_Funct with its shifted counterpart. *)
  Theorem ICT_inv_Func_Shift_One {m n : nat} (h : m ≤ n) (h' : S m ≤ S n) :
    ((ICT_inv_Func ICT) _a h' = (ICT_inv_Func ICT_Shift_One) _a h)%morphism.
  Proof.
    cbn.
    induction (le_Tle h) as [|u t IHt].
    {
      replace h' with (le_n (S m)) by apply proof_irrelevance.
      rewrite le_Tle_n.
      trivial.
    }
    {
      dependent destruction h'.
      + exfalso; eapply Not_S_Tle; eauto.
      + rewrite le_Tle_S.
        cbn.
        rewrite (IHt (Tle_le t)).
        trivial.
    }
  Qed.
  
  Context (Cn : Cone (ICT_Func ICT)).

  (** A cone to an ICT can be turned into a cone to its shifted version. *)
  Program Definition Cone_To_ICT_Shift_One : Cone (ICT_Func ICT_Shift_One) :=
    {|
      cone_apex := Cn;
      cone_edge :=
        {|
          Trans := fun n => Trans Cn (S n)
        |}
    |}.

  Local Obligation Tactic := idtac.

  Next Obligation.
  Proof.
    intros c c' h; cbn in *.
    assert (h' : S c' ≤ S c) by abstract omega.
    cbn_rewrite (Trans_com Cn h').
    cbn_rewrite (ICT_Func_Shift_One h h').
    trivial.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Cone_To_ICT_Shift_One_obligation_1.
  Qed.

  (** A cocone interacting with a cone to an ICT can be turned into a cocone interacting with
the cone to its shifted version obtained from that cone. *)
  Section CoCone_Interacting_With_Cone_To_ICT_Shift_One.
    Context (CCn : CoCone_Interacting_With Cn).

    Program Definition CoCone_Interacting_With_Cone_To_ICT_Shift_One :
      CoCone_Interacting_With Cone_To_ICT_Shift_One :=
      {|
        CCIW_injs := fun n => CCn (S n)
      |}.

    Next Obligation.
    Proof.
      intros c c' h; cbn in *.
      assert (h' : S c' ≤ S c) by abstract omega.
      etransitivity; [apply (CCIW_injs_form_cocone _ _ CCn _ _ h')|].
      cbn.
      cbn_rewrite (ICT_inv_Func_Shift_One h h').
      trivial.
    Qed.

    Next Obligation.
    Proof.
      intros; apply (CCIW_split_epi _ _ CCn).
    Qed.

  End CoCone_Interacting_With_Cone_To_ICT_Shift_One.

  Context (CCn : CoCone_Related_To Cn).

  (** A cocone related to a cone to an ICT can be turned into a cocone related to
the cone to its shifted version obtained from that cone. *)
  Program Definition CoCone_Related_To_Cone_To_ICT_Shift_One :
    CoCone_Related_To Cone_To_ICT_Shift_One :=
    {|
      TRCC_CoCone := CoCone_Interacting_With_Cone_To_ICT_Shift_One (TRCC_CoCone _ _ CCn);
      TRCC_approach_id :=
        fun ε : ApprType L =>
          let (N, Hε) := TRCC_approach_id ICT _ _ ε in
          exist
            _
            _
            (fun m H =>
               Hε (S m)
                 (Nat.le_trans _ _ _ (le_S _ _ (le_n N)) (le_S _ _ H)))
    |}.

  Context (il : is_Limit _ Cn).

  (** If a cone is limit of an ICT, then its converted version is the limit of the
shifted ICT. *)
  Definition is_Limit_Cone_To_ICT_Shift_One_is_Limit :
    is_Limit _ Cone_To_ICT_Shift_One :=
    Related_CoCone_Cone_Limit
      _
      _
      Cone_To_ICT_Shift_One
      CoCone_Related_To_Cone_To_ICT_Shift_One
  .

End Shift_One.


Section Locally_Contractive_Func.
  Context {L : MLattice}
          {M : MCat L}
          (ICT : IncreasingCauchyTower M)
          (F : LocallyContractive (MCat_Prod (MCat_Op M) M) M).
  

  (** The increasing cauchy tower obtained by applying the given functor to the given ICT. 
In other words,

#
<pre>
              f₀        f₁
            ————→     ————→      ......>
       A₀          A₁        A₂  ...... 
            ←————     ←————      <......
              g₀        g₁
</pre>
#

is turned into:

#
<pre>
           F(g₀,f₀)         F(g₁,f₁)
            ————→            ————→            ......>
  F(A₀,A₀)           F(A₁,A₁)       F(A₂,A₂)  ...... 
            ←————            ←————            <......
           F(f₀,g₀)         F(f₁,g₁)
</pre>
#
*)
  Program Definition Locally_Contractive_Func_ICT : IncreasingCauchyTower M :=
    {|
      ICT_Objs := fun n => (F _o (ICT n, ICT n))%object;
      ICT_fs := fun n => (F @_a (_,_) (_,_) (ICT_gs ICT n, ICT_fs ICT n))%morphism;
      ICT_gs := fun n => (F @_a (_,_) (_,_) (ICT_fs ICT n, ICT_gs ICT n))%morphism
    |}.

  Next Obligation.
  Proof.
    cbn_rewrite <- (@F_compose _ _ F); cbn.
    cbn_rewrite (ICT_gs_split_epi ICT).
    apply (@F_id _ _ F).
  Qed.    

  Local Obligation Tactic := idtac.

  Next Obligation.
  Proof.
    cbn in *.
    intros ε.
    destruct (ML_bottom_dichotomy L) as [dicht|dicht].
    {
      destruct (dicht _ (projT2 ε)) as [y' Hd1 [Hd2 Hd3]].
      destruct (ICT_approach_id ICT (existT _ _ Hd1)) as [N H1].
      cbn in H1.
      exists N.
      intros n H2.
      specialize (H1 _ H2).
      cbn.
      cbn_rewrite <- (@F_compose _ _ F); cbn.
      cbn_rewrite <- (@F_id _ _ F).
      eapply LE_LT_Trans;[eapply (CN_contractive (@LCN_FA _ _ _ F _ _))|]; cbn.
      eapply LE_LT_Trans; [apply CR_non_expansive|].
      eapply LE_LT_Trans; [|apply Hd3].
      apply lub_lst; intros [|]; apply H1.
    }
    {
      destruct dicht as [ab Hd1 Hd2].
      destruct (ICT_approach_id ICT (existT _ _ Hd1)) as [N H1].
      cbn in H1.
      exists N.
      intros n H2.
      specialize (H1 _ H2).
      apply Hd2 in H1.
      cbn.
      cbn_rewrite <- (@F_compose _ _ F); cbn.
      cbn_rewrite <- (@F_id _ _ F).
      eapply LE_LT_Trans;[eapply (CN_contractive (@LCN_FA _ _ _ F _ _))|]; cbn.
      eapply LE_LT_Trans; [apply CR_non_expansive|].
      rewrite H1.
      rewrite lub_bot.
      apply ML_appr_pos.
      exact (projT2 ε).
    }
  Qed.

  Section Cone_and_Cone_interacting_with.
    Context
      (Cn : Cone (ICT_Func ICT))
      (CCn : CoCone_Interacting_With Cn).

    (** A cone to an ICT can be turned into a cone to the version where
F is applied to the ICT. *)
    Program Definition Cone_To_Locally_Contractive_Func_ICT :
      Cone (ICT_Func Locally_Contractive_Func_ICT) :=
      {|
        cone_apex := Func_From_SingletonCat (F _o (Cn, Cn))%object;
        cone_edge :=
          {|
            Trans :=
              fun n =>
                (
                  F @_a
                    (_, _)
                    (_, _)
                    (Trans (CCIW_CoCone _ _ CCn) n, Trans Cn n)
                )%morphism
          |}
      |}.

    Local Ltac rewrite_Trans_com Cn h W :=
      set (W := Trans_com Cn h);
      cbn in W;
      repeat rewrite From_Term_Cat in W; cbn in W;
      repeat rewrite MC_id_unit_right in W;
      repeat rewrite MC_id_unit_left in W
    .
    
    Next Obligation.
    Proof.
      intros c c' h; cbn in *.
      rewrite_Trans_com Cn h W; rewrite W; clear W.
      rewrite_Trans_com (CCIW_CoCone _ _ CCn) h W; rewrite W; clear W.
      rewrite MC_id_unit_right.
      induction (le_Tle h) as [|m t IHt].
      + cbn; repeat rewrite MC_id_unit_right; repeat rewrite MC_id_unit_left.
        trivial.
      + cbn in *.
        specialize (IHt (Tle_le t)).
        rewrite_Trans_com Cn (le_S _ _ (le_n m)) W; rewrite W in IHt; clear W.
        rewrite_Trans_com (CCIW_CoCone _ _ CCn) (le_S _ _ (le_n m)) W; rewrite W in IHt; clear W.
        rewrite le_Tle_S, le_Tle_n in IHt.
        cbn in IHt.
        rewrite MC_id_unit_right, MC_id_unit_left in IHt.
        rewrite (MC_assoc _ _ _ _ _ (Trans Cn (S m))).
        rewrite MC_assoc_sym.
        etransitivity; [apply IHt|].
        cbn_rewrite
          (
            @F_compose
              _
              _
              F
              (_, _)
              (_, _)
              (_,_)
              (CCn (S m), Trans Cn (S m))
              (ICT_fs ICT m, ICT_gs ICT m)
          ).
        rewrite MC_assoc.
        trivial.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Cone_To_Locally_Contractive_Func_ICT_obligation_1.
    Qed.

    (** A cocone interacting with a cone Cn can be turned into a cocone
interacting with the corresponding cone in the version where F is applied to the ICT *)
    Program Definition CoCone_Interacting_With_Cone_To_Locally_Contractive_Func_ICT :
      CoCone_Interacting_With Cone_To_Locally_Contractive_Func_ICT :=
      {|
        CCIW_injs :=
          fun n =>
            (
              F @_a
                (_, _)
                (_, _)
                (Trans Cn n, Trans (CCIW_CoCone _ _ CCn) n)
            )%morphism
      |}.
    
    Next Obligation.
    Proof.
      intros c c' h; cbn in *.
      rewrite_Trans_com Cn h W; rewrite W; clear W.
      rewrite_Trans_com (CCIW_CoCone _ _ CCn) h W; rewrite W; clear W.
      rewrite MC_id_unit_left.
      induction (le_Tle h) as [|m t IHt].
      + cbn; repeat rewrite MC_id_unit_right; repeat rewrite MC_id_unit_left.
        trivial.
      + cbn in *.
        specialize (IHt (Tle_le t)).
        rewrite_Trans_com Cn (le_S _ _ (le_n m)) W; rewrite W in IHt; clear W.
        rewrite_Trans_com (CCIW_CoCone _ _ CCn) (le_S _ _ (le_n m)) W; rewrite W in IHt; clear W.
        rewrite le_Tle_S, le_Tle_n in IHt.
        cbn in IHt.
        rewrite MC_id_unit_right, MC_id_unit_left in IHt.
        rewrite (MC_assoc _ _ _ _ _ (Trans Cn (S m))).
        rewrite (MC_assoc_sym _ _ _ _ _ (@OmegaCat.FA_fx (M^op) ICT (ICT_fs ICT) c' m t)).
        etransitivity; [apply IHt|].
        cbn_rewrite
          (
            @F_compose
              _
              _
              F
              (_, _)
              (_, _)
              (_,_)
              (ICT_gs ICT m, ICT_fs ICT m)
              (Trans Cn (S m), CCn (S m))
          ).
        rewrite MC_assoc.
        trivial.
    Qed.

    Next Obligation.
    Proof.
      intros n; cbn.
      cbn_rewrite <- (@F_compose _ _ F); cbn.
      do 2 cbn_rewrite (CCIW_split_epi _ _ CCn).
      apply (@F_id _ _ F).
    Qed.

  End Cone_and_Cone_interacting_with.

  
  Context
    (Cn : Cone (ICT_Func ICT))
    (CCn : CoCone_Related_To Cn).

  (** A cocone related to a cone to an ICT can be turned into a cocone related to
the cone to the version where F is applied to that ICT. *)
  Program Definition CoCone_Related_To_Cone_To_Locally_Contractive_Func_ICT :
    CoCone_Related_To (Cone_To_Locally_Contractive_Func_ICT Cn CCn) :=
    {|
      TRCC_CoCone :=
        CoCone_Interacting_With_Cone_To_Locally_Contractive_Func_ICT Cn (TRCC_CoCone _ _ CCn)
    |}.

  Next Obligation.
  Proof.
    cbn.
    intros ε.
    destruct (ML_bottom_dichotomy L) as [dicht|dicht].
    {
      destruct (dicht _ (projT2 ε)) as [y' Hd1 [Hd2 Hd3]].
      destruct (TRCC_approach_id _ _ CCn (existT _ _ Hd1)) as [N H1].
      cbn in H1.
      exists N.
      intros n H2.
      specialize (H1 _ H2).
      cbn_rewrite <- (@F_compose _ _ F); cbn.
      cbn_rewrite <- (@F_id _ _ F).
      eapply LE_LT_Trans;[eapply (CN_contractive (@LCN_FA _ _ _ F _ _))|]; cbn.
      eapply LE_LT_Trans; [apply CR_non_expansive|].
      eapply LE_LT_Trans; [|apply Hd3].
      apply lub_lst; intros [|]; apply H1.
    }
    {
      destruct dicht as [ab Hd1 Hd2].
      destruct (TRCC_approach_id _ _ CCn (existT _ _ Hd1)) as [N H1].
      cbn in H1.
      exists N.
      intros n H2.
      specialize (H1 _ H2).
      apply Hd2 in H1.
      cbn_rewrite <- (@F_compose _ _ F); cbn.
      cbn_rewrite <- (@F_id _ _ F); cbn.
      eapply LE_LT_Trans;[eapply (CN_contractive (@LCN_FA _ _ _ F _ _))|]; cbn.
      eapply LE_LT_Trans; [apply CR_non_expansive|].
      eapply LE_LT_Trans; [|apply (ML_appr_pos _ _ (projT2 ε))].
      apply lub_lst; intros [|]; match goal with [|- ?A ⊑ ?B] => replace B with A; trivial end.
    }
  Qed.
    
  Context (il : is_Limit _ Cn).

  (** If a cone is limit of an ICT, then its converted version is the limit of the
version where F is applied to that ICT. *)
  Definition is_Limit_Cone_To_Locally_Contractive_Func_ICT_is_Limit :
    is_Limit _ (Cone_To_Locally_Contractive_Func_ICT Cn CCn) :=
    Related_CoCone_Cone_Limit
      _
      _
      (Cone_To_Locally_Contractive_Func_ICT Cn CCn)
      CoCone_Related_To_Cone_To_Locally_Contractive_Func_ICT
  .

End Locally_Contractive_Func.
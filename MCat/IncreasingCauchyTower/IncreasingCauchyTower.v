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
Require Import MCat.MCat.

Local Open Scope order_scope.
Local Open Scope metric_scope.
Local Open Scope lattice_scope.

Section IncreasingCauchyTower.
  Context {L : MLattice} {M : MCat L}.


  (** 
Intuitively, an increasing cauchy tower is a diagram:

#
<pre>
              f₀        f₁
            ————→     ————→      ......>
       A₀          A₁        A₂  ...... 
            ←————     ←————      <......
              g₀        g₁
</pre>
#
Such that fₙ makes gₙ a split epi for all n ∈ N, i.e., gₙ ∘ fₙ = id_Aₙ.
Furthermore, the distance between fₙ ∘ gₙ and id_Aₙ₊₁ decreases as n grows, i.e.,

#
<pre>
       ∀ ε, ∃ N, ∀ n, N ≤ n → ∂(fₙ ∘ gₙ, id_Aₙ₊₁) ⊏ ε
</pre>
#
.
*)
  Record IncreasingCauchyTower : Type :=
    {
      ICT_Objs :> nat → M;
      ICT_fs : ∀ n, (ICT_Objs n –≻ ICT_Objs (S n))%morphism;
      ICT_gs : ∀ n, (ICT_Objs (S n) –≻ ICT_Objs n)%morphism;
      ICT_gs_split_epi : ∀ n, ((ICT_gs n) ∘ (ICT_fs n) = id)%morphism;
      ICT_approach_id :
        ∀ (ε : ApprType L),
          {N : nat | ∀ n, N ≤ n → ∂(((ICT_fs n) ∘ (ICT_gs n))%morphism, id (ICT_Objs (S n))) ⊏ (projT1 ε)}
    }.

  Section ICT_Func_Limit.
    Context (ICT : IncreasingCauchyTower).

    (** The functor from ω → M that maps h : m ≤ n to gₘ ∘ ... ∘ gₙ₋₂ ∘ gₙ₋₁ from Aₙ → Aₘ. *)
    Definition ICT_Func :=
      OmegaCat_Op_Func (ICT_Objs ICT) (ICT_gs ICT).

    (** The functor from ω → M that maps h : m ≤ n to fₙ ∘ ... ∘ fₘ₊₂ ∘ fₘ₊₁ from Aₘ → Aₙ. *)
    Definition ICT_inv_Func :=
      OmegaCat_Func (ICT_Objs ICT) (ICT_fs ICT).

    (** conversion of gₙ to (ICT_Func _a) (le_S _ _ (le_n n) : n ≤ S n) *)
    Lemma ICT_gs_ICT_Func n :
      ICT_gs ICT n = (ICT_Func _a (Tle_S _ _ (Tle_n n)))%morphism.
    Proof.
      cbn.
      cbn_rewrite (MC_id_unit_left M); trivial.
    Qed.

    (** conversion of fₙ to (ICT_inv_Func _a) (le_S _ _ (le_n n) : n ≤ S n) *)
    Lemma ICT_fs_ICT_inv_Func n :
      ICT_fs ICT n = (ICT_inv_Func _a (Tle_S _ _ (Tle_n n)))%morphism.
    Proof.
      cbn.
      cbn_rewrite (MC_id_unit_right M); trivial.
    Qed.
    
    (** A simple tactic to solve equality of OmegaCat_Func *)
    Ltac solve_simpl_omega_func_eq :=
      match goal with
      |  [|- (?F _a ?x)%morphism = (?G _a ?y)%morphism] =>
         cutrewrite (x = y); [trivial|apply Tle_is_HProp]; fail
      | [|- OmegaCat.FA_fx _ ?f _ _ ?x = OmegaCat.FA_fx _ ?f _ _ ?y] =>
        cutrewrite (x = y); [trivial|apply Tle_is_HProp]; fail
      end.

    Local Hint Extern 1 => solve_simpl_omega_func_eq.

    Lemma ICT_inv_Func_ICT_Func_id a b (g : (a ≤ b)%omegacat) :
      (MC_compose M) ((ICT_inv_Func _a)%morphism g, (ICT_Func _a)%morphism g) = MC_id M.
    Proof.
      cbn in *.
      induction g as [|m t IHt].
      + cbn; apply MC_id_unit_left.
      + cbn in *.
        rewrite MC_assoc_sym.
        rewrite (MC_assoc _ _ _ _ _ _ (ICT_gs ICT m)).
        cbn_rewrite ICT_gs_split_epi.
        rewrite MC_id_unit_right.
        apply IHt.
    Qed.
      
    (** A fundamental property of increasing cauchy towers:
Given (g : a ≤ b) (h : c ≤ b) (i : a ≤ c),

(ICT_Func _a h)  ∘ (ICT_inv_Func _a g) = (ICT_inv_Func _a i)

*)
    Lemma ICT_inv_Func_ICT_Func_1
          a b c
          (g : (a ≤ b)%omegacat)
          (h : (c ≤ b)%omegacat)
          (i : (a ≤ c)%omegacat) :
      (MC_compose M) ((ICT_inv_Func _a)%morphism g, (ICT_Func _a)%morphism h) =
      (ICT_inv_Func _a)%morphism i.
    Proof.
      replace g with (Tle_trans _ _ _ i h) by (apply Tle_is_HProp).
      cbn.
      cbn_rewrite (@F_compose _ _ ICT_inv_Func).
      rewrite MC_assoc_sym.
      cbn_rewrite ICT_inv_Func_ICT_Func_id.
      apply MC_id_unit_left.
    Qed.

    (** A fundamental property of increasing cauchy towers:
Given (g : a ≤ b) (h : c ≤ b) (i : c ≤ a),

(ICT_Func _a h)  ∘ (ICT_inv_Func _a g) = (ICT_Func _a i)

*)
    Lemma ICT_inv_Func_ICT_Func_2
          a b c
          (g : (a ≤ b)%omegacat)
          (h : (c ≤ b)%omegacat)
          (i : (c ≤ a)%omegacat) :
      (MC_compose M) ((ICT_inv_Func _a)%morphism g, (ICT_Func _a)%morphism h) =
      (ICT_Func _a)%morphism i.
    Proof.
      replace h with (Tle_trans _ _ _ i g) by (apply Tle_is_HProp).
      cbn.
      cbn_rewrite (@F_compose _ _ ICT_Func).
      rewrite MC_assoc.
      cbn_rewrite ICT_inv_Func_ICT_Func_id.
      apply MC_id_unit_right.
    Qed.

    Local Arguments OmegaCat_Op_Func : simpl never.
    Local Arguments OmegaCat_Func : simpl never.


    (**
This is a function used to create an auxiliary cone to ICT_Func
with apex Aₘ. In practice, Aux_cone_fun is id if m = n. It is
gₘ ∘ ... ∘ gₙ₋₁ ∘ gₙ if n < m and fₙ ∘ ... ∘ fₘ₊₁ ∘ fₘ.
*)
    Definition Aux_cone_fun m n
      : MC_Hom M (ICT_Objs ICT m) (ICT_Objs ICT n)
      :=
      match gt_eq_gt_dec n m with
      | inleft H =>
        match H with
        | left h => (ICT_Func _a)%morphism (Tle_trans _ _ _ (Tle_S _ _ (Tle_n n)) (le_Tle h))
        | right W =>
          match W in _ = y return
                ((ICT y) –≻ (ICT n))%morphism
          with
          | eq_refl => id
          end
        end
      | inright h => (ICT_inv_Func _a)%morphism (Tle_trans _ _ _ (Tle_S _ _ (Tle_n m)) (le_Tle h))
      end.

    Lemma Aux_cone_fun_S m x :
      Aux_cone_fun m x = (MC_compose M) (ICT_fs ICT m, Aux_cone_fun (S m) x).
    Proof.
      unfold Aux_cone_fun.
      (destruct gt_eq_gt_dec as [H|H]; [destruct H as [H|H]|]);
        (destruct gt_eq_gt_dec as [H'|H']; [destruct H' as [H'|H']|]);
        try omega;
        ElimEq;
        repeat rewrite ICT_fs_ICT_inv_Func; repeat rewrite ICT_gs_ICT_Func; cbn
      .
      + erewrite ICT_inv_Func_ICT_Func_2; trivial.
      + change (@MC_id _ M (ICT_Objs ICT x)) with (ICT_Func _a (Tle_n x))%morphism.
        erewrite ICT_inv_Func_ICT_Func_2; trivial.
      + change (@MC_id _ M (ICT_Objs ICT x)) with (ICT_Func _a (Tle_n x))%morphism.
        dependent destruction H'.
        erewrite ICT_inv_Func_ICT_Func_1; trivial.
      + cbn_rewrite <- (@F_compose _ _ ICT_inv_Func); auto.
    Qed.
    
    (** This is an auxiliary cone to ICT_Func with apex Aₘ. *)
    Program Definition Aux_cone (m : nat) : Cone ICT_Func :=
      {|
        cone_apex := Func_From_SingletonCat (ICT m);
        cone_edge :=
          {|
            Trans := Aux_cone_fun m
          |}
      |}.
    
    Next Obligation.
    Proof.
      unfold Aux_cone_fun.
      cbn.
      repeat (try destruct gt_eq_gt_dec;
              try match goal with
                    [H : {_} + {_} |- _] => destruct H
                  end; ElimEq);
        try (assert (h' := Tle_le h); omega; clear h'; fail);
        repeat rewrite (MC_id_unit_right M);
        repeat rewrite ICT_gs_ICT_Func;
        repeat rewrite ICT_fs_ICT_inv_Func;
        repeat cbn_rewrite <- (@F_compose _ _ ICT_Func);
        repeat cbn_rewrite <- (@F_compose _ _ ICT_inv_Func);
        try
          (change (@MC_id _ M (ICT_Objs ICT c)) with (ICT_Func _a (Tle_n c))%morphism; auto).
      + set (W := ICT_inv_Func_ICT_Func_2); cbn in W; erewrite W; auto.
      + erewrite ICT_inv_Func_ICT_Func_2; auto.
      + erewrite ICT_inv_Func_ICT_Func_1; auto.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Aux_cone_obligation_1.
    Qed.

    (** A simplified version of Trans_com of Cones into ICT_Func. *)
    Lemma Cone_Trans_com_simplified
          (Cn : Cone ICT_Func)
          {c c' : nat}
          (h : (c' ≤ c)%omegacat)
      :
        Trans Cn c' =
      (MC_compose M) (Trans Cn c, (ICT_Func _a)%morphism h).
    Proof.
      etransitivity; [|apply (Trans_com Cn h)].
      cbn; rewrite From_Term_Cat.
      symmetry; apply MC_id_unit_right.
    Qed.

    (** A simplified version of Trans_com of CoCones into ICT_inv_Func. *)
    Lemma CoCone_Trans_com_simplified
          (Cn : CoCone ICT_inv_Func)
          {c c' : nat}
          (h : (c' ≤ c)%omegacat)
      :
        Trans Cn c' =
      (MC_compose M) ((ICT_inv_Func _a)%morphism h, Trans Cn c).
    Proof.
      etransitivity; [|apply (Trans_com Cn h)].
      cbn; rewrite From_Term_Cat.
      symmetry; apply MC_id_unit_left.
    Qed.

    Section CoCone_Interacting_With_and_related.

      Context (Cn : Cone ICT_Func).

      (** This is the type of cocones with the same apex as the provided cone.
Furthermore, Trans Cn n ∘ Trans CCn n = id_Aₙ. Where CCn is the cocone of
this definition.
       *)
      Program Record CoCone_Interacting_With :=
        {
          CCIW_injs :> ∀ n, (ICT n –≻ Cn)%morphism;
          CCIW_injs_form_cocone :
            ∀ (c c' : (ω%omegacat ^op)%category) (h : (c –≻ c')%morphism),
              (
                (CCIW_injs c')
                  ∘ (
                    (
                      (Func_From_SingletonCat Cn ^op)
                        ∘ (Functor_To_1_Cat ω%omegacat ^op)
                    )
                      _a
                  ) h
              )%morphism
              = (MC_compose M (((ICT_inv_Func ^op) _a) h, CCIW_injs c))%morphism;
          CCIW_CoCone : CoCone ICT_inv_Func :=
            {|
              cone_apex := (Func_From_SingletonCat Cn)^op;
              cone_edge :=
                {|
                  Trans := CCIW_injs;
                  Trans_com := CCIW_injs_form_cocone;
                  Trans_com_sym := fun _ _ _ => eq_sym (CCIW_injs_form_cocone _ _ _)
                |}
            |};
          CCIW_split_epi : ∀ n, ((Trans Cn n) ∘ (CCIW_injs n) = id)%morphism
        }.

      (** A cocone CCn related to a cone Cn is a cocone interacting with it such that the
distance between composition of injections of CCn with projections of Cn approach the
identity morphism of Cn (Cn's apex). *)
      Program Record CoCone_Related_To : Type :=
        {
          TRCC_CoCone :> CoCone_Interacting_With;
          TRCC_approach_id :
            ∀ (ε : ApprType L),
              {N : nat | ∀ n, N ≤ n → ∂(((TRCC_CoCone n) ∘ (Trans Cn n))%morphism, id Cn) ⊏ (projT1 ε)}
        }.

      Context (CCn : CoCone_Interacting_With).
      
      (** Composition of a cone projection and a cocone injection of an interacting cocone. *)
      Lemma Cone_Interacting_CoCone_Aux_cone_fun_n_m n m
        :
          (MC_compose M)
            (Trans (CCIW_CoCone CCn) n, Trans Cn m) =
          Aux_cone_fun n m.
      Proof.
        repeat unfold Aux_cone_fun.
        repeat (try destruct gt_eq_gt_dec;
                try match goal with
                      [H : {_} + {_} |- _] => destruct H
                    end; ElimEq);
          try omega; cbn.
        + rewrite (Cone_Trans_com_simplified Cn (Tle_trans _ _ _ (Tle_S _ _ (Tle_n m)) (le_Tle g))).
          rewrite (MC_assoc M).
          cbn_rewrite (CCIW_split_epi CCn).
          apply MC_id_unit_right.
        + apply CCIW_split_epi.
        + cbn_rewrite (CoCone_Trans_com_simplified (CCIW_CoCone CCn) (Tle_trans _ _ _ (Tle_S _ _ (Tle_n n)) (le_Tle g))).
          rewrite (MC_assoc_sym M).
          cbn_rewrite (CCIW_split_epi CCn).
          apply MC_id_unit_left.
      Qed.      

      (** Composition of a projection with Aux_cone_fun is just another projection. *)
      Lemma Aux_cone_fun_m_n_o_Cone_n_eq_Cone_m n m (h : m ≤ n) :
        (MC_compose M)
          (Trans Cn n, Aux_cone_fun n m) = Trans Cn m.
      Proof.
        set (W := @Trans_com _ _ _ _ Cn n m).
        cbn in W.
        rewrite From_Term_Cat in W; cbn in W.
        rewrite MC_id_unit_right in W.
        unfold Aux_cone_fun.
        destruct gt_eq_gt_dec as [[H|H]|H]; try omega.
        + symmetry; apply W.
        + destruct H; cbn.
          apply MC_id_unit_left.
      Qed.

      Context (Cn' : Cone ICT_Func).
      
      (** The sequence of projections Cn composed with injections (of a cocone interacting with Cn')
forms a cauchy sequence. *)
      Program Definition proj_n_o_inj_n_cauchy
        :
          Cauchy_Sequence (MC_Hom M (Cn' : M) (Cn : M)) :=
        {|
          CHS_seq :=
            fun n =>
              (MC_compose M)
                (Trans Cn' n,
                 Trans (CCIW_CoCone CCn) n)
        |}.

      Next Obligation.
      Proof.
        apply Cauchy_condition_simpl.
        clear.
        intros ε.
        destruct (ICT_approach_id ICT ε) as [N H1].
        exists N.
        intros n H2.
        set (W := @Trans_com _ _ _ _ Cn' _ _ (Tle_S _ _ (Tle_n n)));
          cbn in W; rewrite From_Term_Cat in W; cbn in W;
          rewrite MC_id_unit_right in W; rewrite W; clear W.
        cbn_rewrite ( CoCone_Trans_com_simplified (CCIW_CoCone CCn) (Tle_S _ _ (Tle_n n))).
        rewrite MC_assoc.
        rewrite (MC_assoc_sym M _ _ _ _ _ ((ICT_Func _a)%morphism (Tle_S n n (Tle_n n)))).
        rewrite
          <- (MC_id_unit_right _ _ _ (Trans (CCIW_CoCone CCn) (S n))) at 2.
        rewrite MC_assoc_sym.
        eapply LE_LT_Trans; [apply NE_non_expansive|].
        cbn.
        rewrite UM_eq_zero_dist.
        rewrite lub_sym.
        rewrite lub_bot.
        eapply LE_LT_Trans; [apply NE_non_expansive|].
        cbn.
        rewrite UM_eq_zero_dist.
        rewrite lub_bot.
        rewrite <- ICT_gs_ICT_Func.
        rewrite <- ICT_fs_ICT_inv_Func.
        apply H1; trivial.
      Qed.

    End CoCone_Interacting_With_and_related.

    Program Definition limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con_NT
            (Cn : Cone ICT_Func)
            (CCn : CoCone_Interacting_With Cn)
            (Cn' : Cone ICT_Func)
      :
        (Cn' –≻ Cn)%nattrans
      :=
        {|
          Trans :=
            fun h =>
              match h as u return (MC_Hom M ((Cn' _o)%object u) ((Cn _o)%object u)) with
              | tt =>
                (CUM_complete _ (proj_n_o_inj_n_cauchy Cn CCn Cn') : MC_Hom M (Cn' : M) (Cn : M))
              end
        |}.

    Next Obligation.
      repeat match goal with [H : unit|- _] => destruct H end.
      repeat rewrite From_Term_Cat; cbn.
      rewrite MC_id_unit_left, MC_id_unit_right.
      trivial.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con_NT_obligation_1.
    Qed.
      
    (** The limit of the sequence of projections of a cone Cn composed with injections
(of a cocone interacting with Cn') forms a cone morphism from Cn' to Cn. *)
    Program Definition limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con
            (Cn : Cone ICT_Func)
            (CCn : CoCone_Interacting_With Cn)
            (Cn' : Cone ICT_Func)
      :
        LoKan_Cone_Morph Cn' Cn :=
      {|
        cone_morph :=
          limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con_NT Cn CCn Cn'
      |}.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify.
      extensionality m.
      cbn.
      rewrite From_Term_Cat; cbn.
      rewrite MC_id_unit_left.
      set (z := CUM_complete (MC_Hom M (Cn' : M) (Cn : M)) (proj_n_o_inj_n_cauchy _ _ _)).
      rewrite (Limit_of_SubSeq_equal z m (Limit_of_SubSeq z m)).
      change (MC_compose M ((Limit_of_SubSeq z m) : MC_Hom _ _ _, Trans Cn m)) with
      (Lim (@NonExpansive_Continuous _ _ _ (Limit_of_SubSeq z m) _ (NonExpansive_Compose_right _ (Trans Cn m)))).
      match goal with
        [|- _ = Lim ?A] =>
        rewrite (Eq_Seq_Eq_Limits _ _ A (Limit_of_ConstSeq (Trans Cn' m)))
      end.
      {
        rewrite Limit_of_ConstSeq_equal.
        trivial.
      }
      {
        clear.
        extensionality n.
        cbn.
        rewrite MC_assoc_sym.
        match goal with
          [|- NE_fun (MC_compose M) (_, ?A) = _] =>
          cutrewrite (A = (Aux_cone_fun (m + n) m));
            [apply Aux_cone_fun_m_n_o_Cone_n_eq_Cone_m; trivial|
             apply Cone_Interacting_CoCone_Aux_cone_fun_n_m]
        end.
        abstract omega.
      }
    Qed.

  End ICT_Func_Limit.

End IncreasingCauchyTower.

Arguments IncreasingCauchyTower {_} _.
Arguments CoCone_Interacting_With {_ _ _} _.
Arguments CoCone_Related_To {_ _ _} _.
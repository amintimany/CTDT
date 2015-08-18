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
        Categories.Archetypal.Discr.Main
        Categories.Archetypal.PreOrder_Cat.OmegaCat
        Categories.KanExt.Local
        Categories.KanExt.LocalFacts.Uniqueness
        Categories.Limits.Limit
.
Require Import MCat.MCat.

Local Open Scope order_scope.
Local Open Scope metric_scope.
Local Open Scope lattice_scope.

Section IncreasingCauchyTower.
  Context {L : MLattice} (M : MCat L).

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

    Definition ICT_Func :=
      OmegaCat_Op_Func (ICT_Objs ICT) (ICT_gs ICT).
    
    Definition ICT_inv_Func :=
      OmegaCat_Func (ICT_Objs ICT) (ICT_fs ICT).

    Lemma MC_id_ICT_Func a :
      MC_id M = (ICT_Func _a)%morphism (le_n a).
    Proof.
      cbn.
      rewrite le_Tle_n; trivial.
    Qed.

    Lemma ICT_gs_ICT_Func n :
      ICT_gs ICT n = (ICT_Func _a (le_S _ _ (le_n n)))%morphism.
    Proof.
      cbn.
      rewrite le_Tle_S.
      rewrite le_Tle_n.
      cbn.
      cbn_rewrite (MC_id_unit_left M); trivial.
    Qed.

    Lemma ICT_fs_ICT_inv_Func n :
      ICT_fs ICT n = (ICT_inv_Func _a (le_S _ _ (le_n n)))%morphism.
    Proof.
      cbn.
      rewrite le_Tle_S.
      rewrite le_Tle_n.
      cbn.
      cbn_rewrite (MC_id_unit_right M); trivial.
    Qed.

    Local Ltac solve_simpl_omega_func_eq :=
      match goal with
      |  [|- (?F _a ?x)%morphism = (?F _a ?y)%morphism] =>
         cutrewrite (x = y); [trivial|apply proof_irrelevance]
      | [|- OmegaCat.FA_fx _ ?f _ _ ?x = OmegaCat.FA_fx _ ?f _ _ ?y] =>
        cutrewrite (x = y); [trivial|apply Tle_is_HProp]
      end.

    Local Hint Extern 1 => solve_simpl_omega_func_eq.

    Lemma ICT_inv_Func_ICT_Func_1  a b c (g : a ≤ b) (h : c ≤ b) (i : a ≤ c) :
      (MC_compose M) ((ICT_inv_Func _a)%morphism g, (ICT_Func _a)%morphism h) =
      (ICT_inv_Func _a)%morphism i.
    Proof.
      cbn.
      revert c h i.
      induction (le_Tle g) as [|m t IHt]; cbn.
      {
        intros c h i.
        rewrite (MC_id_unit_right M); trivial.
        assert (a = c) by omega.
        ElimEq.
        dependent destruction h; [|omega].
        dependent destruction i; [|omega].
        repeat rewrite le_Tle_n; trivial.
      }
      {
        intros c h i.
        rewrite (MC_assoc_sym M).
        dependent destruction h.
        {
          rewrite ICT_fs_ICT_inv_Func.
          rewrite le_Tle_n.
          cbn; rewrite (MC_id_unit_left M).
          replace t with (le_Tle (Tle_le t)) by apply Tle_is_HProp.
          cbn_rewrite <- (@F_compose _ _ ICT_inv_Func).
          solve_simpl_omega_func_eq.
        }
        {
          rewrite le_Tle_S; cbn.
          do 2 rewrite (MC_assoc M).
          rewrite (MC_assoc_sym M _ _ _ _ _ (ICT_fs ICT m)) at 1.
          cbn_rewrite (ICT_gs_split_epi ICT).
          rewrite (MC_id_unit_left M).
          apply IHt; omega.
        }
      }
    Qed.

    Lemma ICT_inv_Func_ICT_Func_2  a b c (g : a ≤ b) (h : c ≤ b) (i : c ≤ a) :
      (MC_compose M) ((ICT_inv_Func _a)%morphism g, (ICT_Func _a)%morphism h) =
      (ICT_Func _a)%morphism i.
    Proof.
      cbn.
      revert a g i.
      induction (le_Tle h) as [|m t IHt]; cbn.
      {
        intros a g i.
        rewrite (MC_id_unit_left M); trivial.
        assert (a = c) by omega.
        ElimEq.
        dependent destruction g; [|omega].
        dependent destruction i; [|omega].
        repeat rewrite le_Tle_n; trivial.
      }
      {
        intros a g i.
        rewrite (MC_assoc M).
        dependent destruction g.
        {
          rewrite ICT_gs_ICT_Func.
          rewrite le_Tle_n.
          cbn; rewrite (MC_id_unit_right M).
          replace t with (le_Tle (Tle_le t)) by apply Tle_is_HProp.
          cbn_rewrite <- (@F_compose _ _ ICT_Func).
          solve_simpl_omega_func_eq.
        }
        {
          rewrite le_Tle_S; cbn.
          do 2 rewrite (MC_assoc_sym M).
          rewrite (MC_assoc M _ _ _ _ _ (ICT_gs ICT m)) at 1.
          cbn_rewrite (ICT_gs_split_epi ICT).
          rewrite (MC_id_unit_right M).
          apply IHt; omega.
        }
      }
    Qed.
        
    Local Arguments OmegaCat_Op_Func : simpl never.
    Local Arguments OmegaCat_Func : simpl never.
    
    Section Limits_Lemmas.
      Context (Cn : Cone ICT_Func).
      
      Program Record The_Related_CoCone : Type :=
        {
          TRCC_injs :> ∀ n, (ICT n –≻ Cn)%morphism;
          TRCC_injs_form_cocone :
            ∀ (c c' : (ω%omegacat ^op)%category) (h : (c –≻ c')%morphism),
              (
                (TRCC_injs c')
                  ∘ (
                    (
                      (Func_From_SingletonCat Cn ^op)
                        ∘ (Functor_To_1_Cat ω%omegacat ^op)
                    )
                      _a
                  ) h
              )%morphism
              = (MC_compose M (((ICT_inv_Func ^op) _a) h, TRCC_injs c))%morphism;
          TRCC_CoCone :> CoCone ICT_inv_Func :=
            {|
              cone_apex := (Func_From_SingletonCat Cn)^op;
              cone_edge :=
                {|
                  Trans := TRCC_injs;
                  Trans_com := TRCC_injs_form_cocone;
                  Trans_com_sym := fun _ _ _ => eq_sym (TRCC_injs_form_cocone _ _ _)
                |}
            |};
          TRCC_split_epi : ∀ n, ((Trans Cn n) ∘ (TRCC_injs n) = id)%morphism;
          TRCC_approach_id :
            ∀ (ε : ApprType L),
          {N : nat | ∀ n, N ≤ n → ∂(((TRCC_injs n) ∘ (Trans Cn n))%morphism, id Cn) ⊏ (projT1 ε)}
        }.

      Local Definition Cone_Limit__The_Related_CoCone_aux_cone_fun m n :=
        match gt_eq_gt_dec n m with
        | inleft H =>
          match H with
          | left h => (MC_compose M) ((ICT_Func _a)%morphism h, ICT_gs ICT n)
          | right W =>
            match W in _ = y return
                  ((ICT y) –≻ (ICT n))%morphism
                      with
                      | eq_refl => id
            end
          end
        | inright h => (MC_compose M) (ICT_fs ICT m, (ICT_inv_Func _a)%morphism h)
        end.

      Lemma Cone_Limit__The_Related_CoCone_aux_cone_fun_S m x :
        Cone_Limit__The_Related_CoCone_aux_cone_fun m x =
        (MC_compose M)
          (ICT_fs ICT m, Cone_Limit__The_Related_CoCone_aux_cone_fun (S m) x).
      Proof.
        unfold Cone_Limit__The_Related_CoCone_aux_cone_fun.
        (destruct gt_eq_gt_dec as [H|H]; [destruct H as [H|H]|]);
          (destruct gt_eq_gt_dec as [H'|H']; [destruct H' as [H'|H']|]);
          try omega;
          ElimEq;
          repeat rewrite ICT_fs_ICT_inv_Func; repeat rewrite ICT_gs_ICT_Func;
          repeat cbn_rewrite <- (@F_compose _ _ ICT_Func);
          repeat cbn_rewrite <- (@F_compose _ _ ICT_inv_Func); cbn
        .
        + erewrite ICT_inv_Func_ICT_Func_2; trivial.
        + rewrite MC_id_ICT_Func.
          erewrite ICT_inv_Func_ICT_Func_2; trivial.
        + rewrite MC_id_ICT_Func.
          dependent destruction H'.
          erewrite ICT_inv_Func_ICT_Func_1; trivial.
        + auto.
      Qed.

      Local Program Definition Cone_Limit__The_Related_CoCone_aux_cone
            (m : nat) : Cone ICT_Func :=
        {|
          cone_apex := Func_From_SingletonCat (ICT m);
          cone_edge :=
            {|
              Trans := Cone_Limit__The_Related_CoCone_aux_cone_fun m
            |}
        |}.
          
      Next Obligation.
      Proof.
        unfold Cone_Limit__The_Related_CoCone_aux_cone_fun.
        repeat (try destruct gt_eq_gt_dec;
        try match goal with
              [H : {_} + {_} |- _] => destruct H
            end; ElimEq);
        try omega;
        repeat rewrite (MC_id_unit_right M);
        repeat rewrite ICT_gs_ICT_Func;
        repeat rewrite ICT_fs_ICT_inv_Func;
        repeat cbn_rewrite <- (@F_compose _ _ ICT_Func);
        repeat cbn_rewrite <- (@F_compose _ _ ICT_inv_Func);
        try solve_simpl_omega_func_eq;
        try rewrite MC_id_ICT_Func
        .
        +  set (W := ICT_inv_Func_ICT_Func_2); cbn in W; erewrite W; auto.
        + auto.
        + erewrite ICT_inv_Func_ICT_Func_2; auto.
        + erewrite ICT_inv_Func_ICT_Func_1; auto.
      Qed.

      Next Obligation.
      Proof.
        symmetry.
        apply Cone_Limit__The_Related_CoCone_aux_cone_obligation_1.
      Qed.
      
      Local Definition Cone_Limit__The_Related_CoCone_aux_cone_to_Cn
            (il : is_Limit _ Cn)
            n
        :=
          isCLRKE_morph_ex
            (Functor_To_1_Cat (ω%omegacat ^op)) ICT_Func Cn il
            (Cone_Limit__The_Related_CoCone_aux_cone n)
      .

      Lemma jm_o_in__h_n_m (il : is_Limit ICT_Func Cn) n m :
        (MC_compose M)
          (Trans (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il n) tt, Trans Cn m) =
        Cone_Limit__The_Related_CoCone_aux_cone_fun n m.
      Proof.
        set (W := f_equal (fun f => Trans f m) (cone_morph_com (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il n))).
        cbn in W.
        rewrite From_Term_Cat in W; cbn in W.
        rewrite MC_id_unit_left in W.
        symmetry.
        trivial.
      Qed.

      Lemma h_n_m_o_jn_eq_jm (il : is_Limit ICT_Func Cn) n m (h : m ≤ n) :
        (MC_compose M)
          (Trans Cn n, Cone_Limit__The_Related_CoCone_aux_cone_fun n m) = Trans Cn m.
      Proof.
        set (W := @Trans_com _ _ _ _ Cn n m).
        cbn in W.
        rewrite From_Term_Cat in W; cbn in W.
        rewrite MC_id_unit_right in W.
        unfold Cone_Limit__The_Related_CoCone_aux_cone_fun.
        destruct gt_eq_gt_dec as [[H|H]|H]; try omega.
        {
          specialize (W (le_trans _ _ _ (le_S _ _ (le_n m)) H)).
          cbn_rewrite (@F_compose _ _ ICT_Func) in W.
          rewrite <- ICT_gs_ICT_Func in W.
          symmetry; trivial.
        }
        {
          destruct H; cbn.
          apply MC_id_unit_left.
        }
      Qed.
        
      Local Program Definition Another_Cone_Limit__The_Related_CoCone_aux_cone_to_Cn
        (il : is_Limit ICT_Func Cn) (n n': nat) (h : n ≤ n')
        :
          LoKan_Cone_Morph
            (Cone_Limit__The_Related_CoCone_aux_cone n)
            Cn :=
        {|
          cone_morph :=
            {|
              Trans :=
                fun w =>
                  MC_compose M
                             ((ICT_inv_Func _a)%morphism h,
                               (Trans (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il n') w)
                             )
            |}
        |}.

      Next Obligation.
      Proof.
        repeat match goal with [H : unit |- _] => destruct H end.
        rewrite From_Term_Cat; cbn.
        rewrite MC_id_unit_right; rewrite MC_id_unit_left; trivial.
      Qed.

      Next Obligation.
      Proof.
        symmetry.
        apply Another_Cone_Limit__The_Related_CoCone_aux_cone_to_Cn_obligation_1.
      Qed.        

      Next Obligation.
      Proof.
        apply NatTrans_eq_simplify.
        extensionality x.
        cbn.
        set (W :=
            f_equal
              (fun f :
                     ((Func_From_SingletonCat (ICT n'))
                        ∘ Functor_To_1_Cat (ω%omegacat ^op) –≻ ICT_Func)%nattrans
               => Trans f x)
              (cone_morph_com (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il n'))
            ).
        cbn in W.
        rewrite From_Term_Cat in W; cbn.
        rewrite MC_id_unit_left in W.
        rewrite From_Term_Cat; cbn.
        rewrite MC_id_unit_left.
        rewrite (MC_assoc_sym  M).
        unfold ICT_inv_Func, OmegaCat_Func, OmegaCat_Op_Func in *.
        cbn in *.
        rewrite <- W.
        clear W.
        {
          induction (le_Tle h) as [|m t IHt].
          {
            cbn; rewrite MC_id_unit_right; trivial.
          }
          {
            rewrite (IHt (Tle_le t)).
            cbn.
            rewrite (MC_assoc_sym).
            rewrite Cone_Limit__The_Related_CoCone_aux_cone_fun_S.
            trivial.
          }
        }
      Qed.

      Program Definition jn_o_in_cauchy (il : is_Limit _ Cn)
        : Cauchy_Sequence (MC_Hom M (Cn : M) (Cn : M)) :=
        {|
          CHS_seq :=
            fun n =>
              (MC_compose M)
                (Trans Cn n,
                 Trans (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il n) tt)
        |}.

      Next Obligation.
      Proof.
        apply Cauchy_condition_simpl.
        clear.
        intros ε.
        destruct (ICT_approach_id ICT ε) as [N H1].
        exists N.
        intros n H2.
        set (W := @Trans_com _ _ _ _ Cn _ _ (le_S _ _ (le_n n)));
          cbn in W; rewrite From_Term_Cat in W; cbn in W;
          rewrite MC_id_unit_right in W; rewrite W; clear W.
        cbn_rewrite (f_equal
               (fun f : (Func_From_SingletonCat (ICT _) –≻ Cn)%nattrans => Trans f tt)
               (isCLRKE_morph_unique
                  _
                  _
                  _
                  il
                  _
                  (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il _)
                  (Another_Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il _ _ (le_S _ _ (le_n n)))
               )
            ).
        rewrite MC_assoc.
        rewrite (MC_assoc_sym M _ _ _ _ _ ((ICT_Func _a)%morphism (le_S n n (le_n n)))).
        rewrite
          <- (MC_id_unit_right _ _ _ (Trans (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il (S n)) tt)) at 2.
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

      Program Definition limit_jn_o_in_forms_Cone_morph_from_Cn_to_Con
        (il : is_Limit _ Cn) :
        LoKan_Cone_Morph Cn Cn :=
        {|
          cone_morph :=
            {|
              Trans :=
                fun h =>
                  match h as u return (MC_Hom M ((Cn _o)%object u) ((Cn _o)%object u)) with
                  | tt =>
                    (CUM_complete _ (jn_o_in_cauchy il) : MC_Hom M (Cn : M) (Cn : M))
                  end
            |}
        |}.

      Next Obligation.
      Proof.
        repeat match goal with [H : unit|- _] => destruct H end.
        rewrite From_Term_Cat; cbn.
        rewrite MC_id_unit_left, MC_id_unit_right.
        trivial.
      Qed.

      Next Obligation.
      Proof.
        symmetry.
        apply limit_jn_o_in_forms_Cone_morph_from_Cn_to_Con_obligation_1.
      Qed.

      Next Obligation.
      Proof.
        apply NatTrans_eq_simplify.
        extensionality m.
        cbn.
        rewrite From_Term_Cat; cbn.
        rewrite MC_id_unit_left.
        set (z := CUM_complete (MC_Hom M (Cn : M) (Cn : M)) (jn_o_in_cauchy il)).
        rewrite (Limit_of_SubSeq_equal z m (Limit_of_SubSeq z m)).
        change (MC_compose M ((Limit_of_SubSeq z m) : MC_Hom _ _ _, Trans Cn m)) with
        (Lim (@NonExpansive_Continuous _ _ _ (Limit_of_SubSeq z m) _ (NonExpansive_Compose_right _ (Trans Cn m)))).
        match goal with
          [|- _ = Lim ?A] =>
          rewrite (Eq_Seq_Eq_Limits _ _ A (Limit_of_ConstSeq (Trans Cn m)))
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
            cutrewrite (A = (Cone_Limit__The_Related_CoCone_aux_cone_fun (m + n) m));
              [apply h_n_m_o_jn_eq_jm; trivial|apply jm_o_in__h_n_m]
          end.
          abstract omega.
        }
      Qed.
      
      Program Definition Cone_Limit__The_Related_CoCone
              (il : is_Limit _ Cn) : The_Related_CoCone :=
        {|
          TRCC_injs :=
            fun n =>
              Trans (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il n) tt
        |}.

      Next Obligation.
      Proof.
        rewrite (MC_id_unit_left M).
        apply (f_equal
               (fun f : (Func_From_SingletonCat (ICT c') –≻ Cn)%nattrans => Trans f tt)
               (isCLRKE_morph_unique
                  _
                  _
                  _
                  il
                  _
                  (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il c')
                  (Another_Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il _ _ h)
               )
            ).
      Qed.        

      Next Obligation.
      Proof.
        set (W := f_equal
                    (fun f :
                           ((Func_From_SingletonCat (ICT n))
                              ∘ Functor_To_1_Cat (ω%omegacat ^op) –≻ ICT_Func)%nattrans
                     => Trans f n)
                    (cone_morph_com (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn il n))
            ).
        cbn in W.
        rewrite From_Term_Cat in W; cbn in W; rewrite MC_id_unit_left in W.
        unfold Cone_Limit__The_Related_CoCone_aux_cone_fun in W.
        destruct gt_eq_gt_dec as [[|H]|]; try omega.
        destruct H.
        cbn in W.
        rewrite W.
        trivial.
      Qed.        
      
      Next Obligation.
      Proof.
        cutrewrite (
            @MC_id _ M (Cn : M) =
            (CUM_complete _ (jn_o_in_cauchy il) : MC_Hom M (Cn : M) (Cn : M))
          ).
        {
          apply (Lim_limit (CUM_complete _ (jn_o_in_cauchy il))).
        }
        {
          match goal with
            [|- ?A = ?B] =>
            change A with (Trans (cone_morph (LoKan_id_Cone_Morph _ _ Cn)) tt);
              change B with (Trans (cone_morph (limit_jn_o_in_forms_Cone_morph_from_Cn_to_Con il)) tt)
          end.
          rewrite (isCLRKE_morph_unique _ _ _ il _ (LoKan_id_Cone_Morph _ _ Cn) (limit_jn_o_in_forms_Cone_morph_from_Cn_to_Con il)).
          trivial.
        }          
      Qed.

    End Limits_Lemmas.

  End ICT_Func_Limit.
    
End IncreasingCauchyTower.
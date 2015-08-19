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

Require Import MCat.IncreasingCauchyTower.IncreasingCauchyTower.

Local Open Scope order_scope.
Local Open Scope metric_scope.
Local Open Scope lattice_scope.

Section Cone_Limit_Related_CoCone.
  Context {L : MLattice}
          (M : MCat L)
          (ICT : IncreasingCauchyTower M)
          (Cn : Cone (ICT_Func ICT))
          (il : is_Limit _ Cn)
  .

  Local Definition Cone_Limit__The_Related_CoCone_aux_cone_to_Cn n
    :=
      isCLRKE_morph_ex
        (Functor_To_1_Cat (ω%omegacat ^op)) (ICT_Func ICT) Cn il
        (Aux_cone ICT n)
  .
  
  Local Program Definition Another_Cone_Limit__The_Related_CoCone_aux_cone_to_Cn
        (n n': nat) (h : n ≤ n')
    :
      LoKan_Cone_Morph
        (Aux_cone ICT n)
        Cn :=
    {|
      cone_morph :=
        {|
          Trans :=
            fun w =>
              MC_compose M
                         ((ICT_inv_Func ICT _a)%morphism h,
                          (Trans (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn n') w)
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
                       ∘ Functor_To_1_Cat (ω%omegacat ^op) –≻ (ICT_Func ICT))%nattrans
              => Trans f x)
             (cone_morph_com (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn n'))
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
        rewrite Aux_cone_fun_S.
        trivial.
      }
    }
  Qed.
  
  Program Definition Cone_Limit__Interacts_With_Cn : CoCone_Interacting_With Cn :=
    {|
      CCIW_injs :=
        fun n =>
          Trans (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn n) tt
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
                (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn c')
                (Another_Cone_Limit__The_Related_CoCone_aux_cone_to_Cn _ _ h)
             )
          ).
  Qed.       

  Next Obligation.
  Proof.
    set (W := f_equal
                (fun f :
                       ((Func_From_SingletonCat (ICT n))
                          ∘ Functor_To_1_Cat (ω%omegacat ^op) –≻ (ICT_Func ICT))%nattrans
                 => Trans f n)
                (cone_morph_com (Cone_Limit__The_Related_CoCone_aux_cone_to_Cn n))
        ).
    cbn in W.
    rewrite From_Term_Cat in W; cbn in W; rewrite MC_id_unit_left in W.
    unfold Aux_cone_fun in W.
    destruct gt_eq_gt_dec as [[|H]|]; try omega.
    destruct H.
    cbn in W.
    rewrite W.
    trivial.
  Qed.

  Program Definition Cone_Limit_Related_CoCone : CoCone_Related_To Cn :=
    {|
      TRCC_CoCone := Cone_Limit__Interacts_With_Cn
    |}.
  
  Next Obligation.
  Proof.
    cutrewrite (
        @MC_id _ M (Cn : M) =
        (CUM_complete
           _
           (proj_n_o_inj_n_cauchy
              ICT
              Cn
              Cone_Limit__Interacts_With_Cn
              Cn
           ) : MC_Hom M (Cn : M) (Cn : M))
      ).
    {
      apply (Lim_limit
               (CUM_complete
                  _
                  (proj_n_o_inj_n_cauchy
                     ICT
                     Cn
                     Cone_Limit__Interacts_With_Cn
                     Cn
                  )
               )
            ).
    }
    {
      match goal with
        [|- ?A = ?B] =>
        change A with (Trans (cone_morph (LoKan_id_Cone_Morph _ _ Cn)) tt);
          change B with
          (Trans
             (cone_morph
                (
                  limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con
                    ICT
                    Cn
                    Cone_Limit__Interacts_With_Cn
                    Cn
                )
             )
             tt
          )
      end.
      rewrite (
          isCLRKE_morph_unique
            _
            _
            _
            il
            _
            (LoKan_id_Cone_Morph _ _ Cn)
            (
              limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con
                ICT
                Cn
                Cone_Limit__Interacts_With_Cn
                Cn
            )
        ).
      trivial.
    }
  Qed.

End Cone_Limit_Related_CoCone.
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
        Categories.KanExt.Local
        Categories.KanExt.LocalFacts.Uniqueness
        Categories.Limits.Limit
.
Require Import MCat.MCat.

Require Import MCat.IncreasingCauchyTower.IncreasingCauchyTower.

Local Open Scope order_scope.
Local Open Scope metric_scope.
Local Open Scope lattice_scope.

Section Related_CoCone_Cone_Limit.
  Context {L : MLattice}
          (M : MCat L)
          (ICT : IncreasingCauchyTower M)
          (Cn : Cone (ICT_Func ICT))
          (RCC : CoCone_Related_To Cn)
  .

  Theorem limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con_is_LoKan_id_Cone_Morph
    :
      limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con _ Cn RCC Cn =
      LoKan_id_Cone_Morph _ _ _
  .
  Proof.
    apply LoKan_Cone_Morph_eq_simplify.
    apply NatTrans_eq_simplify.
    extensionality x.
    destruct x.
    cbn.
    match goal with
      [|- ?A = ?B] =>
      change B with (Lim {|Lim := B; Lim_limit := TRCC_approach_id _ Cn RCC |})
    end.
    apply Limit_unique.
  Qed.    
  
  Definition Cone_Morph_to_Cn (Cn' : Cone (ICT_Func ICT)) : LoKan_Cone_Morph Cn' Cn :=
    limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con _ Cn RCC Cn'.

  Lemma Cone_Morph_to_Cn_Unique
        (Cn' : Cone (ICT_Func ICT)) (h : LoKan_Cone_Morph Cn' Cn)
    :
      h = Cone_Morph_to_Cn Cn' :> NatTrans _ _.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality x.
    destruct x.
    cbn.
    match goal with
      [|- ?A = Lim ?B] =>
      set (z := B)
    end.
    cut (
        proj_n_o_inj_n_cauchy ICT Cn RCC Cn' =
        (fun n : nat => (MC_compose M) (Trans h tt, (MC_compose M) (Trans Cn n, RCC n))) :> Sequence _
      ).
    {
      intros H.
      rewrite (
          Eq_Seq_Eq_Limits
            _
            _
            z
            (match H in _ = y return Metrics.Limit.Limit y with eq_refl => z end)
            H
        ).
      unfold z; clear z;
      match goal with
        [|- ?A = Lim ?B] =>
        rewrite (
            @NonExpansive_Continuous_eq
              _
              _
              _
              (CUM_complete _ (proj_n_o_inj_n_cauchy _ Cn RCC Cn))
              _
              (@NonExpansive_Compose_left _ _ _ _ Cn (Trans h tt))
              B
          )
      end.
      cbn_rewrite (f_equal (fun f : LoKan_Cone_Morph Cn Cn => Trans (cone_morph f) tt) limit_proj_n_o_inj_n_cauchy_forms_Cone_morph_from_Cn_to_Con_is_LoKan_id_Cone_Morph).
      cbn.
      rewrite MC_id_unit_left.
      trivial.
    }
    {
      extensionality n.
      cbn.
      rewrite MC_assoc.
      cbn_rewrite (f_equal
                  (fun f :
                         (Cn' ∘ Functor_To_1_Cat (ω%omegacat ^op) –≻ ICT_Func ICT)%nattrans
                   => Trans f n
                  )
                  (cone_morph_com h)).
      rewrite From_Term_Cat; cbn.
      rewrite MC_id_unit_left.
      trivial.
    }
  Qed.
    
  Program Definition Related_CoCone_Cone_Limit : is_Limit _ Cn :=
    {|
      isCLRKE_morph_ex := Cone_Morph_to_Cn
    |}.

  Next Obligation.
  Proof.
    rewrite (Cone_Morph_to_Cn_Unique _ h);
    rewrite (Cone_Morph_to_Cn_Unique _ h').
    trivial.
  Qed.    

End Related_CoCone_Cone_Limit.
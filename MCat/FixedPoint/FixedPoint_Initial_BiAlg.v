Require Import Coq.Arith.Compare_dec.

Require Import
        Essentials.Facts_Tactics
        Essentials.Notations
        Essentials.Types.

Require Import Metrics.Mappings Metrics.Cauchy Metrics.Mappings Metrics.Banach.
Require Import Metrics.Complete_UltraMetric.

Require Import
        Categories.Category.Main
        Categories.Functor.Main
        Categories.Ext_Cons.Prod_Cat.Prod_Cat
        Categories.Basic_Cons.Terminal
.
Require Import MCat.MCat.

Require Import MCat.MCat MCat.Opposite MCat.Product MCat.MFunc.

Require Import MCat.FixedPoint.BiAlgebra.

Section FixedPoint_Initial_BiAlg.
  Context {L : MLattice}
          {M : MCat L}
          (F : LocallyContractive (MCat_Prod (MCat_Op M) M) M)
          (MTerm : Terminal M)
          (starting_point :
             (
               (terminal MTerm)
                 –≻
                 (F _o (terminal MTerm, terminal MTerm))%object
             )%morphism
          )
  .

  (** The inhabited subcategory of M. *)
  Definition inhM := Full_SubCategory M (fun c => ((terminal MTerm) –≻ c)%morphism).

  Section inhM_Hom_inh.
    Context (a b : inhM).

    (** There always is an arrow from any a to any b in inhM. *)
    Definition inhM_Hom_inh : (a –≻ b)%morphism :=
      exist _ (MC_compose _ (t_morph MTerm (projT1 a), projT2 b)) I.

  End inhM_Hom_inh.
    
  (** F restricts to inhM. *)
  Program Definition inhF : (((inhM ^op) × inhM) –≻ inhM)%functor :=
    {|
      FO :=
        fun a =>
          existT
            _
            (F _o (projT1 (fst a), projT1 (snd a)))%object
            (MC_compose
               _
               (starting_point,
                ((F @_a (_, _) (_, _) (t_morph MTerm (projT1 (fst a)) , projT2 (snd a))))%morphism)
            );
      FA :=
        fun a b f =>
          exist _ (F @_a (_, _) (_, _) (proj1_sig (fst f), proj1_sig (snd f)))%morphism I;
      
      F_id :=
        fun a =>
          sig_proof_irrelevance
            _
            (exist _ _ _)
            (exist _ _ _)
            (F_id F (projT1 (fst a), projT1 (snd a)));
      F_compose :=
        fun a b c f g =>
          sig_proof_irrelevance
            _
            (exist _ _ _)
            (exist _ _ _)
            (@F_compose
               _
               _
               F
               (_, _)
               (_, _)
               (_, _)
               (proj1_sig (fst f), proj1_sig (snd f))
               (proj1_sig (fst g), proj1_sig (snd g))
            )
    |}.
  
  Context {A : inhM} (i : (inhF _o (A, A) ≃≃ A ::> inhM)%isomorphism).

  (** The BiAlgebra induced by A and i. *)
  Definition Ai_BiAlg : BiAlgebra inhF :=
    {|
      BiAlg_obj := A;
      BiAlg_from_obj := (inverse_morphism i);
      BiAlg_to_obj := (iso_morphism i)
    |}.

  Section Construct_BiAlg_Morph.
    Context (B : BiAlgebra inhF).

    (** The following is an operator D that maps a pair of arrows h : B –≻ A and
k : A –≻ B as follows: D(h, k) = (i ∘ F(h, k) ∘ g, f ∘ F(k, h) ∘ i⁻¹) where
f : F(B, B) –≻ B and g : B –≻ F(B, B) are the arrows forming bi-algebra B.

Here D is named Construct_BiAlg_Morph as it is used to create bi-algebra
morphisms.
     *)
    Program Definition Construct_BiAlg_Morph :
      Contractive
        (
          MC_Hom
            (MCat_Prod M (MCat_Op M))
            (projT1 (BiAlg_obj B), projT1 (BiAlg_obj B))
            (projT1 A, projT1 A)
        )
        (
          MC_Hom
            (MCat_Prod M (MCat_Op M))
            (projT1 (BiAlg_obj B), projT1 (BiAlg_obj B))
            (projT1 A, projT1 A)
        )
      :=
        {|
          CN_fun :=
            fun kh =>
              (
                (
                  MC_compose
                    _
                    (
                      MC_compose
                        _
                        (
                          (proj1_sig (BiAlg_from_obj B)),
                          (F @_a (_, _) (_, _) (snd kh, fst kh))%morphism
                        )
                      ,
                      proj1_sig (iso_morphism i)
                    )
                )
                ,
                (
                  MC_compose
                    _
                    (
                      MC_compose
                        _
                        (
                          (proj1_sig (inverse_morphism i)),
                          (F @_a (_, _) (_, _) (fst kh, snd kh))%morphism
                        )
                      ,
                      (proj1_sig (BiAlg_to_obj B))
                    )
                )
              );
          CN_ContrRate := LCN_ContrRate _ _ F
        |}.

    Next Obligation.
    Proof.
      repeat (apply lub_lst; intros [];
              try (eapply PO_Trans; [apply NE_non_expansive |]));
      cbn; try rewrite UM_eq_zero_dist; trivial;
      (eapply PO_Trans;
       [apply (@CCN_contractive _ _ _ _ (@LCN_FA _ _ _ F _ _))|]); trivial;
      rewrite lub_sym; trivial.
    Qed.

    (** A fixed point of D gives a bi-algebra morphism from Ai_BiAlg to B. *)
    Section fixedpoint_of_Construct_BiAlg_Morph_forms_BiAlg_Morph.
      Context
        (h : ((projT1 (BiAlg_obj B)) –≻ (projT1 A))%morphism)
        (k : ((projT1 A) –≻ (projT1 (BiAlg_obj B)))%morphism)
        (fx : Construct_BiAlg_Morph (h, k) = (h, k))
      .

      Local Obligation Tactic := idtac.
      
      Program Definition fixedpoint_of_Construct_BiAlg_Morph_forms_BiAlg_Morph :
        BiAlg_Morph Ai_BiAlg B :=
        {|
          BAM_forward := exist _ k I;
          BAM_backward := exist _ h I
        |}.

      Next Obligation.
      Proof.
        basic_simpl.
        apply sig_proof_irrelevance; cbn.
        set (W := f_equal snd fx); cbn in W; rewrite <- W at 2; clear W.
        rewrite MC_assoc_sym.
        rewrite MC_assoc.
        cbn_rewrite (f_equal (fun x : sig _ => proj1_sig x) (left_inverse i)).
        rewrite MC_id_unit_right; trivial.
      Qed.

      Next Obligation.
      Proof.
        basic_simpl.
        apply sig_proof_irrelevance; cbn.
        set (W := f_equal fst fx); cbn in W; rewrite <- W at 2; clear W.
        rewrite MC_assoc_sym.
        cbn_rewrite (f_equal (fun x : sig _ => proj1_sig x) (left_inverse i)).
        rewrite MC_id_unit_left; trivial.
      Qed.

    End fixedpoint_of_Construct_BiAlg_Morph_forms_BiAlg_Morph.

    (** A bi-algebra morphism from Ai_BiAlg to B gives a fixed point of D. *)
    Section BiAlg_Morph_forms_fixedpoint_of_Construct_BiAlg_Morph.
      Context
        (m : BiAlg_Morph Ai_BiAlg B)
      .

      Local Obligation Tactic := idtac.
      
      Theorem BiAlg_Morph_forms_fixedpoint_of_Construct_BiAlg_Morph :
        Construct_BiAlg_Morph
          (proj1_sig (BAM_backward m), proj1_sig (BAM_forward m)) =
        (proj1_sig (BAM_backward m), proj1_sig (BAM_forward m))
      .
      Proof.
        basic_simpl.
        repeat rewrite MC_assoc_sym.
        cbn_rewrite (f_equal (fun x : sig _ => proj1_sig x) (BAM_forward_com m)).
        repeat rewrite MC_assoc.
        cbn_rewrite (f_equal (fun x : sig _ => proj1_sig x) (BAM_backward_com m)).
        cbn_rewrite (f_equal (fun x : sig _ => proj1_sig x) (right_inverse i)).
        repeat rewrite MC_assoc_sym.
        cbn_rewrite (f_equal (fun x : sig _ => proj1_sig x) (right_inverse i)).
        rewrite MC_id_unit_right, MC_id_unit_left; trivial.
      Qed.

    End BiAlg_Morph_forms_fixedpoint_of_Construct_BiAlg_Morph.
    
  End Construct_BiAlg_Morph.
    
  Program Definition FixedPoint_Initial_BiAlg : Initial (BiAlg_Cat inhF) :=
    {|
      terminal := Ai_BiAlg;
      t_morph :=
        fun d =>
          fixedpoint_of_Construct_BiAlg_Morph_forms_BiAlg_Morph
            d
            _
            _
            (
              Banach_is_FixedPoint
                (
                  Product.product_CUM
                    (MC_Hom M (projT1 (BiAlg_obj d)) (projT1 A))
                    (MC_Hom M (projT1 A) (projT1 (BiAlg_obj d)))
                )
                (proj1_sig (inhM_Hom_inh d A), proj1_sig (inhM_Hom_inh A d))
                (Construct_BiAlg_Morph d)
            )
    |}.

  Next Obligation.
    set (W :=
           Banach_unique
             _
             (Construct_BiAlg_Morph d)
             _
             _
             (BiAlg_Morph_forms_fixedpoint_of_Construct_BiAlg_Morph d f)
             (BiAlg_Morph_forms_fixedpoint_of_Construct_BiAlg_Morph d g)
        ).
    clearbody W.
    apply BiAlg_Morph_eq_simplify;
    destruct (BAM_forward f);
    destruct (BAM_backward f);
    destruct (BAM_forward g);
    destruct (BAM_backward g);
    apply sig_proof_irrelevance.
    apply (f_equal snd W).
    apply (f_equal fst W).
  Qed.    
  
End FixedPoint_Initial_BiAlg.
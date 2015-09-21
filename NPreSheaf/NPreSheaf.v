Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Arith.Compare_dec.

Require Import Essentials.Types.
Require Import Essentials.Arith.
Require Import Essentials.Omega.
Require Import Essentials.Facts_Tactics.
Require Import Metrics.Mappings.
Require Import Metrics.Complete_UltraMetric.
Require Import Metrics.CBULt.Product.
Require Import Bisected.Bisected.
Require Import MCat.MCat.

Require Import Categories.Category.Main.
Require Import Categories.Functor.Main.
Require Import Categories.NatTrans.Main.
Require Import Categories.Archetypal.PreOrder_Cat.OmegaCat.
Require Import Categories.PreSheaf.PreSheaf.

Local Open Scope omegacat_scope.

(** Propositional extensionality assumed locally. *)
Local Axiom PropExt : prop_extensionality.

(** We construct the M-category of presheaves on natural numbers *)
Section NPreSheaf_Hom.
  Context (F G : PShCat ω).

  (** The homomorphisms of presheaf categories are natrual transformations.
In this case, natrual transformations induce a functions from naturla numbrs
to functions (morphisms in Type_Cat).

We define the distance between two such natural transformation to be the bi-sected
distance such that distance between f and g is (1/2)ⁿ if they agree on the first n
elements, i.e., ∀ i ≤ n, f n = g n.

We show that the space of homomorphisms form a complete ultra metric space.
 *)
  Section NPreSheaf_Hom_Dist.
    Context (N N' : (F –≻ G)%nattrans).

    (** The basic definition of distance between morphisms as discussed above. *)
    Program Definition NPreSheaf_Hom_Dist : BiDist :=
      {|
        BD_agree := fun n => ∀ m : nat, m ≤ n → ((Trans N m) = (Trans N' m))%object;
        BD_decreases := fun n m H1 H2 x H3 => _
      |}.

    Next Obligation.
    Proof.
      apply H2.
      apply le_Tle.
      apply Tle_le in H3.
      omega.
    Qed.

  End NPreSheaf_Hom_Dist.

  (** Morphisms form an ultra metric space on top of disected distances. *)
  Program Definition NPreSheaf_Hom_UM : UltraMetric BiDistML :=
    {|
      UM_Carrier := @Hom (PShCat ω) F G;
      UM_distance := NPreSheaf_Hom_Dist
    |}.

  Next Obligation.
  Proof.
    apply BiDist_eq_simpl.
    extensionality n.
    apply PropExt; split; intros H1 m H2; symmetry; auto.
  Qed.        

  Next Obligation.
  Proof.
    apply BiDist_eq_simpl.
    extensionality n.
    cbn.
    apply PropExt; intuition.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality n.
    cbn in *.
    assert (H' : (∀ m : nat, m ≤ n → Trans x m = Trans y m)).
    {
      refine
        (
          match eq_sym (f_equal (fun w => BD_agree w n) H) in _ = y
                return y
          with
            eq_refl => _
          end
        ).
      cbn; trivial.
    }
    {
      apply H'; constructor.
    }
  Qed.

  Next Obligation.
  Proof.      
    intros w.
    intros H.
    assert (H1 := H true).
    assert (H2 := H false).
    clear H.
    cbn in *.
    intros m H3.
    etransitivity; [apply H1|apply H2]; trivial.
  Qed.

  (** Given a cauchy sequence of morphisms, we construct its limit.

For the nth element of the limit (remember that morphisms are natrual
transformations from category of natural numbers) we take the nth element
of the element in the sequence where it is guaranteed that the elements of
the sequence agree on the first n+1 elements.
 *)
  Program Definition NPreSheaf_Hom_complete
          (chs : Cauchy_Sequence NPreSheaf_Hom_UM) :
    (F –≻ G)%nattrans
    :=
      {|
        Trans :=
          fun n =>
            Trans
              (
                CHS_seq
                  _
                  chs
                  (proj1_sig (CHS_cauchy _ chs (existT _ _ (Appr_Half_Pow (S n)))))
              )
              n
      |}.

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros chs c c' h.
    extensionality x.
    cbn in *.
    cbn_rewrite
      <-
      (
        equal_f
          (
            Trans_com
              (
                CHS_seq
                  _
                  chs
                  (proj1_sig (CHS_cauchy _ chs (existT _ _ (Appr_Half_Pow (S c)))))
              )
              h
          )
          x
      ).
    match goal with
      [|- Trans ?A ?x ?y = Trans ?B ?x ?y] =>
      cutrewrite (Trans A x = Trans B x); trivial
    end.
    match goal with
      [|- Trans (CHS_seq _ chs (proj1_sig ?A)) ?x = Trans (CHS_seq _ chs (proj1_sig ?B)) ?x] =>
      set (W := A);
        set (V := B)
    end.
    match goal with
      [|- Trans ?A ?x = Trans ?B ?x] =>
      cut (∂(A, B)%metric ⊏ (BD_Half_pow (S c')))%order; [intros H|]
    end.
    {
      destruct H as [H1 H2].
      cbn in *.
      apply (H1 c'); trivial.
      apply BD_Half_pow_Sn_n.
    }        
    {
      destruct (le_lt_dec (proj1_sig W) (proj1_sig V)).
      {      
        destruct W as [z Hw]; cbn in *.
        apply Hw; auto.
      }
      {
        destruct V as [z Hw]; cbn in *.
        eapply LT_LE_Trans; [|apply (BD_Half_pow_monotone _ _ (Tle_le (Tle_addS _ _ h)))].
        apply Hw; [omega|trivial].
      }
    }          
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply NPreSheaf_Hom_complete_obligation_1.
  Qed.      

  (** Homomorphisms form a complete ultra metric space.
We have formerly shown that it is an ultra metric space.
Now we show that the limit defined above is indeed the limit
of the given cauchy sequence. *)
  Program Definition NPreSheaf_Hom : Complete_UltraMetric BiDistML :=
    {|
      CUM_UM := NPreSheaf_Hom_UM;
      CUM_complete :=
        fun chs =>
          {|
            Lim := NPreSheaf_Hom_complete chs
          |}
    |}.

  Next Obligation.
  Proof.
    intros chs ε.
    destruct (BD_dichotomy_left _ (projT2 ε)) as [e H1 [H21 H22]].
    destruct (BD_dichotomy_left _ H1) as [e' H1' [H21' H22']].
    destruct (CHS_cauchy _ chs (existT _ _ H1')) as [N H].
    exists N.
    intros n H'.
    eapply LE_LT_Trans; [|apply H22].
    intros m H3 k H4.
    cbn in *.
    match goal with
      [|- Trans _ ?x = Trans (CHS_seq _ chs (proj1_sig ?A)) ?x] =>
      set (W := A)
    end.
    match goal with
      [|- Trans ?A ?x = Trans ?B ?x] =>
      cut (∂(A, B)%metric ⊏ (BD_Half_pow (S k)))%order; [intros H5|]
    end.
    {
      destruct H5 as [H51 H52].
      cbn in *.
      apply (H51 k); trivial.
      apply BD_Half_pow_Sn_n.
    }      
    {
      destruct (le_lt_dec (proj1_sig W) N).
      {
        destruct W as [z Hw]; cbn in *.
        apply Hw; auto.
        omega.
      }
      {
        cbn in *.
        eapply LT_LE_Trans;
          [|apply
              (BD_Half_of_monotone
                 _
                 _
                 (BD_LE_Trans
                    _
                    _
                    _
                    (Less_than_BD_Half_pow e _ H3)
                    (BD_Half_pow_monotone _ _ (Tle_le H4))
                 )
              )
          ].
        eapply LT_LE_Trans;
          [|apply (Strictly_less_less_than_BD_pos_half_pos _ _ H22' H1' H1)
          ].
        apply H; trivial.
        omega.
      }          
    }          
  Qed.

End NPreSheaf_Hom.

(** We show that the composition function of the presheaf category on
natural numbers is non-expansive. *)
Program Definition NPreSheaf_Hom_compose
        (a b c : PreSheaf ω)
  :
    NonExpansive
      (product_UM (NPreSheaf_Hom a b) (NPreSheaf_Hom b c))
      (NPreSheaf_Hom_UM a c)
  :=
    {|
      NE_fun :=
        fun x => ((snd x) ∘ (fst x))%morphism
    |}.

Next Obligation.
Proof.
  intros n H1 m H2.
  assert (H11 := H1 true).
  assert (H12 := H1 false).
  clear H1.
  cbn in *.
  extensionality x.
  rewrite H11; trivial.
  rewrite H12; trivial.
Qed.    

(** All these put together gives us the M-category of presheaves
on natural numbers. *)
Program Definition NPreSheaf : MCat BiDistML :=
  {|
    MC_Obj := PShCat ω;
    MC_Hom := NPreSheaf_Hom;
    MC_compose := NPreSheaf_Hom_compose;
    MC_assoc := @assoc (PShCat ω);
    MC_assoc_sym := @assoc_sym (PShCat ω);
    MC_id := @id (PShCat ω);
    MC_id_unit_left := @id_unit_left (PShCat ω);
    MC_id_unit_right := @id_unit_right (PShCat ω)
  |}.

(** The category underlying the M-category defined is indeed the
category of presheaves on natural numbers. *)
Goal (NPreSheaf = (PShCat ω) :> Category).
  reflexivity.
Abort.

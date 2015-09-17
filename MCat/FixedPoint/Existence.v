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
        Categories.Basic_Cons.Terminal
.
Require Import MCat.MCat.

Require Import MCat.MCat MCat.Opposite MCat.Product MCat.MFunc
        MCat.IncreasingCauchyTower.IncreasingCauchyTower
        MCat.IncreasingCauchyTower.Related_CoCone_Cone_Limit
        MCat.IncreasingCauchyTower.Cone_Limit_Related_CoCone
        MCat.IncreasingCauchyTower.Ops_and_Props.

Local Open Scope order_scope.
Local Open Scope metric_scope.
Local Open Scope lattice_scope.

(** We show that any locally-contractive functor F : Mᵒᵖ × M –≻ M where
M is an M-category has a fixed point (an object A such that F(A, A) ≃ A).
*)
Section Existence.
  Context {L : MLattice}
          {M : MCat L}
          (limits_of_ICT : ∀ ICT : IncreasingCauchyTower M, Limit (ICT_Func ICT))
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
  
  Fixpoint ICT_of_Locally_Contractive_Func_obj (n : nat) : M :=
    match n with
      | O => terminal MTerm
      | S n' =>
        (F _o
          (
            ICT_of_Locally_Contractive_Func_obj n',
            ICT_of_Locally_Contractive_Func_obj n'
          ))%object
    end.

  Fixpoint ICT_of_Locally_Contractive_Func_gs (n : nat) :
    ((ICT_of_Locally_Contractive_Func_obj (S n))
      –≻
      (ICT_of_Locally_Contractive_Func_obj n))%morphism
    :=
    match n with
      | O => t_morph MTerm _
      | S n' =>
        F @_a
          (_, _)
          (_, _)
          (
            ICT_of_Locally_Contractive_Func_fs n',
            ICT_of_Locally_Contractive_Func_gs n'
          )
    end
  with
  ICT_of_Locally_Contractive_Func_fs (n : nat) :
    ((ICT_of_Locally_Contractive_Func_obj n)
      –≻
      (ICT_of_Locally_Contractive_Func_obj (S n)))%morphism
    :=
    match n with
      | O => starting_point
      | S n' =>
        F @_a
          (_, _)
          (_, _)
          (
            ICT_of_Locally_Contractive_Func_gs n',
            ICT_of_Locally_Contractive_Func_fs n'
          )
    end
  .

  (** We show that given a locally contractive functor F : Mᵒᵖ × M –≻ M, we can build an
increasing cauchy tower:
#
<pre>

     f₀                 F(g₀, f₀)
   <————               ———–——————>                    <.......
A₀       A₁ = F(A₀,A₀)              A₂ = F(A₁,A₁)     .......
   ————>               —————————–>                    .......>
    g₀                  F(f₀, g₀)
</pre>
#
where f₀ = 1 is the terminal object of M and g₀ is the starting point
(a morphims from 1 to F (1,1) ).
*)
  Program Definition ICT_of_Locally_Contractive_Func :
    IncreasingCauchyTower M :=
    {|
      ICT_Objs := ICT_of_Locally_Contractive_Func_obj;
      ICT_fs := ICT_of_Locally_Contractive_Func_fs;
      ICT_gs := ICT_of_Locally_Contractive_Func_gs
    |}.

  Next Obligation.
  Proof.
    induction n; cbn.
    apply (t_morph_unique MTerm).
    cbn_rewrite <- (@F_compose _ _ F); cbn.
    rewrite IHn.
    apply (@F_id _ _ F).
  Qed.

  Next Obligation.
  Proof.
    destruct (CR_rate_indicator (LCN_ContrRate _ _ F) ε (existT _ _ (ML_appr_top L))) as [N H2].
    exists N.
    intros n H3.
    cbn in *.
    eapply LE_LT_Trans; [|apply H2].
    clear H2.
    induction H3.
    {
      induction N.
      + cbn; trivial.
      + cbn.
        cbn_rewrite <- (@F_compose _ _ F); cbn.
        cbn_rewrite <- (@F_id _ _ F); cbn.
        eapply PO_Trans; [eapply (CCN_contractive (@LCN_FA _ _ _ F _ _))|]; cbn.
        apply (CR_monotone (LCN_ContrRate _ _ F)).
        apply lub_lst; intros []; trivial.
    }        
    {
      cbn.
      cbn_rewrite <- (@F_compose _ _ F); cbn.
      cbn_rewrite <- (@F_id _ _ F); cbn.
      eapply PO_Trans; [eapply (CCN_contractive (@LCN_FA _ _ _ F _ _))|]; cbn.
      eapply PO_Trans; [|apply (CR_non_expansive (LCN_ContrRate _ _ F))].
      apply (CR_monotone (LCN_ContrRate _ _ F)).
      apply lub_lst; intros []; trivial.
    }        
  Qed.

  (** The limit of the cauchy tower of a contractive functor is its fixed point. *)
  Definition FixedPoint :
    (
      F _o
        (
          (limits_of_ICT ICT_of_Locally_Contractive_Func : M),
          (limits_of_ICT ICT_of_Locally_Contractive_Func : M)
        )
        ≃ (limits_of_ICT ICT_of_Locally_Contractive_Func)
    )%isomorphism
  .
  Proof.
    match goal with
      [|- (?A ≃ _)%isomorphism ] =>
      change A with
      (
        (is_Limit_Limit
           _
           (is_Limit_Cone_To_Locally_Contractive_Func_ICT_is_Limit
              _
              F
              _
              (Cone_Limit_Related_CoCone
                 _
                 _
                 (limits_of_ICT ICT_of_Locally_Contractive_Func)
                 (@Limit_is_Limit
                    _
                    _
                    _
                    (limits_of_ICT ICT_of_Locally_Contractive_Func)
                 )
              )
           )
        ) : M
      )
    end.
    match goal with
      [|- (_ ≃ ?A)%isomorphism ] =>
      change A with
      (
        (is_Limit_Limit
           _
           (is_Limit_Cone_To_ICT_Shift_One_is_Limit
              _
              (limits_of_ICT ICT_of_Locally_Contractive_Func)
              (Cone_Limit_Related_CoCone
                 _
                 _
                 (limits_of_ICT ICT_of_Locally_Contractive_Func)
                 (@Limit_is_Limit
                    _
                    _
                    _
                    (limits_of_ICT ICT_of_Locally_Contractive_Func)
                 )
              )
           )
          ) : M
      )
    end.
    apply LoKan_Cone_Iso_object_Iso.
    apply Local_Right_KanExt_unique.
  Defined.

End Existence.
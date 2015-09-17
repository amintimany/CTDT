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
        Categories.Limits.Limit
        Categories.KanExt.Local
.
Require Import
        MCat.MCat
        MCat.IncreasingCauchyTower.IncreasingCauchyTower
        MCat.IncreasingCauchyTower.Cone_Limit_Related_CoCone
.

Require Import MCat.MCat MCat.Opposite MCat.Product MCat.MFunc.

Require Import
        MCat.FixedPoint.BiAlgebra
        MCat.FixedPoint.FixedPoint_Initial_BiAlg
        MCat.FixedPoint.Existence
.

Section FixedPoint_Unique.
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

  (** Local abreviations for more readability. *)
  Local Notation inhM := (inhM MTerm).
  Local Notation inhF := (inhF F MTerm starting_point).

  Context
    {A : inhM}
    (Ai : (inhF _o (A, A) ≃≃ A ::> inhM)%isomorphism)
    {B : inhM}
    (Bi : (inhF _o (B, B) ≃≃ B ::> inhM)%isomorphism)
  .

  (** Fixed points are unique. *)
  Theorem FixedPoint_Unique : (A ≃≃ B ::> inhM)%isomorphism.
  Proof.
    apply (@BiAlg_iso_obj_iso _ _ (Ai_BiAlg _ _ _ Ai) (Ai_BiAlg _ _ _ Bi)).
    apply (@CoIso ((BiAlg_Cat inhF)^op)%category).
    apply (@Terminal_iso
             _
             (FixedPoint_Initial_BiAlg _ _ _ Ai)
             (FixedPoint_Initial_BiAlg _ _ _ Bi)
          ).
  Defined.

  Context (limits_of_ICT : ∀ ICT : IncreasingCauchyTower M, Limit (ICT_Func ICT)).

  (** Abbreviation for more readability. *)
  Local Notation FixedPoint := (FixedPoint limits_of_ICT F MTerm starting_point).
  Local Notation FixedPoint_as_limit := (FixedPoint_as_limit limits_of_ICT F MTerm starting_point).
  
  Definition Inhabitant_of_Existing_FixedPoint :
    (MTerm –≻ FixedPoint)%morphism
    :=
      Trans
        (cone_edge
           (CCIW_CoCone
              _
              _
              (TRCC_CoCone
                 _
                 _
                 (@Cone_Limit_Related_CoCone
                    _
                    _
                    _
                    _
                    (@Limit_is_Limit _ _ _ FixedPoint_as_limit)
                 )
              )
           )
        )
        0
  .

  Definition Existing_FixedPoint_in_inhM : inhM :=
    existT _ FixedPoint Inhabitant_of_Existing_FixedPoint.
  
End FixedPoint_Unique.
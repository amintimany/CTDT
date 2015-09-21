Require Import
        Essentials.Facts_Tactics
        Essentials.Notations
        Essentials.Types.
Require Import Metrics.Mappings.
Require Import Metrics.Complete_UltraMetric.
Require Import Categories.Category.Main.
Require Import Categories.Functor.Main.
Require Import MCat.MCat.

Section MFunc.
  Context {L : MLattice} (M M' : MCat L).

  (** A locally non-expansive functor is one whose arrow map
is non-expansive. *)
  Record LocallyNonExpansive : Type :=
    {
      LNE_FO : M → M';
      LNE_FA : ∀ {a b},
          NonExpansive
            (MC_Hom M a b)
            (MC_Hom M' (LNE_FO a) (LNE_FO b));
      LNE_F_id :
        ∀ a, LNE_FA (@MC_id _ M a) = @MC_id _ M' (LNE_FO a);
      LNE_F_compose :
        ∀ a b c (f : MC_Hom M a b) (g : MC_Hom M b c),
          LNE_FA (MC_compose M (f, g)) =
          MC_compose M' (LNE_FA f, LNE_FA g);
      LNE_Func :> Functor M M' :=
        {|
          FO := LNE_FO;
          FA := @LNE_FA;
          F_id := LNE_F_id;
          F_compose := LNE_F_compose
        |}
    }.

    (** A locally contractive functor is one whose arrow map
is contractive. *)
  Record LocallyContractive : Type :=
    {
      LCN_FO : M → M';
      LCN_ContrRate : ContrRate L;
      LCN_FA : ∀ {a b},
          Controlled_Contractive
            LCN_ContrRate
            (MC_Hom M a b)
            (MC_Hom M' (LCN_FO a) (LCN_FO b));
      LCN_F_id :
        ∀ a, LCN_FA (@MC_id _ M a) = @MC_id _ M' (LCN_FO a);
      LCN_F_compose :
        ∀ a b c (f : MC_Hom M a b) (g : MC_Hom M b c),
          LCN_FA (MC_compose M (f, g)) =
          MC_compose M' (LCN_FA f, LCN_FA g);
      LCN_Func :> Functor M M' :=
        {|
          FO := LCN_FO;
          FA := @LCN_FA;
          F_id := LCN_F_id;
          F_compose := LCN_F_compose
        |}
    }.

End MFunc.

(** The result of composition of a locally contractive functor and a locally
non-expansive functor is locally contractive. *)
Section LContr_LNE_Comp.
  Context
    {L : MLattice}
    {M M' M'' : MCat L}
    (F : LocallyContractive M M')
    (G : LocallyNonExpansive M' M'')
  .

  Program Definition LContr_LNE_Comp : LocallyContractive M M'' :=
    {|
      LCN_FO := ((G ∘ F)%functor _o)%object;
      LCN_ContrRate := LCN_ContrRate _ _ F;
      LCN_FA :=
        fun a b =>
        Contractive_Controlled_Contractive
          (
            NonExp_Contr_Contr
              (Controlled_Contractive_Contractive (@LCN_FA _ _ _ F a b))
              (@LNE_FA _ _ _ G (LCN_FO _ _ F a) (LCN_FO _ _ F b))
          );
      LCN_F_id := F_id (G ∘ F)%functor;
      LCN_F_compose := @F_compose _ _ (G ∘ F)%functor
    |}.

  (** Checking that the underlying functor of LContr_LNE_Comp is the composition of 
individual functors. *)
  Goal (LContr_LNE_Comp = (G ∘ F)%functor :> Functor _ _).
    reflexivity.
  Abort.

End LContr_LNE_Comp.

(** The result of composition of a locally non-expansive functor and a locally
contractive functor is locally contractive. *)
Section LNE_LContr_Comp.
  Context
    {L : MLattice}
    {M M' M'' : MCat L}
    (F : LocallyNonExpansive M M')
    (G :  LocallyContractive M' M'')
  .

  Program Definition LNE_LContr_Comp : LocallyContractive M M'' :=
    {|
      LCN_FO := ((G ∘ F)%functor _o)%object;
      LCN_ContrRate := LCN_ContrRate _ _ G;
      LCN_FA :=
        fun a b =>
        Contractive_Controlled_Contractive
          (
            Contr_NonExp_Contr
              (@LNE_FA _ _ _ F a b)
              (Controlled_Contractive_Contractive (@LCN_FA _ _ _ G (@LNE_FO _ _ _ F a) (@LNE_FO _ _ _ F b)))
          );
      LCN_F_id := F_id (G ∘ F)%functor;
      LCN_F_compose := @F_compose _ _ (G ∘ F)%functor
    |}.

  (** Checking that the underlying functor of LNE_LContr_Comp is the composition of 
individual functors. *)
  Goal (LNE_LContr_Comp = (G ∘ F)%functor :> Functor _ _).
    reflexivity.
  Abort.    
    
End LNE_LContr_Comp.
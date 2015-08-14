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
      LCN_FA : ∀ {a b},
          Contractive
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
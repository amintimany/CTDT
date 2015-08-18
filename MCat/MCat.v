Require Import
        Essentials.Types.
Require Import Metrics.Mappings.
Require Import Metrics.Complete_UltraMetric.
Require Import Metrics.CBULt.Product.
Require Import Categories.Category.Main.

Section MCat.
  Context {L : MLattice}.

  (** An M-category is a category where each hom-set forms a complete
ultra metric space and composition function is non-expansive (where the
domain of composition is the product of complete ultra metric spaces).

In addition, an M-category must have a terminal object.
 *)
  Record MCat : Type :=
    {
      MC_Obj : Type;
      MC_Hom : MC_Obj → MC_Obj → (Complete_UltraMetric L);
      MC_compose :
        ∀ {a b c : MC_Obj},
          NonExpansive
            (product_CUM (MC_Hom a b) (MC_Hom b c))
            (MC_Hom a c)
      where "g ∘ f" := (MC_compose (f, g));
      MC_assoc :
        ∀ (a b c d : MC_Obj)
          (f : MC_Hom a b)
          (g : MC_Hom b c) 
          (h : MC_Hom c d),
          (h ∘ g) ∘ f = h ∘ (g ∘ f);
      MC_assoc_sym :
        ∀ (a b c d : MC_Obj)
          (f : MC_Hom a b)
          (g : MC_Hom b c) 
          (h : MC_Hom c d),
          h ∘ (g ∘ f) = (h ∘ g) ∘ f;
      MC_id : ∀ {a : MC_Obj}, MC_Hom a a;
      MC_id_unit_left :
        ∀ (a b : MC_Obj)
          (h : MC_Hom a b),
          MC_id ∘ h = h;
      MC_id_unit_right :
        ∀ (a b : MC_Obj)
          (h : MC_Hom a b),
          h ∘ MC_id = h;
      MC_Cat :> Category :=
        {|
          Obj := MC_Obj;
          Hom := MC_Hom;
          compose := fun _ _ _ x y => MC_compose (x, y);
          assoc := MC_assoc;
          assoc_sym := MC_assoc_sym;
          id := @MC_id;
          id_unit_left := MC_id_unit_left;
          id_unit_right := MC_id_unit_right
        |}
    }.

End MCat.

Arguments MCat _ : clear implicits.

Section NonExpansive_Compose_left.
  Context {L : MLattice} (M : MCat L) {a b c : M} (f : MC_Hom M a b).

  Program Definition NonExpansive_Compose_left :
    NonExpansive (MC_Hom M b c) (MC_Hom M a c)
    :=
    {|
      NE_fun := fun u : MC_Hom M b c => MC_compose M (f, u)
    |}.

  Next Obligation.
  Proof.
    eapply PO_Trans; [apply NE_non_expansive|].
    cbn.
    rewrite UM_eq_zero_dist.
    rewrite lub_sym.
    rewrite lub_bot.
    trivial.
  Qed.

End NonExpansive_Compose_left.

Section NonExpansive_Compose_right.
  Context {L : MLattice} (M : MCat L) {a b c : M} (g : MC_Hom M b c).

  Program Definition NonExpansive_Compose_right :
    NonExpansive (MC_Hom M a b) (MC_Hom M a c)
    :=
    {|
      NE_fun := fun u : MC_Hom M a b => MC_compose M (u, g)
    |}.

  Next Obligation.
  Proof.
    eapply PO_Trans; [apply NE_non_expansive|].
    cbn.
    rewrite UM_eq_zero_dist.
    rewrite lub_bot.
    trivial.
  Qed.

End NonExpansive_Compose_right.
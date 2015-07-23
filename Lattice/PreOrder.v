Require Import Coq.Sets.Ensembles.
Require Export Essentials.Notations.

Local Open Scope order_scope.

(** Basic Definition of a preorder relation. *)
Record PreOrder : Type :=
  {
    PE_Carrier :> Type;
    PE_LE : PE_Carrier → PE_Carrier → Prop where "x ⊑ y" := (PE_LE x y);
    PE_Refl : ∀ x, x ⊑ x;
    PE_ASym : ∀ x y, x ⊑ y → y ⊑ x → x = y;
    PE_Trans : ∀ x y z, x ⊑ y → y ⊑ z → x ⊑ z
  }
.

Arguments PE_Carrier _ : assert.
Arguments PE_LE {_} _ _, _ _ _.
Arguments PE_Refl {_} _.
Arguments PE_ASym {_} _ _ _ _.
Arguments PE_Trans {_} _ _ _ _ _.

Notation "x ⊑ y" := (PE_LE x y) : order_scope.

Definition PE_LT {p : PreOrder} (x y : p) := (x ⊑ y)%order ∧ x ≠ y.

Notation "x ⊏ y" := (PE_LT x y) : order_scope.

(** Greatest lower bound and least upper bound in a preorder. *)
Section LUB_GLB.
  Context {A : PreOrder}.

  Section Generalized.
    Context (P : A → Prop).
    
    Record LUB :=
      {
        lub : A;
        lub_ub : ∀ (x : A), P x → x ⊑ lub;
        lub_lst : ∀ (ub : A), (∀ (x : A), P x → x ⊑ ub) → lub ⊑ ub
      }
    .

    Record GLB :=
      {
        glb : A;
        glb_lb : ∀ (x : A), P x → glb ⊑ x;
        glb_grst : ∀ (lb : A), (∀ (x : A), P x → lb ⊑ x) → lb ⊑ glb
      }
    .

  End Generalized.

  Notation "⊔ᵍ Q" := (LUB Q) : order_scope.
  
  Notation "⊓ᵍ Q" := (GLB Q) : order_scope.

  Definition LUB_Pair (x y : A) := (⊔ᵍ (Couple _ x y)).

  Definition GLB_Pair (x y : A) := (⊓ᵍ (Couple _ x y)).

End LUB_GLB.

Notation "⊔ᵍ Q" := (LUB Q) : order_scope.

Notation "⊓ᵍ Q" := (GLB Q) : order_scope.

Notation "x ⊔ y" := (LUB_Pair x y) : order_scope.
  
Notation "x ⊓ y" := (GLB_Pair x y) : order_scope.
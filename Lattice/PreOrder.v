Require Import Coq.Program.Tactics.
Require Import Coq.Sets.Ensembles.
Require Export Essentials.Notations.

Local Open Scope order_scope.

(** Basic Definition of a preorder relation. *)
Record PreOrder : Type :=
  {
    PO_Carrier :> Type;
    PO_LE : PO_Carrier → PO_Carrier → Prop where "x ⊑ y" := (PO_LE x y);
    PO_Refl : ∀ x, x ⊑ x;
    PO_ASym : ∀ x y, x ⊑ y → y ⊑ x → x = y;
    PO_Trans : ∀ x y z, x ⊑ y → y ⊑ z → x ⊑ z
  }
.

Arguments PO_Carrier _ : assert.
Arguments PO_LE {_} _ _, _ _ _.
Arguments PO_Refl {_} _.
Arguments PO_ASym {_} _ _ _ _.
Arguments PO_Trans {_} _ _ _ _ _.

Notation "x ⊑ y" := (PO_LE x y) : order_scope.

Definition PO_LT {p : PreOrder} (x y : p) := (x ⊑ y)%order ∧ x ≠ y.

Notation "x ⊏ y" := (PO_LT x y) : order_scope.
  
(** A monotone function is order preserving. *)
Record Monotone (A B : PreOrder) : Type :=
  {
    MNT_fun :> A → B;
    MNT_monotone : ∀ x y, x ⊑ y → MNT_fun x ⊑ MNT_fun y
  }.

Local Hint Resolve MNT_monotone.

Program Definition Monotone_comp
           {A B C : PreOrder}
           (f : Monotone A B)
           (g : Monotone B C)
  :
    Monotone A C :=
  {|
    MNT_fun := fun x => g (f x)
  |}.


(** Greatest lower bound and least upper bound in a preorder. *)
Section LUB_GLB.
  Context {A : PreOrder}.

  Section Generalized.
    Context (P : A → Prop).
    
    Record LUB :=
      {
        lub :> A;
        lub_ub : ∀ (x : A), P x → x ⊑ lub;
        lub_lst : ∀ (ub : A), (∀ (x : A), P x → x ⊑ ub) → lub ⊑ ub
      }
    .

    Record GLB :=
      {
        glb :> A;
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

Arguments lub {_ _} _.
Arguments glb {_ _} _.

Notation "⊔ᵍ Q" := (LUB Q) : order_scope.

Notation "⊓ᵍ Q" := (GLB Q) : order_scope.

Notation "x ⊔ y" := (LUB_Pair x y) : order_scope.
  
Notation "x ⊓ y" := (GLB_Pair x y) : order_scope.

Hint Resolve PO_Refl PO_ASym PO_Trans.

Theorem LE_LT_Trans {A : PreOrder} : ∀ (x y z : A), x ⊑ y → y ⊏ z → x ⊏ z.
Proof.
  intros x y z H1 [H21 H22]; split; eauto.
  intros eq.
  rewrite eq in H1; auto.
Qed.

Theorem LT_LE_Trans {A : PreOrder} : ∀ (x y z : A), x ⊏ y → y ⊑ z → x ⊏ z.
Proof.
  intros x y z [H11 H12] H2; split; eauto.
  intros eq.
  rewrite <- eq in H2; auto.
Qed.
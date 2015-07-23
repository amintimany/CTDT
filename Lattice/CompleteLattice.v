Require Export Lattice.PartialOrder.
Require Import Coq.Sets.Ensembles.

Local Open Scope order_scope.

(** A complete lattice is preorder relation that has all meets (LUBs) and joins (GLBs). *)
Record CompleteLattice : Type :=
  {
    CMSL_PO :> PartialOrder;
    CMSL_meets : ∀ (P : CMSL_PO → Prop), ⊔ᵍ P;
    CMSL_joins : ∀ (P : CMSL_PO → Prop), ⊓ᵍ P;
    CMSL_bot : CMSL_PO;
    CMSL_bot_bottom : ∀ (x : CMSL_PO), CMSL_bot ⊑ x
  }.

Arguments CMSL_PO _ : assert.
Arguments CMSL_meets {_} _, _ _.
Arguments CMSL_joins {_} _, _ _.
Arguments CMSL_bot {_}.

Notation "⊥" := CMSL_bot : lattice_scope.

Definition Lat_LUB {Lat : CompleteLattice} (P : Lat → Prop) : ⊔ᵍ P :=
  (CMSL_meets Lat P).

Definition Lat_GLB {Lat : CompleteLattice} (P : Lat → Prop) : ⊓ᵍ P :=
  (CMSL_joins Lat P).

Definition Lat_LUB_Pair {Lat : CompleteLattice} (x y : Lat) : x ⊔ y :=
  (CMSL_meets Lat (Couple _ x y)).

Definition Lat_GLB_Pair {Lat : CompleteLattice} (x y : Lat) : x ⊓ y :=
  (CMSL_joins Lat (Couple _ x y)).

Notation "⊔ᵍ Q" := (Lat_LUB Q) : lattice_scope.

Notation "⊓ᵍ Q" := (Lat_GLB Q) : lattice_scope.

Notation "x ⊔ y" := (Lat_LUB_Pair x y) : lattice_scope.
  
Notation "x ⊓ y" := (Lat_GLB_Pair x y) : lattice_scope.

Hint Resolve CMSL_bot_bottom.

Theorem Bottom_Unique {Lat : CompleteLattice} (b : Lat) : (∀ x, b ⊑ x) → b = ⊥%lattice.
Proof.
  intros H.
  apply PO_ASym; auto.
Qed.
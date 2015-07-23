Require Import Lattice.PreOrder.
Require Import Coq.Sets.Ensembles.

Local Open Scope order_scope.

(** A complete lattice is preorder relation that has all meets (LUBs) and joins (GLBs). *)
Record Complete_Lattice : Type :=
  {
    CMSL_PO :> PreOrder;
    CMSL_meets : ∀ (P : CMSL_PO → Prop), ⊔ᵍ P;
    CMSL_joins : ∀ (P : CMSL_PO → Prop), ⊓ᵍ P
  }.

Definition Lat_LUB {Lat : Complete_Lattice} (P : Lat → Prop) : ⊔ᵍ P :=
  (CMSL_meets Lat P).

Definition Lat_GLB {Lat : Complete_Lattice} (P : Lat → Prop) : ⊓ᵍ P :=
  (CMSL_joins Lat P).

Definition Lat_LUB_Pair {Lat : Complete_Lattice} (x y : Lat) : x ⊔ y :=
  (CMSL_meets Lat (Couple _ x y)).

Definition Lat_GLB_Pair {Lat : Complete_Lattice} (x y : Lat) : x ⊓ y :=
  (CMSL_joins Lat (Couple _ x y)).

Notation "⊔ᵍ Q" := (Lat_LUB Q) : lattice_scope.

Notation "⊓ᵍ Q" := (Lat_GLB Q) : lattice_scope.

Notation "x ⊔ y" := (Lat_LUB_Pair x y) : lattice_scope.
  
Notation "x ⊓ y" := (Lat_GLB_Pair x y) : lattice_scope.
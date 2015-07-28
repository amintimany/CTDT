Require Export Lattice.PartialOrder.
Require Import Coq.Sets.Ensembles.

Local Open Scope order_scope.

(** A complete lattice is partial order relation that has all meets (LUBs) and joins (GLBs). *)
Record CompleteLattice : Type :=
  {
    CL_PO :> PartialOrder;
    CL_meets : ∀ (P : CL_PO → Prop), ⊔ᵍ P;
    CL_joins : ∀ (P : CL_PO → Prop), ⊓ᵍ P;
    CL_bot : CL_PO;
    CL_bot_bottom : ∀ (x : CL_PO), CL_bot ⊑ x;
    (** This is a usual property of real numbers that is is in dealing with metric spaces in
e.g., proof of uniqueness of limits. We require it to be proven for a complete lattice as we
can't prove it constructively in general. Note that its contrapositive is easily provable for
any partial order relation with a bottom element! *)
    CL_strict_bot : ∀ x, (∀ y, CL_bot ⊏ y → x ⊏ y) → x = CL_bot;
    (** This is a dichotomy about the bottom element of a lattice. It either is not
reachable from a non-bottom element (there is always an element strictly between them)
or there is an element (not necessarily unique) in the lattice that sits immediately
(and strictly) above the bottom element.

We require this as part of the definition of a lattice as we can't distinguish these
two cases yet we need this distinction to keep proofs (e.g., uniqueness of limits)
constructive. *)
    CL_bottom_dichotomy :
      (∀ x, CL_bot ⊏ x → ∃ y, CL_bot ⊏ y ∧ y ⊏ x) ∨
      (∃ ab, CL_bot ⊏ ab ∧ (∀ x, x ⊏ ab → x = CL_bot))
  }.

Arguments CL_PO _ : assert.
Arguments CL_meets {_} _, _ _.
Arguments CL_joins {_} _, _ _.
Arguments CL_bot {_}.

Notation "⊥" := CL_bot : lattice_scope.

Definition Lat_LUB {Lat : CompleteLattice} (P : Lat → Prop) : ⊔ᵍ P :=
  (CL_meets Lat P).

Definition Lat_GLB {Lat : CompleteLattice} (P : Lat → Prop) : ⊓ᵍ P :=
  (CL_joins Lat P).

Definition Lat_LUB_Pair {Lat : CompleteLattice} (x y : Lat) : x ⊔ y :=
  (CL_meets Lat (Couple _ x y)).

Definition Lat_GLB_Pair {Lat : CompleteLattice} (x y : Lat) : x ⊓ y :=
  (CL_joins Lat (Couple _ x y)).

Notation "⊔ᵍ Q" := (Lat_LUB Q) : lattice_scope.

Notation "⊓ᵍ Q" := (Lat_GLB Q) : lattice_scope.

Notation "x ⊔ y" := (Lat_LUB_Pair x y) : lattice_scope.
  
Notation "x ⊓ y" := (Lat_GLB_Pair x y) : lattice_scope.

Hint Resolve CL_bot_bottom.

Local Open Scope lattice_scope.

Theorem Bottom_Unique {Lat : CompleteLattice} (b : Lat) : (∀ x, b ⊑ x) → b = ⊥.
Proof.
  intros H.
  apply PO_ASym; auto.
Qed.

Theorem LE_Bottom_Bottom {Lat : CompleteLattice} (b : Lat) : b ⊑ ⊥ → b = ⊥.
Proof.
  intros H.
  apply PO_ASym; auto.
Qed.
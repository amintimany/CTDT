Require Export Lattice.PartialOrder.
Require Import Coq.Sets.Ensembles.

Local Open Scope order_scope.

(** An M-lattice (measure lattice) is partial order relation that has all joins (LUBs) and
a top element. We require the user to provide the bottom element also explicitly. In any
partial order relation with arbitrary joins always has a unique bottom element – namely,
the join of the empty set. *)
Record MLattice : Type :=
  {
    CL_PO :> PartialOrder;
    CL_meets : ∀ (P : CL_PO → Prop), ⊔ᵍ P;
    CL_top : CL_PO;
    CL_top_top : ∀ (x : CL_PO), x ⊑ CL_top;
    CL_bot : CL_PO;
    CL_bot_bottom : ∀ (x : CL_PO), CL_bot ⊑ x;
    (** This is a usual property of real numbers used in the context of metric spaces in
e.g., proof of uniqueness of limits. We require it to be proven for an M-lattice as we
can't prove it constructively in general. Note that its contrapositive is easily provable for
any partial order relation with a bottom element! *)
    CL_strict_bot : ∀ x, (∀ y, CL_bot ⊏ y → x ⊏ y) → x = CL_bot;
    (** This is a dichotomy about the bottom element of a lattice. It states that the 
bottom element is either not reachable from a non-bottom element (there is always an
element strictly between them) or there is an element (not necessarily unique) in the
lattice that sits immediately (and strictly) above the bottom element.

We require this as part of the definition of an M-lattice as we can't distinguish
these two cases and we need this distinction to keep proofs (e.g., uniqueness of limits)
constructive. *)
    CL_bottom_dichotomy :
      (∀ x, CL_bot ⊏ x → {y : CL_PO | CL_bot ⊏ y ∧ y ⊏ x})
      +
      {ab : CL_PO | CL_bot ⊏ ab ∧ (∀ x, x ⊏ ab → x = CL_bot)}
  }.

Arguments CL_PO _ : assert.
Arguments CL_meets {_} _, _ _.
Arguments CL_top {_}.
Arguments CL_bot {_}.

Notation "⊤" := CL_top : lattice_scope.
Notation "⊥" := CL_bot : lattice_scope.

Definition Lat_LUB {Lat : MLattice} (P : Lat → Prop) : ⊔ᵍ P :=
  (CL_meets Lat P).

Definition Lat_LUB_Pair {Lat : MLattice} (x y : Lat) : x ⊔ y :=
  (CL_meets Lat (Couple _ x y)).


Notation "⊔ᵍ Q" := (Lat_LUB Q) : lattice_scope.

Notation "x ⊔ y" := (Lat_LUB_Pair x y) : lattice_scope.

Hint Resolve CL_bot_bottom.

Hint Resolve CL_top_top.

Local Open Scope lattice_scope.

Theorem Top_Unique {Lat : MLattice} (t : Lat) : (∀ x, x ⊑ t) → t = ⊤.
Proof.
  intros H.
  apply PO_ASym; auto.
Qed.

Theorem Bottom_Unique {Lat : MLattice} (b : Lat) : (∀ x, b ⊑ x) → b = ⊥.
Proof.
  intros H.
  apply PO_ASym; auto.
Qed.

Theorem LE_Bottom_Bottom {Lat : MLattice} (b : Lat) : b ⊑ ⊥ → b = ⊥.
Proof.
  intros H.
  apply PO_ASym; auto.
Qed.

Theorem lub_sym {L : MLattice} (a b : L) : (a ⊔ b) = (b ⊔ a) :> L.
Proof.
  apply PO_ASym; apply lub_lst; intros ? H; destruct H; apply lub_ub; constructor.
Qed.

Theorem lub_bot {L : MLattice} (b : L) : (b ⊔ ⊥) = b :> L.
Proof.
  apply PO_ASym.
  apply lub_lst; intros ? H; destruct H; trivial.
  apply lub_ub; constructor.
Qed.
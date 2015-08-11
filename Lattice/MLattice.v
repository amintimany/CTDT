Require Export Lattice.PartialOrder.
Require Import Coq.Sets.Ensembles.

Local Open Scope order_scope.

(** An M-lattice (measure lattice) is partial order relation that has all joins (LUBs) and
a top element. We require the user to provide the bottom element also explicitly. In any
partial order relation with arbitrary joins always has a unique bottom element – namely,
the join of the empty set. *)
Record MLattice : Type :=
  {
    ML_PO :> PartialOrder;
    ML_meets : ∀ (X : Type) (f : X → ML_PO), ⊔ᵍ f;
    ML_top : ML_PO;
    ML_top_top : ∀ (x : ML_PO), x ⊑ ML_top;
    ML_bot : ML_PO;
    ML_bot_bottom : ∀ (x : ML_PO), ML_bot ⊑ x;
(*    (** This is a usual property of real numbers used in the context of metric spaces in
e.g., proof of uniqueness of limits. We require it to be proven for an M-lattice as we
can't prove it constructively in general. Note that its contrapositive is easily provable for
any partial order relation with a bottom element! *)
    ML_strict_bot : ∀ x, (∀ y, ML_bot ⊏ y → x ⊏ y) → x = ML_bot; *)
    (** The subset of distances for which we have to provide constructive approximatons
for limits and such. *)
    ML_appr_cond : ML_PO → Type;
    (** The top element must be in the approximation subset. *)
    ML_appr_top : ML_appr_cond ML_top;
    (** The approximation subset must be all positive. *)
    ML_appr_pos : ∀ x, ML_appr_cond x → ML_bot ⊏ x;
    (** The approximation subset dominate all positive values. *)
    ML_appr_dominate_pos : (∀ x, (∀ y, ML_appr_cond y → x ⊏ y) → x = ML_bot);
    (** This is a dichotomy about the bottom element of a lattice. It states that the 
bottom element is either not reachable from a non-bottom element (there is always an
element strictly between them) or there is an element (not necessarily unique) in the
lattice that sits immediately (and strictly) above the bottom element.

We require this as part of the definition of an M-lattice as we can't distinguish
these two cases and we need this distinction to keep proofs (e.g., uniqueness of limits)
constructive. *)
    ML_bottom_dichotomy :
      (∀ x, ML_appr_cond x → {y : ML_PO & ML_appr_cond y & ML_bot ⊏ y ∧ y ⊏ x})
      +
      {ab : ML_PO & ML_appr_cond ab & (∀ x, x ⊏ ab → x = ML_bot)};
    (** All elements are approximatable. This is off course not always constructively
provable, e.g., in bisected spaces. Therefore, we try to avoid it as much as possible.*)
    ML_all_approximatable :
      ∀ x, ML_bot ⊏ x → {b : ML_PO & b ⊑ x & ML_appr_cond b}
  }.

Arguments ML_PO _ : assert.
Arguments ML_meets {_ _} _, _ {_} _.
Arguments ML_top {_}.
Arguments ML_bot {_}.

Definition ApprType (M : MLattice) := {x : M & ML_appr_cond M x}.

Notation "⊤" := ML_top : lattice_scope.
Notation "⊥" := ML_bot : lattice_scope.

Definition Lat_LUB {Lat : MLattice} {X : Type} (f : X → Lat) : ⊔ᵍ f :=
  (ML_meets Lat f).

Definition Lat_LUB_Pair {Lat : MLattice} (x y : Lat) : x ⊔ y :=
  (ML_meets Lat (fun u : bool => if u then x else y)).

Notation "⊔ᵍ Q" := (Lat_LUB Q) : lattice_scope.

Notation "x ⊔ y" := (Lat_LUB_Pair x y) : lattice_scope.

Hint Resolve ML_bot_bottom.

Hint Resolve ML_top_top.

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
  apply PO_ASym; apply lub_lst; intros [|];
  apply (lub_ub (fun u : bool => if u then _ else _) _ false) +
  apply (lub_ub (fun u : bool => if u then _ else _) _ true).
Qed.

Theorem lub_bot {L : MLattice} (b : L) : (b ⊔ ⊥) = b :> L.
Proof.
  apply PO_ASym.
  apply lub_lst; intros [|]; trivial.
  apply (lub_ub (fun u : bool => if u then _ else _) _ true).
Qed.

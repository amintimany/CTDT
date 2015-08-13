Require Export Categories.Essentials.Notations.

Notation "x ≤ y" := (le x y) (at level 70, no associativity).

Notation "x ≥ y" := (ge x y) (at level 70, no associativity).

Reserved Notation "x ⊑ y" (at level 70, no associativity).

Reserved Notation "x ⊏ y" (at level 70, no associativity).

Reserved Notation "x ⊓ y" (at level 85, no associativity).

Reserved Notation "x ⊔ y" (at level 85, no associativity).

Reserved Notation "⊓ᵍ y" (at level 75).

Reserved Notation "⊔ᵍ y" (at level 75).

Reserved Notation "∂( x , y )" (at level 75, no associativity).

Reserved Notation "'ρ' x" (at level 75, no associativity).

Delimit Scope order_scope with order.

Delimit Scope lattice_scope with lattice.

Delimit Scope metric_scope with metric.
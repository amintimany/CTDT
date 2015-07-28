Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
                             (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
                             (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.

Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.

Notation "x → y" := (x -> y)
                      (at level 90, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.

Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.

Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

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
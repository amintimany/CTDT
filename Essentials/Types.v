Global Set Primitive Projections.

Global Set Universe Polymorphism.

Require Export Categories.Essentials.Types.
Require Import Essentials.Notations.

(** Singleton Type *)
Axiom Unit : Type.
Axiom TT : Unit.
Axiom Unit_Singleton : ∀ x y : Unit, x = y.
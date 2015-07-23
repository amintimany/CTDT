Require Import Essentials.Notations.

(** Basic definition of fixed point of a function f *)
Section fxpt.
  Context {A : Type} (f : A → A).

  Definition is_FixedPoint (x : A) := f x = x.
  
  Record FixedPoint : Type :=
    {
      fx :> A;
      fx_fixedpoint : is_FixedPoint fx
    }.

End fxpt.


(** Sequence of applications of f. *)
Fixpoint iterate {A : Type} (f : A → A) (x : A) (n : nat) : A :=
  match n with
  | O => x
  | S n' => f (iterate f x n')
  end.
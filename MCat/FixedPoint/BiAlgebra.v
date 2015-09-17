Require Import Coq.Arith.Compare_dec.

Require Import
        Essentials.Facts_Tactics
        Essentials.Notations
        Essentials.Types.
Require Import
        Categories.Category.Main
        Categories.Functor.Main
        Categories.Ext_Cons.Prod_Cat.Prod_Cat
.

Section BiAlgebras.
  Context {C : Category}
          (F : (((C ^op) × C) –≻ C)%functor).

  (** A bi-algebra of a functor F : Cᵒᵖ × C –≻ C is a triple (U, h, k) where
U is an object of C, h : F(U, U) –≻ U and k : U –≻ F(U, U) are morphisms
in C.
*)
  Record BiAlgebra : Type :=
    {
      BiAlg_obj :> C;
      BiAlg_from_obj : (BiAlg_obj –≻ F _o (BiAlg_obj, BiAlg_obj))%morphism%object;
      BiAlg_to_obj : (F _o (BiAlg_obj, BiAlg_obj) –≻ BiAlg_obj)%morphism%object
    }.

  (** a bi-algebra morphism from (U, h, k) to (U', h', k') is a parir of
morphism f : U –≻ U' and g : U' –≻ U such that the following diagrams
commute:
#
<pre>
                  F(g, f)
       F(U, U) ———–———————–> F(U', U')
          |                      |
          |                      |
          |                      |
          |h                     |h'
          |                      |
          |                      |
          |                      |
          ↓                      ↓
          U    ————————————>     U'
                     f


                  F(f, g)
       F(U, U) <———–———————– F(U', U')
          ↑                      ↑
          |                      |
          |                      |
          |k                     |k'
          |                      |
          |                      |
          |                      |
          |                      |
          U    <————————————     U'
                     g

</pre>
#
*)
  Record BiAlg_Morph (A B : BiAlgebra) : Type :=
    {
      BAM_forward : (A –≻ B)%morphism;
      BAM_backward : (B –≻ A)%morphism;
      BAM_forward_com :
        ((BiAlg_to_obj B) ∘ (F @_a (_, _) (_, _) (BAM_backward, BAM_forward)) =
         BAM_forward ∘ (BiAlg_to_obj A))%morphism;
      BAM_backward_com :
        ((F @_a (_, _) (_, _) (BAM_forward, BAM_backward) ∘ (BiAlg_from_obj B)) =
        (BiAlg_from_obj A) ∘ BAM_backward)%morphism
    }.

  Arguments BAM_forward {_ _} _.
  Arguments BAM_backward {_ _} _.


  (** Two bi-algebra morphisms are equal if their underlying arrows are. *)
  Theorem BiAlg_Morph_eq_simplify
          {a b : BiAlgebra}
          (f g : BiAlg_Morph a b)
    : 
      BAM_forward f = BAM_forward g →
      BAM_backward f = BAM_backward g →
      f = g
  .
  Proof.
    intros.
    destruct f; destruct g; cbn in *.
    ElimEq.
    PIR.
    trivial.
  Qed.    


  (** Identity bi-algebra morphisms are bi-algebra morphism
with identity arrow as their underlying morphisms. *)
  Program Definition BiAlg_Morp_id (A : BiAlgebra) : BiAlg_Morph A A :=
    {|
      BAM_forward := id;
      BAM_backward := id
    |}.

  Local Hint Extern 1 =>
  match goal with
    [|- context [((F _a) (?h1 ∘ ?h2, ?h3 ∘ ?h4))%morphism]] =>
    cbn_rewrite
      (@F_compose
         _
         _
         F
         (_, _)
         (_, _)
         (_, _)
         (h1, h4)
         (h2, h3)
      )
  end.

  Local Hint Extern 1 => rewrite assoc_sym; rewrite BAM_forward_com.

  Local Hint Extern 1 => rewrite assoc; rewrite BAM_forward_com.

  Local Hint Extern 1 => rewrite assoc_sym; rewrite BAM_backward_com.

  Local Hint Extern 1 => rewrite assoc; rewrite BAM_backward_com.

  (** composition of bi-algebra morphisms is the bi-algebra morphism that
has as underlying morphisms the composition of the underlying morphisms
of the arrows being composed. *)
  Program Definition BiAlg_Morp_compose
          {a b c : BiAlgebra}
          (f : BiAlg_Morph a b)
          (g : BiAlg_Morph b c)
    :
      BiAlg_Morph a c :=
    {|
      BAM_forward := (BAM_forward g) ∘ (BAM_forward f);
      BAM_backward := (BAM_backward f) ∘ (BAM_backward g)
    |}.

  (** The identity bi-algebra morphism is the left unit of their
compositions. *)
  Theorem BiAlg_Morp_id_unit_left
    {a b : BiAlgebra}
    (f : BiAlg_Morph a b)
    :
      BiAlg_Morp_compose f (BiAlg_Morp_id _) = f
  .
  Proof.
    apply BiAlg_Morph_eq_simplify; cbn; auto.
  Qed.

  (** The identity bi-algebra morphism is the right unit of their
compositions. *)
  Theorem BiAlg_Morp_id_unit_right
    {a b : BiAlgebra}
    (f : BiAlg_Morph a b)
    :
      BiAlg_Morp_compose (BiAlg_Morp_id _) f = f
  .
  Proof.
    apply BiAlg_Morph_eq_simplify; cbn; auto.
  Qed.

  (** Composition of bi-algebra morphisms is associative. *)
  Theorem BiAlg_Morp_compose_assoc
    {a b c d : BiAlgebra}
    (f : BiAlg_Morph a b)
    (g : BiAlg_Morph b c)
    (h : BiAlg_Morph c d)
    :
      BiAlg_Morp_compose f (BiAlg_Morp_compose g h) =
      BiAlg_Morp_compose (BiAlg_Morp_compose f g) h
  .
  Proof.
    apply BiAlg_Morph_eq_simplify; cbn; auto.
  Qed.

  (** Bi-algebras form a category. *)
  Definition BiAlg_Cat : Category :=
    {|
      Obj := BiAlgebra;
      Hom := BiAlg_Morph;
      compose := @BiAlg_Morp_compose;
      assoc := @BiAlg_Morp_compose_assoc;
      assoc_sym := fun _ _ _ _ _ _ _ => eq_sym (@BiAlg_Morp_compose_assoc _ _ _ _ _ _ _);
      id := BiAlg_Morp_id;
      id_unit_right := @BiAlg_Morp_id_unit_right;
      id_unit_left := @BiAlg_Morp_id_unit_left
    |}.

  (** If two bi-algebras are isomorphic, then their underlying objects are. *)
  Program Definition BiAlg_iso_obj_iso
          {a b : BiAlgebra}
          (f : (a ≃≃ b ::> BiAlg_Cat)%isomorphism)
    :
      (a ≃≃ b ::> C)%isomorphism
    :=
      {|
        iso_morphism := BAM_forward (iso_morphism f);
        inverse_morphism := BAM_forward (inverse_morphism f)
      |}.

  Next Obligation.
  Proof.
    apply (f_equal BAM_forward (left_inverse f)).
  Qed.

  Next Obligation.
  Proof.
    apply (f_equal BAM_forward (right_inverse f)).
  Qed.
    
End BiAlgebras.

Arguments BiAlg_Morph {_ _} _ _.
Arguments BAM_forward {_ _ _ _} _.
Arguments BAM_backward {_ _ _ _} _.
Arguments BAM_forward_com {_ _ _ _} _.
Arguments BAM_backward_com {_ _ _ _} _.

Arguments BiAlg_obj {_ _} _.
Arguments BiAlg_from_obj {_ _} _.
Arguments BiAlg_to_obj {_ _} _.
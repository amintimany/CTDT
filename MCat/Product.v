Require Import
        Essentials.Facts_Tactics
        Essentials.Notations
        Essentials.Types.
Require Import Metrics.Mappings.
Require Import Metrics.Complete_UltraMetric.
Require Import Metrics.CBULt.Product.
Require Import Categories.Category.Main.
Require Import
        Categories.Ext_Cons.Prod_Cat.Prod_Cat.
Require Import MCat.MCat.

Local Open Scope order_scope.
Local Open Scope metric_scope.
Local Open Scope lattice_scope.

Section MCat_Prod.
  Context {L : MLattice} (M M' : MCat L).
  
  (** Product of two M-categories is an M-category. *)  
  Program Definition MCat_Prod : MCat L :=
    {|
      MC_Obj := M * M';
      MC_Hom :=
        fun A B =>
          product_CUM
            (MC_Hom M (fst A) (fst B))
            (MC_Hom M' (snd A) (snd B));
      MC_compose :=
        fun a b c =>
          {|
            NE_fun :=
              fun w =>
                (MC_compose M (fst (fst w), (fst (snd w))),
                 MC_compose M' (snd (fst w), (snd (snd w))))
          |};
      MC_id := fun _ => (MC_id M, MC_id M')
    |}.

  Local Ltac lub2ub t :=
    eapply PO_Trans;
    [|apply (lub_ub _ _ t)].
  
  Next Obligation.
  Proof.
    apply lub_lst; intros [].
    {
      eapply PO_Trans; [apply NE_non_expansive|].
      apply lub_lst; intros []; cbn.
      + do 2 (lub2ub true); trivial.
      + lub2ub false; lub2ub true; trivial.
    }      
    {
      eapply PO_Trans; [apply NE_non_expansive|].
      apply lub_lst; intros []; cbn.
      + lub2ub true; lub2ub false; trivial.
      + do 2 (lub2ub false); trivial.
    }    
  Defined.

  Next Obligation.
  Proof.
    rewrite (MC_assoc M).
    rewrite (MC_assoc M').
    trivial.
  Defined.

  Next Obligation.
  Proof.
    rewrite (MC_assoc_sym M).
    rewrite (MC_assoc_sym M').
    trivial.
  Defined.

  Next Obligation.
  Proof.
    rewrite (MC_id_unit_left M).
    rewrite (MC_id_unit_left M').
    trivial.
  Defined.

  Next Obligation.
  Proof.
    rewrite (MC_id_unit_right M).
    rewrite (MC_id_unit_right M').
    trivial.
  Defined.

End MCat_Prod.

(** A simple test showing that product of two M-categories has as its
underlying category the product of the underlying categories of
the input M-categories. *)
Goal (∀ L (M M' : MCat L), (M × M')%category = (@MCat_Prod L M M')).
  exact (fun _ _ _ => eq_refl).
Abort.
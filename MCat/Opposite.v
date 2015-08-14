Require Import
        Essentials.Facts_Tactics
        Essentials.Notations
        Essentials.Types.
Require Import Metrics.Mappings.
Require Import Metrics.Complete_UltraMetric.
Require Import Categories.Category.Main.
Require Import MCat.MCat.

Local Open Scope order_scope.
Local Open Scope metric_scope.
Local Open Scope lattice_scope.

Section MCat_Op.
  Context {L : MLattice} (M : MCat L).
  
  (** Opposite of an M-categories is an M-category. *)  
  Program Definition MCat_Op : MCat L :=
    {|
      MC_Obj := M;
      MC_Hom :=
        fun A B => MC_Hom M B A;
      MC_compose :=
        fun a b c =>
          {|
            NE_fun :=
              fun w =>
                MC_compose M ((snd w), (fst w))
          |};
      MC_id := fun _ => MC_id M
    |}.

  Local Ltac lub2ub t :=
    eapply PO_Trans;
    [|apply (lub_ub _ _ t)].
  
  Next Obligation.
  Proof.
    eapply PO_Trans; [apply NE_non_expansive|].
    apply lub_lst;
      intros [];
      [lub2ub false| lub2ub true]; trivial.
  Qed.

  Next Obligation.
  Proof.
    apply (MC_assoc_sym M).
  Defined.

  Next Obligation.
  Proof.
    apply (MC_assoc M).
  Defined.

  Next Obligation.
  Proof.
    apply (MC_id_unit_right M).
  Defined.

  Next Obligation.
  Proof.
    apply (MC_id_unit_left M).
  Defined.

End MCat_Op.

(** The underlying category of the opposite of an M-category is just
the opposit of the underlying category of that M-category. *)
Goal (∀ L (M : MCat L), (M^op)%category = (@MCat_Op L M)).
  exact (fun _ _ => eq_refl).
Abort.
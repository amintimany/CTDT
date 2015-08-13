Require Import
        Essentials.Types
        Essentials.Facts_Tactics
.
Require Import Lattice.MLattice.
Require Import Metrics.Mappings
        Complete_UltraMetric.
Require Import
        Metrics.CBULt.CBULt
        Metrics.CBULt.Product
        Metrics.CBULt.Exponential
        Metrics.CBULt.Terminal.
Require Import MCat.MCat.
Require Import Categories.Category.Main.


Section CBULt_MCat.
  Context (L : MLattice).

  Program Definition CBULt_MCat : MCat L :=
    {|
      MC_Obj := (CBULt L);
      MC_Hom := Exp_CUM;
      MC_compose :=
        fun a b c =>
          {|
            NE_fun :=
              fun w => NonExp_compose (fst w) (snd w)
          |};
      MC_Term := CBULt_Terminal
    |}.             
  
  Next Obligation.
    apply lub_lst.
    intros x.
    eapply PO_Trans; [apply UM_ineq|].
    apply lub_lst; intros [].
    {
      eapply PO_Trans;
      [|apply (lub_ub (fun u : bool => if u then _ else _) _ true)].
      eapply PO_Trans; [|apply (lub_ub _ _ x)].
      eapply NE_non_expansive.
    }
    {
      eapply PO_Trans;
      [|apply (lub_ub (fun u : bool => if u then _ else _) _ false)].
      eapply PO_Trans; [|apply lub_ub]; trivial.
    }
  Qed.

End CBULt_MCat.

(** A simple test that shows that when a category is taken to be the underlying
category of an M-category, the underlying category of M-category is judgementally
equal to that category. *)
Goal (∀ L, (CBULt_MCat L) = (CBULt L) :> Category).
  exact (fun _ => eq_refl).
Abort.

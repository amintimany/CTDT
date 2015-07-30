Require Import Essentials.Notations.
Require Import Essentials.Arith.
Require Import Metrics.UltraMetric.
Require Import Coq.omega.Omega.

Local Open Scope order_scope.
Local Open Scope lattice_scope.
Local Open Scope metric_scope.

(** Limit of a sequence in an ultra metric space. *)
Section Limit.
  Context {L : MLattice} {U : UltraMetric L} (Seq : Sequence U).

  (** The limit of a sequence is an element whose distance from elements of the sequence
decreases below any positive distance as the sequence progresses. *)
  Record Limit : Type :=
    {
      Lim :> U;
      Lim_limit :
        ∀ (ε : L),
          ⊥ ⊏ ε →
          ∃ (N : nat), ∀ (n : nat), N ≤ n →
              ∂(Seq n, Lim) ⊏ ε
    }.

  Theorem Limit_unique (l l' : Limit) : l = l' :> U.
  Proof.
    destruct (ML_bottom_dichotomy L) as [dicht|dicht].
    {
      apply UM_zero_dist_eq.
      apply ML_strict_bot.
      intros y H.
      specialize (dicht _ H).
      destruct dicht as [y' [Hd1 Hd2]].
      destruct (Lim_limit l y' Hd1) as [Nl Hl].
      destruct (Lim_limit l' y' Hd1) as [Nl' Hl'].
      eapply LE_LT_Trans; [apply (UM_ineq L U l l' (Seq (max Nl Nl'))) |].
      eapply LE_LT_Trans; [|apply Hd2].
      apply lub_lst; intros x Hx.
      destruct Hx.
      + rewrite UM_dist_sym.
        apply Hl.
        apply l_le_max.
      + apply Hl'.     
        apply r_le_max.
    }
    {
      destruct dicht as [ab [Hd1 Hd2]].
      destruct (Lim_limit l ab Hd1) as [Nl Hl].
      destruct (Lim_limit l' ab Hd1) as [Nl' Hl'].
      apply UM_zero_dist_eq.
      apply LE_Bottom_Bottom.
      eapply PO_Trans; [apply (UM_ineq L U l l' (Seq (max Nl Nl'))) |].
      apply lub_lst; intros x Hx.
      destruct Hx.
      + rewrite UM_dist_sym.
        specialize (Hl (max Nl Nl') (l_le_max _ _)).
        apply Hd2 in Hl; rewrite Hl; trivial.
      + specialize (Hl' (max Nl Nl') (r_le_max _ _)).
        apply Hd2 in Hl'; rewrite Hl'; trivial.
    }
  Qed.
     
End Limit.

Arguments Lim {_ _ _} _.
Arguments Lim_limit {_ _ _} _ _ _.

Section Limit_of_SubSeq.
  Context {L : MLattice} {U : UltraMetric L} (Seq : Sequence U).

  Theorem Limit_of_SubSeq (l : Limit Seq) (l' : Limit (fun n => Seq (S n))) : l = l' :> U.
  Proof.
    cut (∀ (ε : L),
            ⊥ ⊏ ε →
            ∃ (N : nat), ∀ (n : nat),
                N ≤ n →
                ∂(Seq n, l') ⊏ ε
        ).
    {
      intros H.
      transitivity ({|Lim := l'; Lim_limit := H|}); trivial.
      apply Limit_unique.
    }
    {    
      intros.
      destruct (Lim_limit l' ε H) as [m H'].
      exists (S m).
      intros n H1.
      destruct n; [omega|].
      cut (m ≤ n); auto; omega.
    }
  Qed.      
      
End Limit_of_SubSeq.
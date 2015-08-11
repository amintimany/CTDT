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
        ∀ (ε : (ApprType L)),
          {N : nat | ∀ (n : nat), N ≤ n →
              ∂(Seq n, Lim) ⊏ (projT1 ε)}
    }.

  Theorem Limit_unique (l l' : Limit) : l = l' :> U.
  Proof.
    destruct (ML_bottom_dichotomy L) as [dicht|dicht].
    {
      apply UM_zero_dist_eq.
      apply ML_appr_dominate_pos.
      intros y H1.
      destruct (dicht _ H1) as [y' Hd1 [Hd2 Hd3]].
      destruct (Lim_limit l (existT _ _ Hd1)) as [Nl Hl].
      destruct (Lim_limit l' (existT _ _ Hd1)) as [Nl' Hl'].
      eapply LE_LT_Trans; [apply (UM_ineq L U l l' (Seq (max Nl Nl'))) |].
      eapply LE_LT_Trans; [|apply Hd3].
      apply lub_lst; intros [|].
      + rewrite UM_dist_sym.
        apply Hl.
        apply l_le_max.
      + apply Hl'.     
        apply r_le_max.
    }
    {
      destruct dicht as [ab Hd1 Hd2].
      destruct (Lim_limit l (existT _ _ Hd1)) as [Nl Hl].
      destruct (Lim_limit l' (existT _ _ Hd1)) as [Nl' Hl'].
      apply UM_zero_dist_eq.
      apply LE_Bottom_Bottom.
      eapply PO_Trans; [apply (UM_ineq L U l l' (Seq (max Nl Nl'))) |].
      apply lub_lst; intros [|].
      + rewrite UM_dist_sym.
        specialize (Hl (max Nl Nl') (l_le_max _ _)).
        apply Hd2 in Hl; rewrite Hl; trivial.
      + specialize (Hl' (max Nl Nl') (r_le_max _ _)).
        apply Hd2 in Hl'; rewrite Hl'; trivial.
    }
  Qed.
     
End Limit.

Arguments Lim {_ _ _} _.
Arguments Lim_limit {_ _ _} _ _.

Section Limit_of_SubSeq.
  Context {L : MLattice} {U : UltraMetric L} (Seq : Sequence U).

  Theorem Limit_of_SubSeq (l : Limit Seq) (l' : Limit (fun n => Seq (S n))) : l = l' :> U.
  Proof.
    cut (∀ (ε : (ApprType L)),
            {N : nat | ∀ (n : nat),
                N ≤ n →
                ∂(Seq n, l') ⊏ (projT1 ε)}
        ).
    {
      intros H.
      transitivity ({|Lim := l'; Lim_limit := H|}); trivial.
      apply Limit_unique.
    }
    {    
      intros ε.
      destruct (Lim_limit l' ε) as [m H'].
      exists (S m).
      intros n H1.
      destruct n; [omega|].
      cut (m ≤ n); auto; omega.
    }
  Qed.      
      
End Limit_of_SubSeq.

Section Distance_of_Limits.
  Context {L : MLattice} {U : UltraMetric L} (Seq Seq' : Sequence U).

  Theorem Distance_of_Limits (δ : L) (l : Limit Seq) (l' : Limit Seq') :
    ⊥ ⊏ δ → (∀ n, ∂(Seq n, Seq' n) ⊑ δ) → ∂(l, l') ⊑ δ.
  Proof.
    intros H1 H2.
    destruct (ML_all_approximatable _ _ H1) as [δ' H3 H4].
    destruct (Lim_limit l (existT _ _ H4)) as [m H5].
    destruct (Lim_limit l' (existT _ _ H4)) as [m' H6].
    eapply PO_Trans; [apply UM_ineq|].
    apply lub_lst; intros [].
    {
      rewrite UM_dist_sym.
      eapply PO_Trans; [|apply H3].
      apply (H5 (max m m') (l_le_max _ _)).
    }
    {
      eapply PO_Trans; [apply UM_ineq|].
      apply lub_lst; intros [].
      {
        apply H2.
      }
      {
        eapply PO_Trans; [|apply H3].
        apply (H6 (max m m') (r_le_max _ _)).
      }
    }
  Qed.

End Distance_of_Limits.





      
Require Import Essentials.Notations.
Require Import Essentials.Arith.
Require Import Metrics.UltraMetric.
Require Import Essentials.Omega.
Require Import Essentials.Facts_Tactics.

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
              δ(Seq n, Lim) ⊏ (projT1 ε)}
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

Section Eq_Seq_Eq_Limits.
  Context {L : MLattice}
          {U : UltraMetric L}
          (Seq Seq' : Sequence U)
          (l : Limit Seq)
          (l' : Limit Seq')
  .

  Theorem Eq_Seq_Eq_Limits : Seq = Seq' → l = l' :> U.
  Proof.
    intros H.
    destruct H.
    apply Limit_unique.
  Qed.    

End Eq_Seq_Eq_Limits.
  
Arguments Lim {_ _ _} _.
Arguments Lim_limit {_ _ _} _ _.

Section Limit_of_SubSeq.
  Context {L : MLattice} {U : UltraMetric L}.

  Program Definition Limit_of_SubSeq {Seq : Sequence U} (l : Limit Seq) (m : nat) :
    Limit (fun n => Seq (m + n)) :=
    {|
      Lim := l
    |}.

  Next Obligation.
  Proof.
    destruct (Lim_limit l ε) as [N H].
    exists (m + N).
    intros n H2.
    apply H.
    abstract omega.
  Defined.

  Theorem Limit_of_SubSeq_equal_1 {Seq : Sequence U} (l : Limit Seq) (l' : Limit (fun n => Seq (S n))) : l = l' :> U.
  Proof.
    cut (∀ (ε : (ApprType L)),
            {N : nat | ∀ (n : nat),
                N ≤ n →
                δ(Seq n, l') ⊏ (projT1 ε)}
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

  Theorem Limit_of_SubSeq_equal {Seq : Sequence U} (l : Limit Seq) (m : nat) (l' : Limit (fun n => Seq (m + n))) : l = l' :> U.
  Proof.
    induction m.
    + apply Limit_unique.
    + rewrite ((IHm (Limit_of_SubSeq l m))).
      set (W := Limit_of_SubSeq_equal_1 (Limit_of_SubSeq l m)).
      cbn in W.
      replace (fun n : nat => Seq (m + S n)) with (fun n : nat => Seq (S m + n)) in W
        by (abstract (FunExt; apply f_equal; omega)).
      apply W.
  Qed.
      
End Limit_of_SubSeq.

Section Limit_of_ConstSeq.
  Context {L : MLattice} {U : UltraMetric L} (A : U).

  Program Definition Limit_of_ConstSeq :
    Limit (fun _ => A) :=
    {|
      Lim := A
    |}.

  Next Obligation.
  Proof.
    exists 0.
    intros ? ?.
    rewrite UM_eq_zero_dist.
    apply ML_appr_pos.
    apply (projT2 ε).
  Qed.    
  
  Theorem Limit_of_ConstSeq_equal (l : Limit (fun _ => A)) : l = A :> U.
  Proof.
    change A with (Lim Limit_of_ConstSeq).
    apply Limit_unique.
  Qed.
  
End Limit_of_ConstSeq.
  
Section Distance_of_Limits.
  Context {L : MLattice} {U : UltraMetric L} (Seq Seq' : Sequence U).

  Theorem Distance_of_Limits (δ : L) (l : Limit Seq) (l' : Limit Seq') :
    ⊥ ⊏ δ → (∀ n, δ(Seq n, Seq' n) ⊑ δ) → δ(l, l') ⊑ δ.
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
Require Import Essentials.Notations Essentials.Facts_Tactics Essentials.Definitions.
Require Import Metrics.UltraMetric.
Require Import Metrics.Limit.

Local Obligation Tactic := idtac.

Local Open Scope order_scope.
Local Open Scope lattice_scope.

Section Mappings.
  Context {L : MLattice} (U U' : UltraMetric L).

  Local Hint Extern 1 => progress cbn in *.
  
  Local Hint Extern 1 => ElimEq.

  Local Hint Extern 1 => PIR.
  
  (** A non-expansive function is one that does not increase distance.
Here, as ultrametric spaces can have different measures, we need a
mapping from the measure of the codomain of the function to the
measure of the domain of the function.
   *)
  Record NonExpansive : Type :=
    {
      NE_fun :> U → U';
      NE_non_expansive :
        ∀ x y, (∂(NE_fun x, NE_fun y) ⊑ ∂(x, y))%order%metric
    }.

  (** Two non-expansive mappings are equal if their underlying maps are. *)
  Theorem NonExpansive_eq_simplify (f g : NonExpansive) : f = g :> (_ → _) → f = g.
  Proof.
    intros; destruct f; destruct g; auto.
  Qed.
    
  (**
A mechanism to indicate contraction rate of a contractive mapping.
   *)
  Record ContrRate : Type :=
    {
      CR_fun :> L → L;
      CR_monotone : ∀ x y, x ⊑ y → CR_fun x ⊑ CR_fun y;
      CR_non_expansive : ∀ x, CR_fun x ⊑ x;
      CR_contracts : ∀ x, ⊥ ⊏ x → CR_fun x ⊏ x;
      CR_rate_indicator :
        ∀ (ε ε' : L), ⊥ ⊏ ε → ∃ n, (iterate CR_fun ε' n) ⊏ ε
    }.

  (** Two contraction rates are equal if their underlying maps are. *)
  Theorem ContrRate_eq_simplify (f g : ContrRate) : f = g :> (_ → _) → f = g.
  Proof.
    intros; destruct f; destruct g; auto.
  Qed.

  Local Hint Extern 1 => rewrite ContrRate_eq_simplify.

  (** A contractive function is one that does decreases distance.
Here, as ultrametric spaces can have different measures, we need a
mapping from the measure of the codomain of the function to the
measure of the domain of the function.

We also require a contraction rate.
   *)
  Record Contractive : Type :=
    {
      CN_fun :> U → U';
      CN_ContrRate : ContrRate;
      CN_contractive :
        ∀ x y, (∂(CN_fun x, CN_fun y) ⊑ CN_ContrRate (∂(x, y)))%order%metric
    }.

  (** Two contractive mappings are equal if their underlying maps are. *)
  Theorem Contractive_eq_simplify (f g : Contractive) :
    f = g :> (_ → _) →
    (CN_ContrRate f) = (CN_ContrRate g) →
    f = g
  .
  Proof.
    intros; destruct f; destruct g; auto.
  Qed.

End Mappings.

Arguments ContrRate _ : clear implicits.

Arguments NE_fun {_ _ _} _ _.
Arguments NE_non_expansive {_ _ _} _ _ _.
Arguments CR_fun {_} _ _.
Arguments CR_monotone {_} _ _ _ _.
Arguments CR_non_expansive {_} _ _.
Arguments CR_contracts {_} _ _ _.
Arguments CR_rate_indicator {_} _ _ _ _.
Arguments CN_fun {_ _ _} _ _.
Arguments CN_ContrRate {_ _ _} _.
Arguments CN_contractive {_ _ _} _ _ _.

Notation "'ρ' f" := (CN_ContrRate f) : metric_scope.

Section NonExp_compose_and_id.
  Context {L : MLattice}.

  Local Obligation Tactic := auto.
  
  Section NonExp_id.
    Context (U : UltraMetric L).
    
    (** Idenetity non-expansive mapping. *)
    Program Definition NonExp_id : NonExpansive U U :=
      {|
        NE_fun := fun x => x
      |}.

  End NonExp_id.
  
  Section NonExp_compose.
    Context {U U' U'' : UltraMetric L}
            (F : NonExpansive U U')
            (G : NonExpansive U' U'').
    
    Local Obligation Tactic := cbn; eauto.

    Local Hint Extern 1 => apply NE_non_expansive.
    
    (** Composition of non-expansive mappings *)
    Program Definition NonExp_compose : NonExpansive U U'' :=
      {|
      NE_fun := fun x => G (F x)
      |}.

  End NonExp_compose.

  Local Hint Extern 1 => apply NonExpansive_eq_simplify.

  Section NonExp_compose_assoc.
    Context {U1 U2 U3 U4 : UltraMetric L}
            (F : NonExpansive U1 U2)
            (G : NonExpansive U2 U3)
            (H : NonExpansive U3 U4).
    
    (** Composition of non-expansive mappings *)
    Theorem NonExp_compose_assoc :
      NonExp_compose F (NonExp_compose G H) = NonExp_compose (NonExp_compose F G) H.
    Proof.
      auto.
    Qed.

  End NonExp_compose_assoc.

  Section NonExp_id_unit.
    Context {U U' : UltraMetric L}
            (F : NonExpansive U U').

    (** NonExp_id is the left unit of composition *)
    Theorem NonExp_id_unit_left : NonExp_compose F (NonExp_id _) = F.
    Proof.
      auto.
    Qed.

    (** NonExp_id is the right unit of composition *)
    Theorem NonExp_id_unit_right : NonExp_compose (NonExp_id _) F = F.
    Proof.
      auto.
    Qed.

  End NonExp_id_unit.

End NonExp_compose_and_id.
    
Section Contr_Comp.
  Context {L : MLattice}
          {U U' U'' : UltraMetric L}
  .
        
  (** Composition of non-expansive function on the right with a contractive function is
contractive. *)
  Program Definition Contr_NonExp_Contr
          (f : NonExpansive U U')
          (g : Contractive U' U'')
    :
      Contractive U U'' :=
    {|
      CN_fun := fun x => (g (f x));
      CN_ContrRate := (ρ g)%metric
    |}.

  Next Obligation.
  Proof.
    intros f g x y.
    cbn.
    eapply PO_Trans; [apply CN_contractive |].
    apply CR_monotone.
    apply NE_non_expansive.
  Qed.


  (** Composition of non-expansive function on the left with a contractive function is
contractive. *)
  Program Definition NonExp_Contr_Contr
          (f : Contractive U U')
          (g : NonExpansive U' U'')
    :
      Contractive U U'' :=
    {|
      CN_fun := fun x => (g (f x));
      CN_ContrRate := (ρ f)%metric
    |}.

  Next Obligation.
  Proof.
    intros f g x y.
    cbn.
    eapply PO_Trans; [|apply CN_contractive].
    apply NE_non_expansive.
  Qed.

End Contr_Comp.

(** Every contractive function is continuous. *)
Section Contractive_Continuous.
  Context {L : MLattice}
          {U : UltraMetric L}
          (Seq : Sequence U)
          (lm : Limit Seq)
          {U' : UltraMetric L}
          (f : Contractive U U')
  .

  Program Definition Contractive_Continuous : Limit (fun n => f (Seq n)) :=
    {|
      Lim := f lm
    |}.

  Next Obligation.
  Proof.
    intros ε H1.
    destruct (Lim_limit lm ε H1) as [N H2].
    exists N.
    intros n H3.
    eapply LE_LT_Trans; [apply CN_contractive|].
    eapply LE_LT_Trans; [apply CR_non_expansive|].
    apply H2; trivial.
  Qed.

End Contractive_Continuous.

(** Every non-expansive function is continuous. *)
Section NonExpansive_Continuous.
  Context {L : MLattice}
          {U : UltraMetric L}
          (Seq : Sequence U)
          (lm : Limit Seq)
          {U' : UltraMetric L}
          (f : NonExpansive U U')
  .

  Program Definition NonExpansive_Continuous : Limit (fun n => f (Seq n)) :=
    {|
      Lim := f lm
    |}.

  Next Obligation.
  Proof.
    intros ε H1.
    destruct (Lim_limit lm ε H1) as [N H2].
    exists N.
    intros n H3.
    eapply LE_LT_Trans; [apply NE_non_expansive|].
    apply H2; trivial.
  Qed.

End NonExpansive_Continuous.

(** Iterating a contractive function contracts the distance at least according to iterated ρ (ContrRate). *)
Section iterate_Contractive_LE.
  Context {L : MLattice}
          {U : UltraMetric L}
          (f : Contractive U U)
          (x y : U)
  .

  Theorem iterate_Contractive_LE :
    ∀ n, (∂(iterate f x n, iterate f y n) ⊑ iterate (ρ f)%metric (∂(x, y)) n)%metric.
  Proof.
    induction n; cbn; trivial.
    eapply PO_Trans; [apply CN_contractive|].
    apply CR_monotone; trivial.
  Qed.

End iterate_Contractive_LE.

(** Iterating a contraction rate contracts more the more it is applied. *)
Section iterate_ContrRate_LE.
  Context {L : MLattice}
          (f : ContrRate L)
          (x : L)
  .

  Theorem iterate_ContrRate_LE :
    ∀ n m, n ≤ m → iterate f x m ⊑ iterate f x n.
  Proof.
    intros n m H.
    induction H; cbn; trivial.
    eapply PO_Trans; [apply CR_non_expansive|]; trivial.
  Qed.

End iterate_ContrRate_LE.
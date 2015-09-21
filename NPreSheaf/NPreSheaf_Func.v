Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Arith.Compare_dec.

Require Import Essentials.Types.
Require Import Essentials.Arith.
Require Import Essentials.Omega.
Require Import Essentials.Facts_Tactics.
Require Import Metrics.Mappings.
Require Import Metrics.Complete_UltraMetric.
Require Import Metrics.CBULt.Product.
Require Import Bisected.Bisected.
Require Import MCat.MCat MCat.Product MCat.Opposite MCat.MFunc.
Require Import NPreSheaf.NPreSheaf.

Require Import Categories.Category.Main.
Require Import Categories.Functor.Main.
Require Import Categories.NatTrans.Main.
Require Import Categories.Archetypal.PreOrder_Cat.OmegaCat.
Require Import Categories.PreSheaf.PreSheaf.
Require Import Categories.Basic_Cons.Exponential
        Categories.Basic_Cons.Exponential_Functor.
Require Import Categories.PreSheaf.Product Categories.PreSheaf.Exponential.


Local Open Scope omegacat_scope.

(** A local abbreviation for the exponential functor of NPreSheaf. *)
Local Notation NPShExp := (@Exp_Func _ _ (PSh_Has_Exponentials ω)).

(** The action of exponential functor of the NPreSheaf on morphisms is
non-expansive. *)
Program Definition NPreSheaf_Exp_Func_FA
        (a b : MCat_Prod (MCat_Op NPreSheaf) NPreSheaf)
:
  NonExpansive
    (MC_Hom (MCat_Prod (MCat_Op NPreSheaf) NPreSheaf) a b)
    (MC_Hom NPreSheaf (NPShExp _o a)%object (NPShExp _o b)%object)
  :=
    {|
      NE_fun := fun x => (NPShExp _a x)%morphism
    |}.

Next Obligation.
Proof.
  intros n H1 m H2.
  assert (H11 := H1 true).
  assert (H12 := H1 false).
  clear H1.
  cbn in *.
  extensionality x.
  apply NatTrans_eq_simplify; cbn.
  extensionality y.
  extensionality h.
  destruct h as [h z].
  apply (Tle_le) in H2.
  set (h' := Tle_le h).
  rewrite H11; [|apply le_Tle; omega].
  rewrite H12; [|apply le_Tle; omega].
  trivial.
Qed.

(** The exponential functor of NPreSheaf is non-expansive. *)
Program Definition NPreSheaf_Exp_Func_NE :
  LocallyNonExpansive
    (MCat_Prod (MCat_Op NPreSheaf) NPreSheaf)
    NPreSheaf
  :=
    {|
      LNE_FO := FO NPShExp;
      LNE_FA := NPreSheaf_Exp_Func_FA;
      LNE_F_id := F_id NPShExp;
      LNE_F_compose := @F_compose _ _ NPShExp
    |}.

(** The underlying functor of NPreSheaf_Exp_Func_NE is indeed the
exponential functor of NPreSheaf. *)
Goal (NPreSheaf_Exp_Func_NE = NPShExp :> Functor _ _).
  reflexivity.  
Abort.

(** The later functor that maps a presheaf F to the presheaf ▷F such that

#
<pre>
         { unit       if n = 0
▷F(n) =  {
         { F (n-1)    oterhwise
</pre>
#
The arrow map is as expected.

Here we construct the object map of this functor. I.e., given a presheaf F
we construct ▷F.
*)
Section Basic_Later_PreSheaf.
  Context (F : PreSheaf ω).

  (** The object map of the later functor. *)
  Definition Basic_Later_PreSheaf_O : nat → Type :=
    fun n =>
      match n return Type with
      | O => unit
      | S n' => (F _o n')%object
      end
  .

  (** The arrow map of the later functor. *)
  Program Definition Basic_Later_PreSheaf_A
             (a b : nat) (h : b ≤ a)
    :
      (Basic_Later_PreSheaf_O a) → (Basic_Later_PreSheaf_O b)
    :=
      match a as u return
            ∀ x, x ≤ u → (Basic_Later_PreSheaf_O u) → (Basic_Later_PreSheaf_O x)
      with
      | O =>
        fun x h =>
          match x as v return
                v ≤ O → (Basic_Later_PreSheaf_O O) → (Basic_Later_PreSheaf_O v)
          with
          | O => fun _ _ => tt
          | S x' =>  fun h => _
          end h
      | S a' =>
        fun x h =>
          match x as v return
                v ≤ S a' → (Basic_Later_PreSheaf_O (S a')) → (Basic_Later_PreSheaf_O v)
          with
          | O => fun _ _ => tt
          | S x' => fun h => (F _a (Tle_remS _ _ h))%morphism
          end h
      end
        b h
  .

  Next Obligation.
  Proof.
    inversion h.
  Defined.

  (** Basic_Later_PreSheaf_A maps ids to ids. *)
  Theorem Basic_Later_PreSheaf_A_id
          (a : nat)
    :
      Basic_Later_PreSheaf_A _ _ (Tle_n a) = fun x => x.
  Proof.  
    extensionality n.
    destruct a; cbn.
    + destruct n; trivial.
    + replace (Tle_remS a a (Tle_n (S a)))
      with (Tle_n a) by apply Tle_is_HProp.
      cbn_rewrite (F_id F); trivial.
  Qed.

  (** Basic_Later_PreSheaf_A (Tle_S _ _ h) (b ≤ (S a) given h : b ≤ a) 
maps elements the same ways as first applying (Basic_Later_PreSheaf_A (Tle_S (Tle_n a) : a ≤ (S a)))
and then applying (Basic_Later_PreSheaf_A h). *)
  Program Definition Basic_Later_PreSheaf_A_Tle_S
          (a b : nat) (h : b ≤ a)
    :
      Basic_Later_PreSheaf_A _ _ (Tle_S _ _ h) =
      (fun n =>
         Basic_Later_PreSheaf_A _ _ h (Basic_Later_PreSheaf_A _ _ (Tle_S _ _ (Tle_n a)) n)
      )
  .
  Proof.
    destruct a.
    {
      destruct b; [trivial|inversion h].
    }
    {
      destruct b; trivial.
      cbn.
      cbn_rewrite
        <-
        (@F_compose
           _
           _
           F
           _
           _
           _
           (Tle_remS a (S a) (Tle_S (S a) (S a) (Tle_n (S a))))
           (Tle_remS b a h)
        ).
      match goal with
        [|- (F _a ?A = F _a ?B)%morphism] =>
        cutrewrite (A = B); [trivial|apply Tle_is_HProp]
      end.
    }      
  Qed.

  (** Basic_Later_Func_A maps composition of arrows (Tle_trans) to the
composition of Basic_Later_Func_A of individual arrows (≤ relations). *)
  Theorem Basic_Later_PreSheaf_A_compose
          (a b c : nat)
          (f : b ≤ a)
          (g : c ≤ b)
    :
      Basic_Later_PreSheaf_A a c (Tle_trans c b a g f) = 
      (fun x : Basic_Later_PreSheaf_O a =>
         Basic_Later_PreSheaf_A b c g (Basic_Later_PreSheaf_A a b f x))
  .
  Proof.  
    extensionality n.
    induction f.
    {
      destruct g.
      {
        replace (Tle_trans c c c (Tle_n c) (Tle_n c))
        with (Tle_n c) by apply Tle_is_HProp.
        rewrite Basic_Later_PreSheaf_A_id; trivial.
      }        
      {
        replace (Tle_trans c (S m) (S m) (Tle_S c m g) (Tle_n (S m)))
        with (Tle_S c m g) by apply Tle_is_HProp.
        rewrite Basic_Later_PreSheaf_A_id; trivial.
      }        
    }
    {
      replace (Tle_trans c b (S m) g (Tle_S b m f))
      with (Tle_S _ _ (Tle_trans c b m g f)) by apply Tle_is_HProp.
      rewrite Basic_Later_PreSheaf_A_Tle_S.
      rewrite IHf.
      rewrite (equal_f (Basic_Later_PreSheaf_A_Tle_S _ _ f)).
      trivial.
    }
  Qed.
    
  (** The later functor. *)
  Program Definition Basic_Later_PreSheaf : PreSheaf ω :=
    {|
      FO := Basic_Later_PreSheaf_O;
      FA := Basic_Later_PreSheaf_A;
      F_id := Basic_Later_PreSheaf_A_id;
      F_compose := Basic_Later_PreSheaf_A_compose
  |}.

End Basic_Later_PreSheaf.

(** The arrow map of later functor. The object map is already
defined: Basic_Later_PreSheaf. 
*)
Program Definition Basic_Later_Func_A {F G : PreSheaf ω} (f : NatTrans F G) :
  NatTrans (Basic_Later_PreSheaf F) (Basic_Later_PreSheaf G)
  :=
    {|
      Trans :=
        fun n x =>
          match
            n as u return (Basic_Later_PreSheaf_O F u → Basic_Later_PreSheaf_O G u)
          with
          | 0 => fun x => x
          | S n' => fun v => Trans f n' v
          end
            x
    |}.

Next Obligation.
Proof.
  extensionality x.
  destruct h; cbn.
  {
    destruct c'; cbn; trivial.
    apply (equal_f (Trans_com f (Tle_remS c' c' (Tle_n (S c'))))).
  }
  {
    destruct c'; trivial.
    apply (equal_f (Trans_com f (Tle_remS c' m (Tle_S (S c') m h)))).
  }
Qed.    

Next Obligation.
Proof.
  symmetry.
  apply Basic_Later_Func_A_obligation_1.
Qed.  

(** Basic_Later_Func_A maps ids to ids. *)
Program Definition Basic_Later_Func_A_id (F : PreSheaf ω) :
  Basic_Later_Func_A (NatTrans_id F) = NatTrans_id (Basic_Later_PreSheaf F)
.
Proof.
  apply NatTrans_eq_simplify.
  extensionality x.
  destruct x; cbn in *; trivial.
Qed.

(** Basic_Later_Func_A respects compositions. *)
Program Definition Basic_Later_Func_A_compose
        (F G I : PreSheaf ω)
        (f : NatTrans F G)
        (g : NatTrans G I)
  :
  Basic_Later_Func_A (g ∘ f) = ((Basic_Later_Func_A g) ∘ (Basic_Later_Func_A f))%nattrans
.
Proof.
  apply NatTrans_eq_simplify.
  extensionality x.
  destruct x; cbn in *; trivial.
Qed.

(** The later functor from the category of presheaves on natural numbers to itself. *)
Program Definition Basic_Later_Func : Functor (PShCat ω) (PShCat ω) :=
  {|
    FO := Basic_Later_PreSheaf;
    FA := @Basic_Later_Func_A;
    F_id := Basic_Later_Func_A_id;
    F_compose := Basic_Later_Func_A_compose
  |}.

(** The arrow map of Basic_Later_Func is contractive. *)
Program Definition Basic_Later_Func_A_Contr
        (F G : NPreSheaf)
  :
    Controlled_Contractive
      Half_ContrRate
      (MC_Hom NPreSheaf F G)
      (MC_Hom NPreSheaf (Basic_Later_PreSheaf F) (Basic_Later_PreSheaf G))
  :=
    {|
      CCN_fun := @Basic_Later_Func_A F G
    |}.

Local Obligation Tactic := idtac.

Next Obligation.
Proof.
  intros F G f g n H1 m H2; cbn in *.
  destruct m; trivial.
  destruct n; [inversion H2|].
  FunExt; rewrite H1; trivial.
  apply Tle_remS; trivial.
Qed.

(** The exponential functor of NPreSheaf is non-expansive. *)
Program Definition Later_Func :
  LocallyContractive NPreSheaf NPreSheaf
  :=
    {|
      LCN_FO := Basic_Later_PreSheaf;
      LCN_FA := Basic_Later_Func_A_Contr;
      LCN_F_id := Basic_Later_Func_A_id;
      LCN_F_compose := Basic_Later_Func_A_compose
    |}.

(** The underlying functor ofLater_Func is indeed Basic_Later_Func . *)
Goal (Later_Func = Basic_Later_Func :> Functor _ _).
  reflexivity.  
Abort.
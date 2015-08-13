Require Import Essentials.Facts_Tactics.
Require Export Coq.omega.Omega.
(** It seems that omega changes the Obligation Tactic Globally!!! *)
Global Obligation Tactic := basic_simpl; auto.
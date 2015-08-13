Require Import Essentials.Notations.
Require Import Essentials.Omega.

Theorem l_le_max : ∀ n m, n ≤ max n m.
Proof.
  induction n; cbn; intros; try omega.
  destruct m; trivial.
  cut (n ≤ max n m); trivial; omega.
Qed.

Theorem r_le_max : ∀ n m, m ≤ max n m.
Proof.
  induction n; cbn; intros; try omega.
  destruct m;  try omega.
  cut (m ≤ max n m); trivial; omega.
Qed.
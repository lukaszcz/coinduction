From Coinduction Require Import Coinduction.
Require Import Lists.Streams.

Coinduction lem : forall s : Stream nat, EqSt s s.
Proof.
  intros ? ? CH.
  destruct s; constructor; [ reflexivity | apply CH ].
Qed.

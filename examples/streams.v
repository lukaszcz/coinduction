From Coinduction Require Import Coinduction.
Require Lists.Streams.

Coinduction lem0 : forall (A : Type) (s : Streams.Stream A), Streams.EqSt s s.
Proof.
  intros ? ? CH.
  Print EqSt__g.
  destruct s; constructor; [ reflexivity | apply CH ].
Qed.

Check lem0.
Print lem0.

Import Lists.Streams.

Coinduction lem : forall s : Stream nat, EqSt s s.
Proof.
  intros ? ? CH.
  destruct s; constructor; [ reflexivity | apply CH ].
Qed.

Check lem.
Print lem.
Print lem0.

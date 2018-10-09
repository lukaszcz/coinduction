From Coinduction Require Import Coinduction.
Require Lists.Streams.

CoInduction lem_eq : forall (A : Type) (s : Streams.Stream A), Streams.EqSt s s.
Proof.
  ccrush.
Qed.

Import Lists.Streams.

CoInduction lem_eq_nat : forall s : Stream nat, EqSt s s.
Proof.
  ccrush.
Qed.

Print lem_eq.

CoFixpoint plusone s := match s with Cons x t => Cons (x + 1) (plusone t) end.
CoFixpoint ones := Cons 1 ones.
CoFixpoint plus s1 s2 := match s1, s2 with Cons x1 t1, Cons x2 t2 => Cons (x1 + x2) (plus t1 t2) end.

CoInduction lem_plusone : forall s, EqSt (plus s ones) (plusone s).
Proof.
  csolve on s.
  Undo.
  yelles 2.
Qed.

Print lem_plusone.

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

Lemma lem_eq2 : forall (A : Type) (s : Stream A), EqSt s s.
Proof.
  coinduction on s.
Qed.

Print lem_eq2.

CoFixpoint plusone s := match s with Cons x t => Cons (x + 1) (plusone t) end.
CoFixpoint ones := Cons 1 ones.
CoFixpoint plus s1 s2 := match s1, s2 with Cons x1 t1, Cons x2 t2 => Cons (x1 + x2) (plus t1 t2) end.

CoInduction lem_plusone : forall s, EqSt (plus s ones) (plusone s).
Proof.
  csolve on s.
Qed.

Print lem_plusone.

CoInduction lem_plusone_1 : forall s, EqSt (plus s ones) (plusone s).
Proof.
  yelles 2.
Qed.

Lemma lem_plusone_2 : forall s, EqSt (plus s ones) (plusone s).
Proof.
  coinduction on s.
Qed.

CoInductive EqSt2 {A : Type} : Stream A -> Stream A -> Prop :=
| eqst2 : forall x y s1 s2, x = y -> EqSt2 s1 s2 -> EqSt2 (Cons x s1) (Cons y s2).

CoInduction lem_st_to_st2 : forall (A : Type) (s1 s2 : Stream A), EqSt s1 s2 -> EqSt2 s1 s2.
Proof.
  destruct s1 eqn:?, s2 eqn:?.
  intro H; inversion H.
  ccrush.
Qed.

Lemma lem_st2_to_st : forall (A : Type) (s1 s2 : Stream A), EqSt2 s1 s2 -> EqSt s1 s2.
Proof.
  coinduction.
Qed.

CoInduction lem_ex : forall (A : Type) (s : Stream A), exists s', EqSt2 s s'.
Proof.
  csolve on s using yelles 2.
Qed.

CoInduction lem_two : forall (A : Type) (s1 s2 : Stream A), EqSt s1 s2 -> EqSt s2 s1 /\ EqSt s1 s2.
Proof.
  yelles 2.
Qed.

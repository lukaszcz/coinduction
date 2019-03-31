From Coinduction Require Import Coinduction.

CoInductive Stream (A : Type) : Type :=
| cons : A -> Stream A -> Stream A.

Arguments cons [A] _ _.

CoInductive EqSt {A : Type} : Stream A -> Stream A -> Prop :=
| eqst : forall x s1 s2, EqSt s1 s2 -> EqSt (cons x s1) (cons x s2).

Notation "A == B" := (EqSt A B) (at level 70).

CoInduction lem_refl : forall {A : Type} (s : Stream A), s == s.
Proof.
  ccrush.
Qed.

CoInduction lem_sym : forall {A : Type} (s1 s2 : Stream A), s1 == s2 -> s2 == s1.
Proof.
  ccrush.
Qed.

CoInduction lem_trans : forall {A : Type} (s1 s2 s3 : Stream A), s1 == s2 -> s2 == s3 -> s1 == s3.
Proof.
  destruct 1; ccrush.
Qed.

Lemma lem_trans_2 : forall {A : Type} (s1 s2 s3 : Stream A), s1 == s2 -> s2 == s3 -> s1 == s3.
Proof.
  cofix CH.
  intros A s1 s2 s3 H1 H2.
  destruct H1; inversion H2; constructor; eauto.
Qed.

Declare_peek Stream.

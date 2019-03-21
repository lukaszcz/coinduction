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
  intros A s1 s2 s3 H1 H2.
  destruct H1; inversion H2; ccrush.
Qed.

Definition sunf {A} (s : Stream A) :=
  match s with cons n s' => cons n s' end.

Lemma sunf_eq : forall {A} (s : Stream A), s = sunf s.
Proof.
  destruct s; auto.
Qed.

CoFixpoint enumerate (n : nat) : Stream nat :=
  cons n (enumerate (S n)).

CoFixpoint map (f : nat -> nat) s : Stream nat :=
  match s with cons n s' => cons (f n) (map f s') end.

CoInduction example : forall n, (enumerate n) == (cons n (map S (enumerate n))).
Proof.
  intros.
  (* rewrite sunf_eq at 1; simpl. *)
  pattern (enumerate n) at 1; rewrite sunf_eq; simpl.
  constructor.
  rewrite (sunf_eq (enumerate n)); simpl.
  rewrite (sunf_eq (map _ _)); simpl.
  apply CH.
Qed.

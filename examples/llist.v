From Coinduction Require Import Coinduction.

CoInductive LList (A : Type) : Type :=
| nil : LList A
| cons : A -> LList A -> LList A.

Arguments nil [A].
Arguments cons [A] _ _.

Declare_peek LList.

CoInductive EqLList {A : Type} : LList A -> LList A -> Prop :=
| eqnil : EqLList nil nil
| eqcons : forall x s1 s2, EqLList s1 s2 -> EqLList (cons x s1) (cons x s2).

Notation "A == B" := (EqLList A B) (at level 70).

CoInduction lem_refl : forall {A : Type} (s : LList A), s == s.
Proof. ccrush. Qed.

CoInduction lem_sym : forall {A : Type} (s1 s2 : LList A), s1 == s2 -> s2 == s1.
Proof. ccrush. Qed.

CoInduction lem_trans :
  forall {A : Type} (s1 s2 s3 : LList A), s1 == s2 -> s2 == s3 -> s1 == s3.
Proof. destruct 1; ccrush. Qed.

CoInductive Infinite {A : Type} : LList A -> Prop :=
| infcons : forall x s, Infinite s -> Infinite (cons x s).

CoFixpoint append {A : Type} (s1 s2 : LList A) : LList A :=
  match s1 with
  | nil => s2
  | cons x s1' => cons x (append s1' s2)
  end.

CoInduction lem_inf_app :
  forall {A : Type} (s1 s2 : LList A), Infinite s1 -> append s1 s2 == s1.
Proof.
  intros A s1 s2 H.
  destruct H as [x s].
  peek (append (cons x s) s2).
  ccrush.
Qed.

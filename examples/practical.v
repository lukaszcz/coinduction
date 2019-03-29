From Coinduction Require Import Coinduction.

CoInductive Stream (A : Type) : Type :=
| cons : A -> Stream A -> Stream A.

Arguments cons [A] _ _.

Require Import Classes.RelationClasses.
Require Import Relations.

CoInductive Lex {A : Type} (R : relation A) : Stream A -> Stream A -> Prop :=
| lex_1 : forall x y s1 s2, R x y -> Lex R (cons x s1) (cons y s2)
| lex_2 : forall x s1 s2, Lex R s1 s2 -> Lex R (cons x s1) (cons x s2).

CoInduction lem_lex : forall (A : Type) (x y z : Stream A) (R : relation A), Transitive R ->
                                                                             Lex R x y -> Lex R y z -> Lex R x z.
Proof.
  destruct 2; ccrush.
Qed.

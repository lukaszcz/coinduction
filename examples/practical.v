From Coinduction Require Import Coinduction.

CoInductive Stream (A : Type) : Type :=
| cons : A -> Stream A -> Stream A.

Arguments cons [A] _ _.

Declare_peek Stream.

Require Import Classes.RelationClasses.
Require Import Relations.

(*******************************************************)
(* 3.1. Lexicographic order on streams                 *)

(* R is supposed to be a strict order *)
CoInductive Lex {A : Type} (R : relation A) : Stream A -> Stream A -> Prop :=
| lex_1 : forall x y s1 s2, R x y -> Lex R (cons x s1) (cons y s2)
| lex_2 : forall x s1 s2, Lex R s1 s2 -> Lex R (cons x s1) (cons x s2).

CoInduction lem_lex :
  forall (A : Type) (x y z : Stream A) (R : relation A),
    Transitive R -> Lex R x y -> Lex R y z -> Lex R x z.
Proof.
  destruct 2; ccrush.
Qed.

CoFixpoint plus s1 s2 :=
  match s1, s2 with cons x1 t1, cons x2 t2 => cons (x1 + x2) (plus t1 t2) end.

Lemma lem_plus : forall x y s1 s2, plus (cons x s1) (cons y s2) = cons (x + y) (plus s1 s2).
Proof.
  peek_eq.
Qed.

CoInduction lem_monotone :
  forall (s1 s2 t1 t2 : Stream nat),
    Lex lt s1 t1 -> Lex lt s2 t2 -> Lex lt (plus s1 s2) (plus t1 t2).
Proof.
  destruct 1, 1; do 2 rewrite lem_plus; ccrush.
Qed.

(*******************************************************)
(* 3.2. Recursive types                                *)

CoInductive RecTy : Type :=
| bot : RecTy
| top : RecTy
| arr : RecTy -> RecTy -> RecTy.

CoInductive LeTy : RecTy -> RecTy -> Prop :=
| le_bot : forall x, LeTy bot x
| le_top : forall x, LeTy x top
| le_arr : forall x1 x2 y1 y2, LeTy y1 x1 -> LeTy x2 y2 -> LeTy (arr x1 x2) (arr y1 y2).

CoInduction lem_lety_trans : forall x y z, LeTy x y -> LeTy y z -> LeTy x z.
Proof.
  destruct 1; ccrush.
Qed.

(*******************************************************)
(* 3.4. Bisimilarity                                   *)

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

CoInduction lem_trans :
  forall {A : Type} (s1 s2 s3 : Stream A), s1 == s2 -> s2 == s3 -> s1 == s3.
Proof.
  destruct 1; ccrush.
Qed.

CoFixpoint split1 {A : Type} (s : Stream A) :=
  match s with cons x (cons _ s') => cons x (split1 s') end.

CoFixpoint split2 {A : Type} (s : Stream A) :=
  match s with cons _ (cons x s') => cons x (split2 s') end.

CoFixpoint merge {A : Type} (s1 s2 : Stream A) :=
  match s1, s2 with cons x s1', cons y s2' => cons x (cons y (merge s1' s2')) end.

Lemma lem_split1 :
  forall A x y (s : Stream A), split1 (cons x (cons y s)) = cons x (split1 s).
Proof.
  peek_eq.
Qed.

Lemma lem_split2 :
  forall A x y (s : Stream A), split2 (cons x (cons y s)) = cons y (split2 s).
Proof.
  peek_eq.
Qed.

Lemma lem_merge :
  forall A x y (s1 s2 : Stream A), merge (cons x s1) (cons y s2) = cons x (cons y (merge s1 s2)).
Proof.
  peek_eq.
Qed.

CoInduction lem_merge_split : forall {A} (s : Stream A), merge (split1 s) (split2 s) == s.
Proof.
  destruct s as [a s].
  destruct s as [b s].
  rewrite lem_split1.
  rewrite lem_split2.
  rewrite lem_merge.
  constructor; ccrush.
Qed.

CoFixpoint merge2 {A : Type} (s1 s2 : Stream A) :=
  match s1 with cons x s1' => cons x (merge2 s2 s1') end.

Lemma lem_merge2 :
  forall A x (s1 s2 : Stream A), merge2 (cons x s1) s2 = cons x (merge2 s2 s1).
Proof.
  peek_eq.
Qed.

CoInduction lem_merge2_split : forall {A} (s : Stream A), merge2 (split1 s) (split2 s) == s.
Proof.
  destruct s as [a s].
  destruct s as [b s].
  rewrite lem_split1.
  rewrite lem_split2.
  do 2 rewrite lem_merge2.
  constructor; ccrush.
Qed.

CoFixpoint enumerate (n : nat) : Stream nat :=
  cons n (enumerate (S n)).

CoFixpoint map (f : nat -> nat) s : Stream nat :=
  match s with cons n s' => cons (f n) (map f s') end.

CoInduction lem_enumerate : forall n, enumerate n == cons n (map S (enumerate n)).
Proof.
  intro n.
  peek (enumerate n).
  constructor.
  peek (map S (cons n (enumerate (S n)))).
  apply CH.
Qed.

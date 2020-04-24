From Coinduction Require Import Coinduction.
Require Lists.Streams.
From Hammer Require Import Tactics.

CoInduction lem_eq : forall (A : Type) (s : Streams.Stream A), Streams.EqSt s s.
Proof.
  cauto.
Qed.

Import Lists.Streams.

CoInduction lem_eq_nat : forall s : Stream nat, EqSt s s.
Proof.
  cauto.
Qed.

Print lem_eq.

From Coinduction Require Import Tactics.

Lemma lem_eq2 : forall (A : Type) (s : Stream A), EqSt s s.
Proof.
  coinduction on s.
Qed.

Print lem_eq2.

CoInduction lem_sym : forall (A : Type) (s1 s2 : Stream A), EqSt s1 s2 -> EqSt s2 s1.
Proof.
  inversion 1; cauto.
Qed.

CoInduction lem_trans : forall (A : Type) (s1 s2 s3 : Stream A), EqSt s1 s2 -> EqSt s2 s3 -> EqSt s1 s3.
Proof.
  intros A s1 s2 s3 H1 H2.
  inversion_clear H1.
  inversion_clear H2.
  cauto.
Qed.

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
  cauto.
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
  inversion 1; cauto.
Qed.

Print lem_st_to_st2.

CoInduction lem_st2_to_st : forall (A : Type) (s1 s2 : Stream A), EqSt2 s1 s2 -> EqSt s1 s2.
Proof.
  inversion 1; cauto.
Qed.

Print lem_st2_to_st.

Lemma lem_st2_to_st' : forall (A : Type) (s1 s2 : Stream A), EqSt2 s1 s2 -> EqSt s1 s2.
Proof.
  coinduction CH on hyp 3.
Qed.

CoInduction lem_two : forall (A : Type) (s1 s2 : Stream A), EqSt s1 s2 -> EqSt s2 s1 /\ EqSt s1 s2.
Proof.
  inversion 1; cauto.
Qed.

Print lem_two.

CoInduction lem_ex : forall (A : Type) (s : Stream A), exists s', EqSt2 s s'.
Proof.
  cauto.
Qed.

Print lem_ex.

CoInduction lem_ex_2 : forall (A : Type) (s : Stream A), exists s', EqSt2 s' s.
Proof.
  cauto.
Qed.

Print lem_ex_2.

CoInductive EqSt3 {A : Type} : Stream A -> Stream A -> Type :=
| eqst3 : forall x s1 s2, EqSt3 s1 s2 -> EqSt3 (Cons x s1) (Cons x s2).

CoInduction lem_ex_impl : forall (A : Type) (s1 s2 : Stream A), EqSt3 s1 s2 -> exists s, EqSt2 s1 s.
Proof.
  intros A s1 s2 H.
  inversion_clear H.
  generalize (CH A s0 s3 X); intro HH.
  cauto.
Qed.

Print lem_ex_impl.

CoInductive PlusSt : Stream nat -> Stream nat -> Stream nat -> Prop :=
| plus_st : forall x y s1 s2 s3, PlusSt s1 s2 s3 ->
                                 PlusSt (Cons x s1) (Cons y s2) (Cons (x + y) s3).

Lemma lem_plus : forall s1 s2 x y, plus (Cons x s1) (Cons y s2) = Cons (x + y) (plus s1 s2).
Proof.
  intros.
  rewrite <- (peek_eq__Stream nat) at 1.
  cauto.
Qed.

CoInduction lem_plus_st : forall s1 s2, PlusSt s1 s2 (plus s1 s2).
Proof.
  destruct s1 eqn:?, s2 eqn:?.
  rewrite lem_plus.
  cauto.
Qed.

CoInductive GeqSt : Stream nat -> Stream nat -> Prop :=
| geq_eq_st : forall x s1 s2, GeqSt s1 s2 -> GeqSt (Cons x s1) (Cons x s2)
| geq_gt_st : forall x y s1 s2, x > y -> GeqSt s1 s2 -> GeqSt (Cons x s1) (Cons x s2).

CoInductive GeqSt2 : Stream nat -> Stream nat -> Set :=
| geq_eq_st2 : forall x s1 s2, GeqSt2 s1 s2 -> GeqSt2 (Cons x s1) (Cons x s2)
| geq_gt_st2 : forall x y s1 s2, x > y -> GeqSt2 s1 s2 -> GeqSt2 (Cons x s1) (Cons x s2).

CoInduction lem_geq : forall s1 s2, GeqSt2 s1 s2 -> exists s, GeqSt s1 s /\ GeqSt s s2.
Proof.
  intros s1 s2 H.
  inversion_clear H; scrush.
Qed.

Print lem_geq.

CoInduction lem_geq_1 : forall s1 s2, GeqSt2 s1 s2 -> exists s, GeqSt s1 s /\ GeqSt s s2.
Proof.
  intros s1 s2 H.
  destruct H; scrush.
Qed.

Print lem_geq_1.

CoInductive I : Set :=
| c : I -> I.

CoInductive R : I -> Prop :=
| r : forall x, R x -> R (c x).

CoInductive S : I -> Set :=
| s : forall x, S x -> S (c x).

CoInduction lem_eex : forall x : I, exists y, R y.
Proof.
  intro x.
  destruct x.
  destruct (CH x) as [y H].
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

CoInduction lem_eex_2 : forall x : I, exists y, R y.
Proof.
  intro x.
  destruct x.
  destruct x.
  destruct (CH (c x)) as [y H].
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

CoInduction lem_eex_3 : forall x : I, S x -> exists y, R y.
Proof.
  intros x H.
  destruct H.
  destruct (CH x) as [y H1].
  assumption.
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

CoInduction lem_eex_4 : forall (x1 x2 : I), S x1 -> S x2 -> exists y, R y.
Proof.
  intros x1 x2 H1 H2.
  inversion_clear H1.
  inversion_clear H2.
  destruct (CH x x0 H H0) as [y HH].
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

Inductive term : Set :=
| var : nat -> term
| app : term -> term -> term.

CoInductive exteq : term -> term -> Prop :=
| app_eq : forall t s, (forall q, exteq (app t q) (app s q)) -> exteq t s.

Lemma lem_eeq : forall t, exteq t t.
Proof.
  coinduction.
Qed.

CoInduction lem_eeq_2 : forall t, exteq t t.
Proof.
  cauto.
Qed.

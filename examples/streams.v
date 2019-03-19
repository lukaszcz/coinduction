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

CoInduction lem_sym : forall (A : Type) (s1 s2 : Stream A), EqSt s1 s2 -> EqSt s2 s1.
Proof.
  ccrush.
Qed.

CoInduction lem_trans : forall (A : Type) (s1 s2 s3 : Stream A), EqSt s1 s2 -> EqSt s2 s3 -> EqSt s1 s3.
Proof.
  intros A s1 s2 s3 H1 H2.
  inversion_clear H1.
  inversion_clear H2.
  ccrush.
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
  ccrush.
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
  ccrush.
Qed.

Print lem_st_to_st2.

CoInduction lem_st2_to_st : forall (A : Type) (s1 s2 : Stream A), EqSt2 s1 s2 -> EqSt s1 s2.
Proof.
  ccrush.
Qed.

Print lem_st2_to_st.

Lemma lem_st2_to_st' : forall (A : Type) (s1 s2 : Stream A), EqSt2 s1 s2 -> EqSt s1 s2.
Proof.
  coinduction.
Qed.

CoInduction lem_two : forall (A : Type) (s1 s2 : Stream A), EqSt s1 s2 -> EqSt s2 s1 /\ EqSt s1 s2.
Proof.
  yelles 2.
Qed.

Print lem_two.

CoInduction lem_ex : forall (A : Type) (s : Stream A), exists s', EqSt2 s s'.
Proof.
  csolve on s.
Qed.

Print lem_ex.

CoInduction lem_ex_2 : forall (A : Type) (s : Stream A), exists s', EqSt2 s' s.
Proof.
  csolve on s.
Qed.

Print lem_ex_2.

CoInduction lem_ex_two : forall (A : Type) (s : Stream A), exists s', EqSt2 s s' /\ EqSt2 s' s.
Proof.
  csolve on s.
Qed.

Print lem_ex_two.

CoInduction lem_ex_ex_two :
  forall (A : Type) (s : Stream A), exists s1 s2, EqSt2 s s1 /\ EqSt2 s2 s.
Proof.
  csolve on s.
Qed.

Print lem_ex_ex_two.

CoInductive EqSt3 {A : Type} : Stream A -> Stream A -> Type :=
| eqst3 : forall x s1 s2, EqSt3 s1 s2 -> EqSt3 (Cons x s1) (Cons x s2).

CoInduction lem_ex_impl : forall (A : Type) (s1 s2 : Stream A), EqSt3 s1 s2 -> exists s, EqSt2 s1 s.
Proof.
  intros A s1 s2 H.
  inversion_clear H.
  generalize (CH A s0 s3 X); intro HH.
  destruct HH as [ s H ].
  eexists; constructor; eauto.
Qed.

Print lem_ex_impl.

CoInductive PlusSt : Stream nat -> Stream nat -> Stream nat -> Prop :=
| plus_st : forall x y s1 s2 s3, PlusSt s1 s2 s3 ->
                                 PlusSt (Cons x s1) (Cons y s2) (Cons (x + y) s3).

Lemma lem_plus : forall s1 s2 x y, plus (Cons x s1) (Cons y s2) = Cons (x + y) (plus s1 s2).
Proof.
  intros.
  rewrite <- (peek_eq__Stream nat) at 1.
  ccrush.
Qed.

CoInduction lem_plus_st : forall s1 s2, PlusSt s1 s2 (plus s1 s2).
Proof.
  destruct s1 eqn:?, s2 eqn:?.
  rewrite lem_plus.
  ccrush.
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
  inversion_clear H; ccrush.
Qed.

Print lem_geq.

CoInduction lem_geq_1 : forall s1 s2, GeqSt2 s1 s2 -> exists s, GeqSt s1 s /\ GeqSt s s2.
Proof.
  intros s1 s2 H.
  destruct H; ccrush.
Qed.

Print lem_geq_1.

CoInduction lem_geq_2 : forall s1 s2, GeqSt2 s1 s2 -> exists s, GeqSt s1 s /\ GeqSt s s2.
Proof.
  intros s1 s2 H.
  inversion H; ccrush.
Qed.

Print lem_geq_2.

CoInduction lem_geq_3 : forall s1 s2, GeqSt2 s1 s2 -> exists s, GeqSt s1 s /\ GeqSt s s2.
Proof.
  intros s1 s2 H.
  inversion H; subst; clear H; ccrush.
Qed.

Print lem_geq_3.

(*
CoInductive MinusSt : Stream nat -> Stream nat -> Stream nat -> Set :=
| minus_st : forall x y s1 s2 s3, MinusSt s1 s2 s3 ->
                                  MinusSt (Cons x s1) (Cons y s2) (Cons (x - y) s3).

Require Import Omega.

CoInduction lem_minus : forall s1 s2 s3, GeqSt2 s1 s2 -> MinusSt s1 s2 s3 -> exists s, PlusSt s3 s s1.
Proof.
  intros s1 s2 s3 H1 H2.
  inversion H1 as [x y t1 t2 H0]; subst.
  inversion_clear H2 as [x y t1 t2 t3 H0].
  generalize (CH t1 t2 t3 H0); intro HH.
  destruct HH as [s HH1].
  exists (Cons__g Stream__r nat (y - (y - x)) s).
  ccrush.
Qed. *)

(* Set Printing All. *)

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
  ccrush.
Qed.

(* The following don't work with the current version of the plugin *)

CoInduction lem_geq_3 : forall s1 s2, GeqSt2 s1 s2 -> exists s, GeqSt s1 s /\ GeqSt s s2.
Proof.
  intros s1 s2 H.
  inversion H; subst; clear H; ccrush.
Qed.

Print lem_geq_3.

CoInduction lem_eex_5 : forall (x1 x2 : I), S x1 -> S x2 -> exists y, R y.
Proof.
  intros x1 x2 H1 H2.
  destruct H1 as [ x1 H1 ].
  destruct H2 as [ x2 H2 ].
  destruct (CH x1 x2 H1 H2) as [y HH].
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

Check (let
   cofix H (x1 x2 : I) (H1 : S x1) (H2 : S x2) : I :=
     match H1 with
     | s x3 H3 => match H2 with
                  | s x4 H4 => c (H x3 x4 H3 H4)
                  end
     end in
 let
   cofix H0 (x1 x2 : I) (H1 : S x1) (H2 : S x2) : R (H x1 x2 H1 H2) :=
     eq_rect (peek__I (H x1 x2 H1 H2)) (fun y : I => R y)
       match H1 as s in (S i) return (R (peek__I (H i x2 s H2))) with
       | s x3 H3 =>
           match H2 as s0 in (S i) return (R (peek__I (H (c x3) i (s x3 H3) s0))) with
           | s x4 H4 => r (H x3 x4 H3 H4) (H0 x3 x4 H3 H4)
           end
       end (H x1 x2 H1 H2) (peek_eq__I (H x1 x2 H1 H2)) in
 fun (x1 x2 : I) (H1 : S x1) (H2 : S x2) => ex_intro (fun y : I => R y) (H x1 x2 H1 H2) (H0 x1 x2 H1 H2)).


CoInductive Q : I -> I -> Prop :=
| q : forall x y, Q x y -> Q x (c y).

Check (let cofix H (x : I) : I := match x with
                            | c _ => c (H x)
                            end in
 let
   cofix H0 (x : I) : Q x (H x) :=
     eq_rect (peek__I (H x)) (fun y : I => Q x y)
       match x as x0 return (Q x0 (peek__I (H x0))) with
       | c x0 => q (c x0) (H (c x0)) (H0 (c x0))
       end (H x) (peek_eq__I (H x)) in
 fun x : I => ex_intro (fun y : I => Q x y) (H x) (H0 x)).

CoInduction lem_eex_3 : forall x : I, exists y, Q x y.
Proof.
  intro x.
  refine (match x as x0 return (exists y : I__g I__r, Q__g__01 I__r Q__r__01 x y) with c x0 => _ end).
  destruct (CH x) as [y H].
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

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

Check (let
   cofix H (A : Type) (s1 s2 : Stream A) (H0 : EqSt3 s1 s2) : Stream A :=
     match H0 in (EqSt3 s s0) return (s = s1 -> s0 = s2 -> Stream A) with
     | eqst3 x s0 s3 X =>
         fun (H1 : Cons x s0 = s1) (H2 : Cons x s3 = s2) =>
         match H1 with
         | eq_refl =>
             fun H3 : Cons x s3 = s2 => match H3 with
                                        | eq_refl => fun X0 : EqSt3 s0 s3 => Cons x (H A s0 s3 X0)
                                        end
         end H2 X
     end eq_refl eq_refl in
 let
   cofix H0 (A : Type) (s1 s2 : Stream A) (H1 : EqSt3 s1 s2) : EqSt2 s1 (H A s1 s2 H1) :=
     eq_ind (peek__Stream A (H A s1 s2 H1)) (fun s : Stream A => EqSt2 s1 s)
       (match H1 as H2 in (EqSt3 s s0) return (s = s1 -> s0 = s2 -> EqSt2 s1 (peek__Stream A (H A s s0 H2))) with
        | eqst3 x s0 s3 X =>
            fun (H2 : Cons x s0 = s1) (H3 : Cons x s3 = s2) =>
              match H2 in (_ = y) return (Cons x s3 = s2 -> forall X0 : EqSt3 s0 s3,
                                             EqSt2 y (peek__Stream A (H A (Cons x s0) (Cons x s3) (eqst3 x s0 s3 X0))))
              with
              | eq_refl =>
                fun H4 : Cons x s3 = s2 =>
                match H4 with
                | eq_refl => fun X0 => eqst2 x x s0 (H A s0 s3 X0) eq_refl (H0 A s0 s3 X0)
                end
              end H3 X
        end eq_refl eq_refl) (H A s1 s2 H1) (peek_eq__Stream A (H A s1 s2 H1)) in
 fun (A : Type) (s1 s2 : Stream A) (H1 : EqSt3 s1 s2) =>
 ex_intro (fun s : Stream A => EqSt2 s1 s) (H A s1 s2 H1) (H0 A s1 s2 H1)).

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

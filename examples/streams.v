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

Definition peek {A:Type} (s : Stream A) : Stream A :=
  match s with
  | Cons a s0 => Cons a s0
  end.

Lemma peek_eq : forall {A} (s : Stream A), peek s = s.
Proof.
  ccrush.
Qed.

Check (let H := (cofix H (A : Type) (s : Stream A) : Stream A := match s with
                                                              | Cons a s0 => Cons a (H A s0)
                                                              end) in
  (fun (H0 : forall (A : Type) (s : Stream A), EqSt2 s (H A s)) (A : Type) (s : Stream A) =>
   ex_intro (fun s' : Stream A => EqSt2 s s') (H A s) (H0 A s))
    (cofix H0 (A : Type) (s : Stream A) : EqSt2 s (H A s) :=
       eq_ind (peek (H A s)) (fun r => EqSt2 s r)
       (match s as s0 return EqSt2 s0 (peek (H A s0)) with
        | Cons a s0 => eqst2 a a s0 (H A s0) eq_refl (H0 A s0)
        end)
       (H A s)
       (peek_eq (H A s))
      )).

Print peek_eq.

Check (let cofix H (A : Type) (s : Stream A) : Stream A := match s with
                                                     | Cons a s0 => Cons a (H A s0)
                                                     end in
 let
   cofix H0 (A : Type) (s : Stream A) : EqSt2 s (H A s) :=
     match s as s0 return (s0 = s -> EqSt2 s0 (H A s)) with
     | Cons a s0 =>
       (fun H1 =>
          eq_ind (Cons a s0)
                 (fun r => EqSt2 (Cons a s0) (H A r))
                 (eq_ind (peek (H A (Cons a s0)))
                          (fun r => EqSt2 (Cons a s0) r)
                          (eqst2 a a s0 (H A s0) eq_refl (H0 A s0))
                          (H A (Cons a s0))
                          (peek_eq (H A (Cons a s0))))
                 s
                 H1)
     end eq_refl in
 fun (A : Type) (s : Stream A) => ex_intro (fun s' : Stream A => EqSt2 s s') (H A s) (H0 A s)).

CoInduction lem_ex : forall (A : Type) (s : Stream A), exists s', EqSt2 s s'.
Proof.
  csolve on s.
Qed.

CoInduction lem_ex_two : forall (A : Type) (s : Stream A), exists s', EqSt2 s s' /\ EqSt2 s' s.
Proof.
  csolve on s.
Qed.

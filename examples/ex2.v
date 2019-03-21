From Coinduction Require Import Coinduction.

CoInductive I : Set :=
| c : I -> I.

CoInductive R : I -> Prop :=
| r : forall x, R x -> R (c x).

CoInductive S : I -> Set :=
| s : forall x, S x -> S (c x).

CoInduction lem_ex : forall x : I, exists y, R y.
Proof.
  intro x.
  destruct x.
  destruct (CH x) as [y H].
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

CoInduction lem_ex_2 : forall x : I, exists y, R y.
Proof.
  intro x.
  destruct x.
  destruct x.
  destruct (CH (c x)) as [y H].
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

CoInduction lem_ex_3 : forall x : I, S x -> exists y, R y.
Proof.
  intros x H.
  destruct H.
  destruct (CH x) as [y H1].
  assumption.
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

CoInduction lem_ex_4 : forall (x1 x2 : I), S x1 -> S x2 -> exists y, R y.
Proof.
  intros x1 x2 H1 H2.
  inversion_clear H1.
  inversion_clear H2.
  destruct (CH x x0 H H0) as [y HH].
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

CoInduction lem_ex_5 : forall (x1 x2 : I), S x1 -> S x2 -> exists y, R y.
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

Check (let cofix H (x : I) : I := match x with
                            | c _ => c (H x)
                            end in
 let
   cofix H0 (x : I) : Q x (H x) :=
     eq_rect (peek__I (H x)) (fun y : I => Q x y)
       match x as x0 return (Q x (peek__I (H x0))) with
       | c _ => q x (H x) (H0 x)
       end (H x) (peek_eq__I (H x)) in
 fun x : I => ex_intro (fun y : I => Q x y) (H x) (H0 x)).

CoInduction lem_ex_3 : forall x : I, exists y, Q x y.
Proof.
  intro x.
  refine (match x as x0 return (exists y : I__g I__r, Q__g__01 I__r Q__r__01 x y) with c x0 => _ end).
  destruct (CH x) as [y H].
  exists (c__g I__r y).
  constructor.
  assumption.
Qed.

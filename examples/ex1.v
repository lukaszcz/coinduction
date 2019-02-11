From Coinduction Require Import Coinduction.

Inductive term : Set :=
| var : nat -> term
| app : term -> term -> term.

CoInductive exteq : term -> term -> Prop :=
| app_eq : forall t s, (forall q, exteq (app t q) (app s q)) -> exteq t s.

Lemma lem_eq : forall t, exteq t t.
Proof.
  coinduction.
Qed.

CoInduction lem_eq_2 : forall t, exteq t t.
Proof.
  ccrush.
Qed.

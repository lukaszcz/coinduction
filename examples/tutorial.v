From Coinduction Require Import Coinduction.

Open Scope type_scope.

CoInductive term : Set :=
| C : nat -> term
| A : term -> term
| B : term -> term -> term.

CoInductive Eq : term -> term -> Set :=
| eq_C : forall i, Eq (C i) (C i)
| eq_A : forall t t', Eq t t' -> Eq (A t) (A t')
| eq_B : forall s s' t t', Eq s s' -> Eq t t' -> Eq (B s t) (B s t').

Notation "A == B" := (Eq A B) (at level 70).

CoInduction lem_eq_refl : forall t, t == t.
Proof.
  ccrush.
Qed.

Print lem_eq_refl.

CoInduction lem_eq_sym : forall s t, s == t -> t == s.
Proof.
  ccrush.
Qed.

CoInduction lem_eq_trans : forall t1 t2 t3, t1 == t2 -> t2 == t3 -> t1 == t3.
Proof.
  intros t1 t2 t3 H1 H2.
  destruct H1; inversion_clear H2; econstructor; eauto.
Qed.

CoInductive Red : term -> term -> Set :=
| red_C : forall i, Red (C i) (C i)
| red_A : forall t t', Red t t' -> Red (A t) (A t')
| red_B : forall s s' t t', Red s s' -> Red t t' -> Red (B s t) (B s' t')
| red_AB : forall t t1 t2, Red t t1 -> Red t t2 -> Red (A t) (B t1 t2).

Notation "A ==> B" := (Red A B) (at level 70).

CoInduction lem_red_refl : forall t, t ==> t.
Proof.
  ccrush.
Qed.

CoInduction lem_eq_to_red : forall t1 t2, t1 == t2 -> t1 ==> t2.
Proof.
  pose lem_eq_refl; ccrush.
Qed.

CoInduction lem_red_trans : forall t1 t2 t3, t1 ==> t2 -> t2 ==> t3 -> t1 ==> t3.
Proof.
  intros t1 t2 t3 H1 H2.
  destruct H1; inversion_clear H2; econstructor; eauto.
Qed.

CoInduction lem_red_ex : forall t, { s & t ==> s }.
Proof.
  intro t.
  destruct t; pose lem_red_refl; ccrush.
Qed.

CoInduction lem_red_confl : forall s t t', s ==> t -> s ==> t' -> { s' & (t ==> s') * (t' ==> s') }.
Proof.
  intros s t t' H1 H2.
  destruct H1.
  - inversion_clear H2; ccrush.
  - inversion_clear H2.
    + generalize (CH t t'0 t'1 H1 H); intro HH.
      destruct HH as [ x [ HH1 HH2 ] ].
      eexists; split; constructor; eauto.
    + generalize (CH t t'0 t1 H1 H); intro HH1.
      generalize (CH t t'0 t2 H1 H0); intro HH2.
      destruct HH1 as [ x [ X1 X2 ] ].
      destruct HH2 as [ y [ Y1 Y2 ] ].
      exists (B__g term__r x y).
      split; constructor; eauto.
  - inversion_clear H2.
    generalize (CH s s' s'0 H1_ H); intro HH1.
    generalize (CH t t'0 t'1 H1_0 H0); intro HH2.
    destruct HH1 as [ x [ X1 X2 ] ].
    destruct HH2 as [ y [ Y1 Y2 ] ].
    eexists; split; constructor; eauto.
  - inversion_clear H2.
    + generalize (CH t t1 t'0 H1_ H); intro HH1.
      generalize (CH t t2 t'0 H1_0 H); intro HH2.
      destruct HH1 as [ x [ X1 X2 ] ].
      destruct HH2 as [ y [ Y1 Y2 ] ].
      exists (B__g term__r x y).
      split; constructor; eauto.
    + generalize (CH t t1 t3 H1_ H); intro HH1.
      generalize (CH t t2 t4 H1_0 H0); intro HH2.
      destruct HH1 as [ x [ X1 X2 ] ].
      destruct HH2 as [ y [ Y1 Y2 ] ].
      eexists; split; constructor; eauto.
Qed.

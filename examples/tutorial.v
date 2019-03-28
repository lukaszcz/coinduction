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

CoInductive Peak : term -> term -> term -> Set :=
| peak_C : forall i, Peak (C i) (C i) (C i)
| peak_A : forall s t t', Peak s t t' -> Peak (A s) (A t) (A t')
| peak_B : forall s t s1 t1 s2 t2, Peak s s1 s2 -> Peak t t1 t2 -> Peak (B s t) (B s1 t1) (B s2 t2)
| peak_AAB : forall s s' t1 t2, Peak s s' t1 -> Peak s s' t2 -> Peak (A s) (A s') (B t1 t2)
| peak_ABA : forall s s' t1 t2, Peak s t1 s' -> Peak s t2 s' -> Peak (A s) (B t1 t2) (A s')
| peak_ABB : forall s s1 s2 t1 t2, Peak s s1 t1 -> Peak s s2 t2 -> Peak (A s) (B s1 s2) (B t1 t2).

CoInduction lem_peak : forall s t t', s ==> t -> s ==> t' -> Peak s t t'.
Proof.
  destruct 1; inversion_clear 1; constructor; eauto.
Qed.

CoInduction lem_peak_rev : forall s t t', Peak s t t' -> (s ==> t) * (s ==> t').
Proof.
  intros s t t' H.
  inversion_clear H.
  - ccrush.
  - generalize (CH s0 t0 t'0 H0); intro.
    simp_hyps; split; constructor; eauto.
  - generalize (CH s0 s1 s2 H0); intro.
    generalize (CH t0 t1 t2 H1); intro.
    simp_hyps; split; constructor; eauto.
  - generalize (CH s0 s' t1 H0); intro.
    generalize (CH s0 s' t2 H1); intro.
    simp_hyps; split; constructor; eauto.
  - generalize (CH s0 t1 s' H0); intro.
    generalize (CH s0 t2 s' H1); intro.
    simp_hyps; split; constructor; eauto.
  - generalize (CH s0 s1 t1 H0); intro.
    generalize (CH s0 s2 t2 H1); intro.
    simp_hyps; split; constructor; eauto.
Qed.

CoInduction lem_confl : forall s t t', Peak s t t' -> { s' & (t ==> s') * (t' ==> s') }.
Proof. intros s t t' H. inversion_clear H.
  - ccrush.
  - generalize (CH s0 t0 t'0 H0); intro.
    simp_hyps; eexists; split; constructor; eauto.
  - generalize (CH s0 s1 s2 H0); generalize (CH t0 t1 t2 H1); intros.
    simp_hyps; eexists; split; constructor; eauto.
  - generalize (CH s0 s' t1 H0); intro.
    generalize (CH s0 s' t2 H1); intro.
    simp_hyps.
    exists (B__g term__r s'1 s'0).
    split; constructor; eauto.
  - generalize (CH s0 t1 s' H0); intro.
    generalize (CH s0 t2 s' H1); intro.
    simp_hyps; eexists; split; constructor; eauto.
  - generalize (CH s0 s1 t1 H0); intro.
    generalize (CH s0 s2 t2 H1); intro.
    simp_hyps; eexists; split; constructor; eauto.
Qed.

Corollary cor_confl : forall s t t', s ==> t -> s ==> t' -> { s' & (t ==> s') * (t' ==> s') }.
Proof.
  eauto using lem_confl, lem_peak.
Qed.

(* The following direct proof doesn't work with the current version of
   the plugin, because it requires two nested dependent eliminations
   on arguments of the implicit corecursive function *)

(*
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
*)

CoInductive Red0 : term -> term -> Prop :=
| red0_C : forall i, Red0 (C i) (C i)
| red0_A : forall t t', Red0 t t' -> Red0 (A t) (A t')
| red0_B : forall s s' t t', Red0 s s' -> Red0 t t' -> Red0 (B s t) (B s' t')
| red0_AB : forall t t1 t2, Red0 t t1 -> Red0 t t2 -> Red0 (A t) (B t1 t2).

Notation "A --> B" := (Red0 A B) (at level 70).

CoInduction lem_red0_refl : forall t, t --> t.
Proof.
  ccrush.
Qed.

CoInduction lem_red_ex_1 : forall t t', t ==> t' -> exists s, t --> s /\ s --> t'.
Proof.
  intros t t' H.
  inversion_clear H; ccrush. (* 10 sec *)
Qed.

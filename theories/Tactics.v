Require Lists.Streams.
From Hammer Require Import Tactics.

Create HintDb chints discriminated.

Hint Rewrite -> Streams.tl_nth_tl : chints.

Ltac csolve0 H tac :=
  intros; autorewrite with chints; cbn;
  solve [ econstructor; cbn;
          solve [ first [ simple eapply H | intros; simple eapply H ]; clear H; tac | try clear H; tac ]
        | try clear H; tac ].

(* "csolve CH" solves the current goal, ensuring that the coinductive
   hypothesis CH is used in a guarded manner *)
Tactic Notation "csolve" hyp(H) := try csolve0 H ltac:(scrush).
Tactic Notation "csolve" hyp(H) "using" tactic(tac) := try csolve0 H tac.

Ltac notPropAtom t :=
  lazymatch type of t with
    | Prop => tryif isAtom t then fail else idtac
    | _ => idtac
  end.

Ltac intros_until_prop_atom_hyp :=
  repeat match goal with
         | [ |- forall x : ?A, _ ] => notPropAtom A; intro
         end.

Ltac coind_solve C tac :=
  intros_until_prop_atom_hyp;
  match goal with
  | [ |- forall _, _ ] =>
    let H := fresh "H" in
    intro H; inversion H; try subst;
    try solve [ csolve0 C tac | coind_solve C tac ]
  | _ =>
    try solve [ csolve0 C tac ]
  end.

Tactic Notation "csolve" hyp(H) "on" "*"  := coind_solve H ltac:(strivial).
Tactic Notation "csolve" hyp(H) "on" "*" "using" tactic(tac) := coind_solve H tac.
Tactic Notation "csolve" "on" "*" := coind_solve 0 ltac:(ccrush).
Tactic Notation "csolve" "on" "*" "using" tactic(tac) := coind_solve 0 tac.

Ltac coind_on_solve C tac :=
  match goal with
  | [ |- forall _ : ?T, _ ] =>
    isProp T;
    let H := fresh "H" in
    intro H; inversion H; try subst;
    try solve [ csolve0 C tac ]
  | [ |- forall n : ?T, _ ] =>
    notProp T;
    let x := fresh n in
    intro x; destruct x; try subst;
    try solve [ csolve0 C tac ]
  | _ =>
    try solve [ csolve0 C tac ]
  end.

Tactic Notation "csolve" hyp(H) "on" "hyp" int_or_var(n) := do n intro; coind_on_solve H ltac:(strivial).
Tactic Notation "csolve" hyp(H) "on" "hyp" int_or_var(n) "using" tactic(tac) := do n intro; coind_on_solve H tac.
Tactic Notation "csolve" "on" "hyp" int_or_var(n) := do n intro; coind_on_solve 0 ltac:(ccrush).
Tactic Notation "csolve" "on" "hyp" int_or_var(n) "using" tactic(tac) := do n intro; coind_on_solve 0 tac.

Tactic Notation "csolve" hyp(H) "on" ident(n) := intros until n; revert n; coind_on_solve H ltac:(strivial).
Tactic Notation "csolve" hyp(H) "on" ident(n) "using" tactic(tac) := intros until n; revert n; coind_on_solve H tac.
Tactic Notation "csolve" "on" ident(n) := intros until n; revert n; coind_on_solve 0 ltac:(ccrush).
Tactic Notation "csolve" "on" ident(n) "using" tactic(tac) := intros until n; revert n; coind_on_solve 0 tac.

Tactic Notation "coinduction" ident(H) := autounfold with shints; cofix H; csolve H using strivial.
Tactic Notation "coinduction" ident(H) "using" tactic(tac) := autounfold with shints; cofix H; csolve H using tac.
Tactic Notation "coinduction" := let H := fresh "CH" in coinduction H using scrush.
Tactic Notation "coinduction" "using" tactic(tac) := let H := fresh "CH" in coinduction H using tac.

Tactic Notation "coinduction" ident(H) "on" "*" :=
  autounfold with shints; cofix H; csolve H on * using strivial.
Tactic Notation "coinduction" ident(H) "on" "*" "using" tactic(tac) :=
  autounfold with shints; cofix H; csolve H on * using tac.
Tactic Notation "coinduction" "on" "*" :=
  let H := fresh "CH" in coinduction H on * using scrush.
Tactic Notation "coinduction" "on" "*" "using" tactic(tac) :=
  let H := fresh "CH" in coinduction H on * using tac.

Tactic Notation "coinduction" ident(H) "on" ident(n) :=
  autounfold with shints; cofix H; csolve H on n using strivial.
Tactic Notation "coinduction" ident(H) "on" ident(n) "using" tactic(tac) :=
  autounfold with shints; cofix H; csolve H on n using tac.
Tactic Notation "coinduction" "on" ident(n) :=
  let H := fresh "CH" in coinduction H on n using scrush.
Tactic Notation "coinduction" "on" ident(n) "using" tactic(tac) :=
  let H := fresh "CH" in coinduction H on n using tac.

Tactic Notation "coinduction" ident(H) "on" "hyp" int_or_var(n) :=
  autounfold with shints; cofix H; csolve H on hyp n using strivial.
Tactic Notation "coinduction" ident(H) "on" "hyp" int_or_var(n) "using" tactic(tac) :=
  autounfold with shints; cofix H; csolve H on hyp n using tac.
Tactic Notation "coinduction" "on" "hyp" int_or_var(n) :=
  let H := fresh "CH" in coinduction H on hyp n using scrush.
Tactic Notation "coinduction" "on" "hyp" int_or_var(n) "using" tactic(tac) :=
  let H := fresh "CH" in coinduction H on hyp n using tac.

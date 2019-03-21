From Coinduction Require Import Coinduction.

CoInductive U : Prop := cnsu : forall (A : Prop), (A -> False) -> A -> U.

Definition g (x : U) : False :=
  match x with
  | cnsu A h a => h a
  end.

CoInduction lem_U : U.
Proof.
  Print U__g.
  (* this proof cannot be finished ... fortunately! *)
Qed.

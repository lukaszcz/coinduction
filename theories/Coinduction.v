Declare ML Module "coinduction_plugin".

Ltac peek t := pattern t; let ty := ltac:(type of t) in rewrite_peek ty; cbn.
Ltac peek_eq := intros; match goal with [ |- ?L = _ ] => peek L; reflexivity end.

From Coq Require Import Relations.

Print relation.

Inductive image (A : Type) (R : relation A): A -> Prop :=
  | Rimage : forall x y, R x y -> image A R x.

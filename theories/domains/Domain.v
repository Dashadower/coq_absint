From AbsInt Require Import ZInf.
From Coq Require Import ZArith.

Class AbstractDomain (A C : Type) := {
  bottom : A;
  join : A -> A -> A;
  order : A -> A -> Prop;
  (* concretize : A -> C;
  abstraction : C -> A; *)

  order_refl : forall (x : A), order x x;
  order_trans : forall (x y z : A), order x y -> order y z -> order x z;
  order_antisymm : forall x y, order x y -> order y x -> x = y;
  join_comm : forall x y, join x y = join y x;
  join_assoc : forall x y z, join (join x y) z = join x (join y z);
  join_idem : forall x, join x x = x;
  join_order_l : forall x y, order x (join x y);
  join_order_r : forall x y, order y (join x y)
}.

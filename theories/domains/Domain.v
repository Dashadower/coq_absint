From AbsInt Require Import ZInf.
From Coq Require Import ZArith.

Class AbstractDomain (Abstraction Concretization : Type) := {
  bottom : Abstraction;
  join : Abstraction -> Abstraction -> Abstraction;
  order : Abstraction -> Abstraction -> Prop;
  (* concretize : A -> Concretization;
  abstraction : Concretization -> A; *)

  order_refl : forall (x : Abstraction), order x x;
  order_trans : forall (x y z : Abstraction), order x y -> order y z -> order x z;
  order_antisymm : forall (x y : Abstraction), order x y -> order y x -> x = y;

  join_comm : forall x y, join x y = join y x;
  join_assoc : forall x y z, join (join x y) z = join x (join y z);
  join_idem : forall x, join x x = x;
  join_order_l : forall x y, order x (join x y);
  join_order_r : forall x y, order y (join x y)
}.

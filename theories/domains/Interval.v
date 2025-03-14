
From AbsInt Require Import Domain.
From AbsInt Require Import ZInf.
From Coq Require Import ZArith.

Inductive IntervalDomain :=
  | Interval : ZInf -> ZInf -> IntervalDomain
  | Bottom : IntervalDomain.

Definition IntervalDomain_Join (A B : IntervalDomain) : IntervalDomain :=
  match A with
  | Interval A0 A1 => 
    match B with
    | Interval B0 B1 => Interval (if ZInfLeb A0 B0 then A0 else B0) (if ZInfLeb B1 A1 then A1 else B1)
    | Bottom => Bottom
    end
  | Bottom => Bottom
  end.

Inductive IntervalDomain_Order : IntervalDomain -> IntervalDomain -> Prop :=
  | IDO_bot : IntervalDomain_Order Bottom Bottom
  | IDO_lhs_bot : forall A, IntervalDomain_Order Bottom A
  | IDO_inc : forall (lh_0 lh_1 rh_0 rh_1 : ZInf), (ZInfLe rh_0 lh_0) -> (ZInfLe lh_1 rh_1) -> IntervalDomain_Order (Interval lh_0 lh_1) (Interval rh_0 rh_1).

Definition IntDomain_Orderb (lhs rhs : IntervalDomain) : bool :=
  match lhs with
  | Interval lhs_0 lhs_1 => 
    match rhs with
    | Interval rhs_0 rhs_1 => if ZInfLeb rhs_0 lhs_0 then (if ZInfLeb lhs_1 rhs_1 then true else false ) else false
    | Bottom => false
    end
  | Bottom => true
  end.

Lemma IntervalDomain_Order_eq_dec : forall lhs rhs,
IntervalDomain_Order lhs rhs <-> IntDomain_Orderb lhs rhs = true.
Proof.
  split; generalize dependent rhs.
  - induction lhs; intros.

Lemma IntervalDomain_order_refl : forall A,
  IntervalDomain_Order A A.
Proof.
  intros.
  induction A.
  - apply IDO_inc.
    + apply ZILe_refl.
    + apply ZILe_refl.
  - apply IDO_bot.
Qed.

Lemma IntervalDomain_order_trans : forall x y z,
  IntervalDomain_Order x y -> IntervalDomain_Order y z -> IntervalDomain_Order x z.
Proof.
  intros x.
  induction x.
  - intros y. destruct y.
    + intros. inversion H. subst. inversion H0. subst. apply IDO_inc.
      * apply (ZInfLe_trans rh_0 z1 z) in H3; assumption.
      * apply (ZInfLe_trans z0 z2 rh_1) in H6; assumption.
    + intros. inversion H.
  - intros y. destruct y.
    + intros. apply IDO_lhs_bot.
    + intros. apply IDO_lhs_bot.
Qed.

Lemma IntervalDomain_order_antisym : forall x y,
IntervalDomain_Order x y -> IntervalDomain_Order y x -> x = y.
Proof.
  intros x.
  induction x; intros.
  - inversion H. subst. inversion H0. subst. apply ZInfLe_antisymm in H3.
    + subst. apply ZInfLe_antisymm in H5.
      * subst. reflexivity.
      * assumption.
    + assumption.
  - inversion H0; reflexivity.
Qed. 

Open Scope Z_scope.

Definition i1 := Interval (Znum 1) (Znum 5).
Definition i2 := Interval (Znum (-5)) Zposinf.


Instance IntervalAbstractDomain : AbstractDomain IntervalDomain ZInf := {
  bottom := Bottom;
  join := IntervalDomain_Join;
  order := IntervalDomain_Order;

  order_refl := IntervalDomain_order_refl;
  order_trans := IntervalDomain_order_trans;
  order_antisym := IntervalDomain_order_antisym;
}.
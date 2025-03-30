Print LoadPath.
From AbsInt.ZImp Require Import ZImp_partial.
From AbsInt Require Import Maps.
From Coq Require Import ZArith.
From AbsInt.ZImp Require Import ZImp_partial_eval.



Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition examplepmap :=
  ("Church" |-> 1 ; "Turing" |-> 2).

Print examplepmap.

Compute update examplepmap "Curry" 2.

Definition test_prog : com := <{
  X := 1 ;
  Y := 2 ;
  while Y > X do
  X := X + 0
  end
  }>.

Compute ceval_func (CNormal empty_st) test_prog 100.
Print LoadPath.
From AbsInt.ZImp Require Import ZImp_partial.
From AbsInt Require Import Maps.
From Coq Require Import ZArith.
From Coq Require Import Nat.

Inductive ceval_func_result : Type :=
  | CFTerminates (st : ceval_result)
  | CFDiverges.

Fixpoint ceval_func (st : ceval_result) (c : com) (fuel : nat) : ceval_func_result :=
  match fuel with
  | 0%nat => CFDiverges
  | S fuel' => 
    match st with
    | CError => CFTerminates CError
    | CNormal st' =>
      match c with
      | CSkip => CFTerminates st
      | CAsgn var_name a_exp => 
        match (aeval st' a_exp) with
        | ANormal a' => CFTerminates (CNormal (var_name |-> a' ; st'))
        | AError => CFTerminates CError
        end
      | CSeq c1 c2 =>
        match (ceval_func st c1 fuel') with
        | CFDiverges => CFDiverges
        | CFTerminates st'' => (ceval_func st'' c2 fuel')
        end
      | CIf b c1 c2 => 
        match (beval st' b) with
        | BError => CFTerminates CError
        | BNormal b' => 
          match b' with
          | true => ceval_func st c1 fuel'
          | false => ceval_func st c2 fuel'
          end
        end
      | CWhile b cbody =>
        match (beval st' b) with
        | BError => CFTerminates CError
        | BNormal b' =>
          match b' with
          | true => 
            match (ceval_func st cbody fuel') with
            | CFDiverges => CFDiverges
            | CFTerminates st'' => ceval_func st'' c fuel'
            end
          | false => CFTerminates st
          end
        end
      end
    end
  end.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".


(* Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 100). *)

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
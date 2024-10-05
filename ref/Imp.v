From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.

From AbsInt Require Import Maps.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp). 

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.

Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Definition empty_st := (_ !-> 0).

Definition state := total_map nat.
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Fixpoint aeval (st : state) (* <--- NEW *)
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (* <--- NEW *)
               (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.


Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').


  /To define the behavior of assert and assume, we need to add notation for an error, which indicates that an assertion has failed. We modify the ceval relation, therefore, so that it relates a start state to either an end state or to error. The result type indicates the end value of a program, either a state or an error:
Inductive result : Type :=
  | RNormal : state → result
  | RError : result.
Now we are ready to give you the ceval relation for the new language.
Inductive ceval : com → state → result → Prop :=
  (* Old rules, several modified *)
  | E_Skip : ∀ st,
      st =[ skip ]=> RNormal st
  | E_Asgn : ∀ st a1 n x,
      aeval st a1 = n →
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : ∀ c1 c2 st st' r,
      st =[ c1 ]=> RNormal st' →
      st' =[ c2 ]=> r →
      st =[ c1 ; c2 ]=> r
  | E_SeqError : ∀ c1 c2 st,
      st =[ c1 ]=> RError →
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : ∀ st r b c1 c2,
      beval st b = true →
      st =[ c1 ]=> r →
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : ∀ st r b c1 c2,
      beval st b = false →
      st =[ c2 ]=> r →
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : ∀ b st c,
      beval st b = false →
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : ∀ st st' r b c,
      beval st b = true →
      st =[ c ]=> RNormal st' →
      st' =[ while b do c end ]=> r →
      st =[ while b do c end ]=> r
  | E_WhileTrueError : ∀ st b c,
      beval st b = true →
      st =[ c ]=> RError →
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : ∀ st b,
      beval st b = true →
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : ∀ st b,
      beval st b = false →
      st =[ assert b ]=> RError
  | E_Assume : ∀ st b,
      beval st b = true →
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(* 
To define the behavior of assert and assume, we need to add notation for an error, which indicates that an assertion has failed. We modify the ceval relation, therefore, so that it relates a start state to either an end state or to error. The result type indicates the end value of a program, either a state or an error:

Inductive result : Type :=
  | RNormal : state → result
  | RError : result.


Now we are ready to give you the ceval relation for the new language.
Inductive ceval : com → state → result → Prop :=
  (* Old rules, several modified *)
  | E_Skip : ∀ st,
      st =[ skip ]=> RNormal st
  | E_Asgn : ∀ st a1 n x,
      aeval st a1 = n →
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : ∀ c1 c2 st st' r,
      st =[ c1 ]=> RNormal st' →
      st' =[ c2 ]=> r →
      st =[ c1 ; c2 ]=> r
  | E_SeqError : ∀ c1 c2 st,
      st =[ c1 ]=> RError →
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : ∀ st r b c1 c2,
      beval st b = true →
      st =[ c1 ]=> r →
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : ∀ st r b c1 c2,
      beval st b = false →
      st =[ c2 ]=> r →
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : ∀ b st c,
      beval st b = false →
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : ∀ st st' r b c,
      beval st b = true →
      st =[ c ]=> RNormal st' →
      st' =[ while b do c end ]=> r →
      st =[ while b do c end ]=> r
  | E_WhileTrueError : ∀ st b c,
      beval st b = true →
      st =[ c ]=> RError →
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : ∀ st b,
      beval st b = true →
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : ∀ st b,
      beval st b = false →
      st =[ assert b ]=> RError
  | E_Assume : ∀ st b,
      beval st b = true →
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

 *)
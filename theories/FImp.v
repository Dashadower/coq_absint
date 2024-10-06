From Coq Require Import Bool.Bool.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
(* Print LoadPath. *)
From AbsInt Require Import FMaps.
From AbsInt Require Import Number.
From Coq Require Import ZArith.
From Coq Require Import QArith.

Inductive aexp : Type :=
  | AInt (n : Z)
  | ARational (n : Q)
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
Coercion AInt : Z >-> aexp.
Coercion ARational : Q >-> aexp.

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

Print empty.

Definition empty_st := empty (A := Number).

Print empty_st.

Definition state := partial_map Number.
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Inductive Aresult : Type :=
  | RNormal : Number -> Aresult
  | RError : Aresult.

Compute 5.2.


Fixpoint aeval (st : state)
               (a : aexp) : Aresult :=
  match a with
  | AInt n => RNormal (IntVal n)
  | ARational f => RNormal (QVal f)
  | AId x => 
    match st x with
    | Some a => RNormal a
    | None => RError
    end
  | <{a1 + a2}> => 
    match (aeval st a1) with
    | RNormal v1 =>
      match (aeval st a2) with
      | RNormal v2 => RNormal (NAdd v1 v2)
      | RError => RError
      end
    | RError => RError
    end
  | <{a1 - a2}> => 
    match (aeval st a1) with
    | RNormal v1 =>
      match (aeval st a2) with
      | RNormal v2 => RNormal (NSub v1 v2)
      | RError => RError
      end
    | RError => RError
    end
  | <{a1 * a2}> => 
    match (aeval st a1) with
    | RNormal v1 =>
      match (aeval st a2) with
      | RNormal v2 => RNormal (NMult v1 v2)
      | RError => RError
      end
    | RError => RError
    end
  end.

Compute (aeval empty_st <{1 + 1}>).
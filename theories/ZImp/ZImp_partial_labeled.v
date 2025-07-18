From AbsInt.ZImp Require Import ZImp_partial.
From AbsInt Require Import Maps.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.

(* Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com). *)



Declare Custom Entry lcom.
Declare Scope lcom_scope.
Open Scope lcom_scope.

Inductive Labeledcom : Type :=
  | LCSkip (label : nat)
  | LCAsgn (x : string) (a : aexp) (label : nat)
  | LCSeq (c1 c2 : Labeledcom)
  | LCIf (b : bexp) (c1 c2 : Labeledcom) (label : nat)
  | LCWhile (b : bexp) (c : Labeledcom) (label : nat).

Notation "'skip' @ label"  :=
         (LCSkip label) (in custom lcom at level 0) : lcom_scope.
Notation "x := y @ label"  :=
         (LCAsgn x y label)
            (in custom lcom at level 0, x constr at level 0,
             y at level 85, no associativity) : lcom_scope.
Notation "x ; y" :=
         (LCSeq x y)
           (in custom lcom at level 90, right associativity) : lcom_scope.
Notation "'if' x 'then' y 'else' z 'end' @ label" :=
         (LCIf x y z label)
           (in custom lcom at level 89, x at level 99,
            y at level 99, z at level 99) : lcom_scope.
Notation "'while' x 'do' y 'end' @ label" :=
         (LCWhile x y label)
            (in custom lcom at level 89, x at level 99, y at level 99) : lcom_scope.

Notation "<{{ e }}>" := e (at level 0, e custom lcom at level 99) : lcom_scope.

Fixpoint LabelProgram (c : com) (n : nat) : Labeledcom * nat :=
  match c with
  | CSkip => (LCSkip n, S n)
  | CAsgn x a => (LCAsgn x a n, S n)
  | CSeq c1 c2 => 
    match (LabelProgram c1 n) with
    | (lp1, next_label1) => 
      match (LabelProgram c2 next_label1) with
      | (lp2, next_label2) => (LCSeq lp1 lp2, next_label2)
      end
    end
  | CIf b tc fc => 
    match LabelProgram tc (S n) with
    | (ltc, nl1) =>
      match LabelProgram fc nl1 with
      | (lfc, nl2) => (LCIf b ltc lfc n, nl2)
      end
    end
  | CWhile b c => 
    match LabelProgram c (S n) with
    | (lc, nl) => (LCWhile b lc n, nl)
    end
  end.

Definition test_prog : com := <{
  X := 1 ;
  Y := 2 ;
  while Y > X do
  X := X + 0
  end
  }>.

Locate "skip".
Print Custom Grammar lcom.
Print Scopes.

Definition LabelProgram' (c : com) : Labeledcom :=
  fst (LabelProgram c 1).
Set Printing Notations.
Compute LabelProgram' test_prog.
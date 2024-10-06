From Coq Require Import ZArith.
From Coq Require Import QArith.

Inductive Number : Type :=
  | IntVal (v : Z)
  | QVal (v : Q).

Definition ZtoQ (z : Z) : Q := z # xH.

Definition NAdd (left right : Number) : Number :=
  match left with
  | IntVal l =>
    match right with
    | IntVal r => IntVal (l + r)
    | QVal r => QVal ((ZtoQ l) + r)
    end
  | QVal l => 
    match right with
    | IntVal r => QVal (l + (ZtoQ r))
    | QVal r => QVal (l + r)
    end
  end.

Example Nadd_1 : NAdd (IntVal 1) (QVal 3.5) = (QVal 4.5).
Proof. reflexivity. Qed.

Definition NSub (left right : Number) : Number :=
  match left with
  | IntVal l =>
      match right with
      | IntVal r => IntVal (l - r)
      | QVal r => QVal ((ZtoQ l) - r)
      end
  | QVal l => 
      match right with
      | IntVal r => QVal (l - (ZtoQ r))
      | QVal r => QVal (l - r)
      end
  end.

Definition NMult (left right : Number) : Number :=
  match left with
  | IntVal l =>
      match right with
      | IntVal r => IntVal (l * r)
      | QVal r => QVal ((ZtoQ l) * r)
      end
  | QVal l => 
      match right with
      | IntVal r => QVal (l * (ZtoQ r))
      | QVal r => QVal (l * r)
      end
  end.
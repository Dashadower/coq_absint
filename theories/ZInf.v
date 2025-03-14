From Coq Require Import ZArith.

Inductive ZInf :=
  | Znum (num : Z) : ZInf
  | Zposinf : ZInf
  | Zneginf : ZInf.

Open Scope Z_scope.

Definition ZInfAdd (left right : ZInf) : ZInf :=
  match left with
  | Znum l =>
    match right with
    | Znum r => Znum (l + r)
    | Zposinf => Zposinf
    | Zneginf => Zneginf
    end
  | Zposinf => Zposinf
  | Zneginf => Zneginf
  end.

Definition ZInfSub (left right : ZInf) : ZInf :=
  match left with
  | Znum l =>
    match right with
    | Znum r => Znum (l - r)
    | Zposinf => Zposinf
    | Zneginf => Zneginf
    end
  | Zposinf => Zposinf
  | Zneginf => Zneginf
  end.

Definition ZInfMult (left right : ZInf) : ZInf :=
  match left with
  | Znum l =>
    match right with
    | Znum r => Znum (l * r)
    | Zposinf => Zposinf
    | Zneginf => Zneginf
    end
  | Zposinf => Zposinf
  | Zneginf => Zneginf
  end.


Definition ZInfLeb (left right : ZInf) : bool :=
  match left with
  | Znum l =>
    match right with
    | Znum r => l <=? r
    | Zposinf => true
    | Zneginf => false
    end
  | Zposinf => 
    match right with
    | Znum r => false
    | Zposinf => true
    | Zneginf => false
    end
  | Zneginf => true
  end.

Inductive ZInfLe : ZInf -> ZInf -> Prop :=
  | ZILe_refl : forall Z, ZInfLe Z Z
  | ZILe_lhs_ninf : forall ZI, ZInfLe Zneginf ZI
  | ZILe_rhs_inf : forall lh, ZInfLe lh Zposinf
  | ZILe_vv : forall (lh rh : Z), Z.le lh rh -> ZInfLe (Znum lh) (Znum rh).

Lemma ZInfLe_leb : forall x y,
  ZInfLe x y <-> ZInfLeb x y = true.
Proof.
  split.
  {
    induction x; intros.
    - inversion H; subst.
      + simpl. rewrite Z.leb_refl. reflexivity.
      + simpl. reflexivity.
      + simpl. rewrite <- Zle_is_le_bool. assumption.
    - inversion H; subst. reflexivity. simpl. reflexivity.
    - simpl. reflexivity.
  }
  generalize dependent x.
  induction x.
  - intros. destruct y.
    + inversion H. rewrite <- Zle_is_le_bool in H1. apply ZILe_vv. assumption.
    + apply ZILe_rhs_inf.
    + simpl in H. discriminate H.
  - intros. destruct y.
    + simpl in H. discriminate H.
    + apply ZILe_refl.
    + simpl in H. discriminate H.
  - intros. destruct y.
    + apply ZILe_lhs_ninf.
    + apply ZILe_rhs_inf.
    + apply ZILe_lhs_ninf.
Qed.

Lemma ZInfLe_trans : forall x y z,
  ZInfLe x y -> ZInfLe y z -> ZInfLe x z.
Proof.
  intros x.
  induction x.
  - intros. inversion H; subst.
    + assumption.
    + inversion H0; apply ZILe_rhs_inf.
    + inversion H; subst.
      * assumption.
      * inversion H0; subst; try assumption.
        ** apply ZILe_rhs_inf.
        ** apply (Z.le_trans num rh rh0) in H2.
           *** apply ZILe_vv. assumption.
           *** assumption.
  - intros. inversion H; subst; assumption.
  - intros. apply ZILe_lhs_ninf.
Qed.

Lemma ZInfLe_antisymm : forall x y,
  ZInfLe x y -> ZInfLe y x -> x = y.
Proof.
  intros x.
  induction x; intros.
  - inversion H; subst.
    + reflexivity.
    + inversion H0.
    + inversion H0; subst.
      * reflexivity.
      * apply Z.le_antisymm in H2.
        ** subst. reflexivity.
        ** assumption.
  - inversion H; reflexivity.
  - inversion H0; reflexivity.
Qed.


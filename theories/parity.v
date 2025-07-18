From Coq Require Import Arith.Arith.

Inductive parity :=
  | Even
  | Odd.

Definition flip (p : parity) : parity :=
  match p with
  | Even => Odd
  | Odd => Even
  end.

Fixpoint iseven (n : nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') => iseven n'
  end.

Definition abstract (n : nat) : parity :=
  match (iseven n) with
  | true => Even
  | false => Odd
  end.

Inductive concretize : nat -> parity -> Prop :=
  | CZero : concretize 0 Even
  | CFlip (n : nat) (p : parity) : concretize n p -> concretize (S n) (flip p).

Lemma flip_twice_symm : forall p,
  flip (flip p) = p.
  intros.
  destruct p; reflexivity.
Qed.

Lemma calc_parity_succ : forall n ,
  abstract (S n) = flip (abstract n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - unfold abstract in *. simpl in *. rewrite IHn. rewrite flip_twice_symm.
    reflexivity.
Qed.

Lemma DA_Corr : forall n p,
    concretize n p <-> abstract(n) = p.
Proof.
    split.
    - generalize dependent p.
      induction n; intros.
      + inversion H. reflexivity.
      + inversion H; subst. apply IHn in H1.
        rewrite calc_parity_succ. rewrite H1. reflexivity.
    - generalize dependent p.
      induction n.
      + intros. rewrite <- H. apply CZero.
      + intros.
        destruct (abstract n) eqn:Eqc.
        * assert (H1: abstract (S n) = Odd). {
            rewrite calc_parity_succ. rewrite Eqc. reflexivity.
          }
          rewrite <- H.
          rewrite calc_parity_succ in H1. rewrite Eqc in H1.
          rewrite calc_parity_succ. apply CFlip. rewrite Eqc.
          specialize (IHn Even). apply IHn. reflexivity.
        * rewrite <- H. rewrite calc_parity_succ.
          apply CFlip. specialize (IHn Odd). rewrite Eqc.
          apply IHn. reflexivity.
Qed.

    
    
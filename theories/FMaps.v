From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Floats.
(* Open Scope float_scope. *)

Inductive FMap_Value : Type :=
    | NatVal (v : nat)
    | FloatVal (v : float).

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "nat" !-> NatVal 1;
    "float" !-> FloatVal 1.5;
    _ !-> NatVal 0
  ).

(* **************************** *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  intros A x v.
  unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold t_update.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v.
  intros H.
  unfold t_update.
  apply String.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  unfold t_update.
  apply functional_extensionality.
  intros x0.
  destruct (x =? x0)%string eqn:Eqe.
    - reflexivity.
    - reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros A m x.
  unfold t_update.
  apply functional_extensionality.
  intros x0.
  destruct (String.eqb_spec x x0).
    - rewrite e. reflexivity.
    - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2.
  intros H.
  unfold t_update.
  apply functional_extensionality.
  intros x.
  apply String.eqb_neq in H.
  destruct (String.eqb_spec x x1).
    - rewrite <- e in H. apply String.eqb_eq in e.
      rewrite String.eqb_sym in e. rewrite e. rewrite H. reflexivity.
    - apply String.eqb_neq in n. rewrite String.eqb_sym in n. rewrite n.
      reflexivity.
Qed.
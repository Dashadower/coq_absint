From Coq Require Import Relations.
(* From Coq.Relations Require Import Relation_Definitions. *)
(* From Coq.Classes Require Import RelationClasses. *)

Print antisymmetric.

Print relation.
(* 
relation = fun A : Type => A -> A -> Prop
     : Type -> Type

Arguments relation A%type_scope
*)

Class OrderRelation (E : Type) (R : relation E) := {
  OR_reflexive : forall x, R x x;
  OR_transitive : forall x y z, R x y -> R y z -> R x z;
  OR_antisymmetric : forall x y, R x y -> R y x -> x = y
}.

Class TotalOrder (E : Type) (R : relation E) `{OrderRelation E R} := {
  total : forall x y : E, R x y \/ R y x
}.

Definition SubsetProp (E : Type) : Type := E -> Prop.
Definition Subset (E : Type) (P : SubsetProp E) := {e : E | P e}.

From Coq Require Import Arith.
From Coq Require Import Lia.
Instance nat_le_is_ordered : OrderRelation nat le.
Proof.
  constructor.
  - apply Nat.le_refl.
  - apply Nat.le_trans.
  - intros x y H. destruct H; auto.
    intros H1. apply Nat.le_trans with (n := S m) in H.
    + apply Nat.nle_succ_diag_l in H. destruct H.
    + assumption.
Qed.

Print nat_le_is_ordered.

Instance nat_le_is_total : TotalOrder nat le.
Proof.
  constructor.
  intros x y.
  destruct (x <=? y) eqn:Exy.
  - apply Nat.leb_le in Exy. left. assumption.
  - right. apply Nat.leb_gt in Exy. unfold lt in Exy. apply le_S in Exy.
    lia.
Qed.
    

Definition Chain (E : Type) (P : SubsetProp E) (R : relation (Subset E P)) `{TotalOrder (Subset E P) R} : Prop := 
  True.

Definition GreatestElement (E : Type) (R : relation E) (x : E) :=
  forall y, R x y.

Definition LeastElement (E : Type) (R : relation E) (x : E) :=
  forall y, R y x.

Definition LeastUpperBound (E : Type) (R : relation E) (OR : OrderRelation E R) (x y lub : E) : Prop := 
  R x lub /\ R y lub /\ forall ub, R x ub -> R y ub -> R lub ub.

Definition GreatestUpperBound (E : Type) (R : relation E) (OR : OrderRelation E R) (x y glb : E) : Prop :=
  R glb x /\ R glb y /\ forall lb, R lb x -> R lb y -> R lb glb.


Theorem LeastUpperBound_unique : forall (E : Type) (R : relation E) (OR : OrderRelation E R) (x y lub lub' : E),
  LeastUpperBound E R OR x y lub -> LeastUpperBound E R OR x y lub' -> lub = lub'.
Proof.
  intros. unfold LeastUpperBound in H. destruct H as [xlub  [ylub  ulub]].
  unfold LeastUpperBound in H0. destruct H0 as [xlub' [ylub' ulub']].
  apply ulub in xlub'. apply ulub' in xlub.
  apply OR_antisymmetric in xlub. all: assumption.
Qed.

Theorem GreatestUpperBound_unique : forall (E : Type) (R : relation E) (OR : OrderRelation E R) (x y glb glb' : E),
  GreatestUpperBound E R OR x y glb -> GreatestUpperBound E R OR x y glb' -> glb = glb'.
Proof.
  intros. unfold GreatestUpperBound in *. destruct H as [xglb [yglb lglb]].
  destruct H0 as [xglb' [yglb' lglb']].
  apply lglb' in xglb. apply lglb in xglb'.
  apply OR_antisymmetric in xglb.
  symmetry. all: assumption.
Qed.


Class Lattice (E : Type) (R : relation E) `{OR : OrderRelation E R} := {
  greatest_exists : exists inf, GreatestElement E R inf;
  least_exists : exists sup, LeastElement E R sup;
  lub_exists : forall x y, exists lub, LeastUpperBound E R OR x y lub;
  glb_exists : forall x y, exists glb, GreatestUpperBound E R OR x y glb;
}.

Check Subset nat (fun x: nat => x <= 3).
Check Subset.

Class CompleteLattice (E : Type) (R : relation E) `{Lattice E R} := {
  subset_lub_exists : forall (P : SubsetProp E) (R' : relation (Subset E P)) (x y : Subset E P)
                             (OR' : OrderRelation (Subset E P) R'),
                      exists lub, LeastUpperBound (Subset E P) R' OR' x y lub;
  subset_glb_exists : forall (P : SubsetProp E) (R' : relation (Subset E P)) (x y : Subset E P)
                             (OR' : OrderRelation (Subset E P) R'),
                      exists glb, GreatestUpperBound (Subset E P) R' OR' x y glb;
}.

From Coq Require Import Relations.
From Coq Require Import Specif.
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
  TOtotal : forall x y : E, R x y \/ R y x
}.

Definition SubsetProp (E : Type) : Type := E -> Prop.
Definition Subset (E : Type) (P : SubsetProp E) := {e : E | P e}.
(* 
A subset Subset E P represent the elements e of E that satisfies
P e
*)

(* Given a relation defined on E, return the same relation that is defined on Subset E P *)
Definition SubsetRelation {E : Type} (P : SubsetProp E) (R : relation E) : relation (Subset E P) :=
  fun (x y : Subset E P) => R (proj1_sig x) (proj1_sig y).

From Coq Require Import ProofIrrelevance.

(* An ordered relation defined on E is also ordered on subsets of E *)
Lemma relation_is_ordered_in_subset : forall (E : Type) (R : relation E) (P : SubsetProp E),
  OrderRelation E R -> OrderRelation (Subset E P) (SubsetRelation P R).
Proof.
  intros.
  constructor; inversion H.
  - intros. inversion x. unfold SubsetRelation. apply OR_reflexive0.
  - intros. unfold SubsetRelation in *. apply (OR_transitive0 (proj1_sig x) _ (proj1_sig z)) in H0; assumption.
  - intros. unfold SubsetRelation in *. apply OR_antisymmetric0 in H0.
    + destruct x. destruct y. simpl in H0. subst. f_equal. apply proof_irrelevance.
    + assumption.
Qed.


(* Given a function f : E -> F, return the same function but the domain set as Subset E P  *)
Definition SubsetFunc {E F : Type} (P : SubsetProp E) (f : E -> F) : (Subset E P) -> F :=
  fun (x : Subset E P) => f (proj1_sig x).

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

Definition GreatestElement {E : Type} (R : relation E) (x : E) :=
  forall y, R y x.

Definition LeastElement {E : Type} (R : relation E) (x : E) :=
  forall y, R x y.

Definition LeastUpperBound {E : Type} {R : relation E} (OR : OrderRelation E R) (lub : E) : Prop := 
  forall x y, R x lub /\ R y lub /\ forall ub, R x ub -> R y ub -> R lub ub.

Definition GreatestUpperBound {E : Type} {R : relation E} (OR : OrderRelation E R) (glb : E) : Prop :=
  forall x y, R glb x /\ R glb y /\ forall lb, R lb x -> R lb y -> R lb glb.


Theorem LeastUpperBound_unique : forall {E : Type} {R : relation E} (OR : OrderRelation E R) (lub lub' : E),
  LeastUpperBound OR lub -> LeastUpperBound OR lub' -> lub = lub'.
Proof.
  intros. unfold LeastUpperBound in *. destruct (H lub lub') as [H1 [H2 H3]].
  destruct (H0 lub lub') as [H4 [H5 H6]]. inversion OR. apply OR_antisymmetric in H4.
  - symmetry. assumption.
  - assumption.
Qed.

Theorem GreatestUpperBound_unique : forall {E : Type} {R : relation E} (OR : OrderRelation E R) (glb glb' : E),
  GreatestUpperBound OR glb -> GreatestUpperBound OR glb' -> glb = glb'.
Proof.
  intros. unfold GreatestUpperBound in *. destruct (H glb glb') as [H1 [H2 H3]].
  destruct (H0 glb glb') as [H4 [H5 H6]]. apply OR_antisymmetric in H4.
  - assumption.
  - assumption.
Qed.


Class Lattice {E : Type} (R : relation E) `{OR : OrderRelation E R} := {
  Lattice_top : E;
  Lattice_bottom : E;
  Lgreatest_exists : GreatestElement R Lattice_top;
  Lleast_exists : LeastElement R Lattice_bottom;
  Llub_exists : exists lub, LeastUpperBound OR lub;
  Lglb_exists : exists glb, GreatestUpperBound OR glb;
}.


Class CompleteLattice (E : Type) (R : relation E) `{Lattice E R} := {
  CLsubset_lub_exists : forall (P : SubsetProp E) (x y : Subset E P)
                             (OR' : OrderRelation (Subset E P) (SubsetRelation P R)),
                      exists lub, LeastUpperBound OR' lub;
  CLsubset_glb_exists : forall (P : SubsetProp E) (x y : Subset E P)
                             (OR' : OrderRelation (Subset E P) (SubsetRelation P R)),
                      exists glb, GreatestUpperBound OR' glb;
}.

(* 
E is a complete partial order (for short, CPO) 
if it has an infimum and is such that any chain of elements of E has a least upper bound in E
*)  
Class CompletePartialOrder {E : Type} {R : relation E} (OR: OrderRelation E R) := {
  CPO_bottom : E;
  CPOleast_exists : LeastElement R CPO_bottom;
  CPOsubset_lub_exists : forall (P : SubsetProp E) (x y : Subset E P)
                             (OR' : OrderRelation (Subset E P) (SubsetRelation P R)),
                      exists lub, LeastUpperBound OR' lub;
 }.

 Definition Monotonic {E : Type} {F : Type} {RE : relation E} {RF : relation F}
                     (ORE : OrderRelation E RE) (ORF : OrderRelation F RF) (f : E -> F) : Prop :=
  forall (x y : E), RE x y -> RF (f x) (f y).

Definition Image (A : Type) (R : relation A) (image : A) : Prop := exists a, R a image.


(* 
Scott Continuity
f : E -> F
assuming that E and F are CPOs, we say that f is continuous 
if and only if the image of any chain G of E by f has a least upper bound, 
that is, such that ⊔{f(x) | x ∈ G} = f(⊔G).
*)
Definition LeastUpperBound_proj_f {E F : Type} {R : relation F} (OR : OrderRelation F R) (f : E -> F) (lub : E) : Prop := 
  forall x y, R (f x) (f lub) /\ R (f y) (f lub) /\ forall ub, R (f x) (f ub) -> R (f y) (f ub) -> R (f lub) (f ub).

Definition Continuous {E F: Type} {RE : relation E} {RF : relation F} {ORE : OrderRelation E RE}
                     {ORF : OrderRelation F RF} (CPOE : CompletePartialOrder ORE) (CPOF : CompletePartialOrder ORF)
                     (f : E -> F) : Prop :=
  forall (P : SubsetProp E) (G : (OrderRelation (Subset E P) (SubsetRelation P RE))), 
  exists (lub lub' : Subset E P), LeastUpperBound_proj_f ORF (SubsetFunc P f) lub ->
                             LeastUpperBound G lub' ->
                             f (proj1_sig lub) = f (proj1_sig lub').


(* A continuous function is also monotone *)
Lemma continuous_impl_monotone : forall (E F: Type) (RE : relation E) (RF : relation F) (ORE : OrderRelation E RE) (P : SubsetProp E)
                                        (ORF : OrderRelation F RF) (CPOE : CompletePartialOrder ORE) (CPOF : CompletePartialOrder ORF)
                                        (f : E -> F),
  Continuous CPOE CPOF f -> Monotonic ORE ORF f.
Proof.
  intros. unfold Continuous in H. 
  unfold Monotonic.
  pose proof (relation_is_ordered_in_subset E RE P). apply H0 in ORE as ORSE.
  destruct (H P ORSE) as[lub [lub' H1]]. clear H H0.
  intros.
Abort.


Definition LFP {E : Type} {R : relation E} (OR : OrderRelation E R) (f : E -> E) (lfp : E) :=
  forall fp, fp = f fp -> R fp lfp.

Fixpoint fix_f {E : Type} {R : relation E} {OR : OrderRelation E R} (CPO : CompletePartialOrder OR) (f : E -> E) (fuel : nat) : E :=
  match fuel with
  | 0 => CPO_bottom
  | S n' => f (fix_f CPO f n')
  end.

Lemma CPO_bottom_lessthan_f_bottom : forall {E : Type} {R : relation E} {OR : OrderRelation E R} (CPO : CompletePartialOrder OR) (f : E -> E),
  R CPO_bottom (f CPO_bottom).
Proof.
  intros.
  pose proof CPOleast_exists. unfold LeastElement in H.
  apply H.
Qed.

Theorem Kleene_fp : forall (E : Type) (R : relation E) (OR : OrderRelation E R) (CPO : CompletePartialOrder OR) (f : E -> E),
  Continuous CPO CPO f -> exists n fp, fp = fix_f CPO f n /\ Fixpoint_f f fp.
Proof.
  intros.
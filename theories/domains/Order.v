From Stdlib Require Import Relations.
From Stdlib Require Import Specif.
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

Definition SubsetRelation {E : Type} (P : SubsetProp E) (R : relation E) : relation (Subset E P) :=
  (* Given a relation defined on E, return the same relation that is defined on Subset E P *)
  fun (x y : Subset E P) => R (proj1_sig x) (proj1_sig y).

Require Import ProofIrrelevance.

Lemma relation_is_ordered_in_subset : forall (E : Type) (R : relation E) (P : SubsetProp E),
  (* An ordered relation defined on E is also ordered on subsets of E *)
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


Definition SubsetFunc {E F : Type} (P : SubsetProp E) (f : E -> F) : (Subset E P) -> F :=
  (* Given a function f : E -> F, return the same function 
     but the domain set as Subset E P  *)
  fun (x : Subset E P) => f (proj1_sig x).

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
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
  Lgreatest_exists : exists inf, GreatestElement E R inf;
  Lleast_exists : exists sup, LeastElement E R sup;
  Llub_exists : forall x y, exists lub, LeastUpperBound E R OR x y lub;
  Lglb_exists : forall x y, exists glb, GreatestUpperBound E R OR x y glb;
}.


Class CompleteLattice (E : Type) (R : relation E) `{Lattice E R} := {
  CLsubset_lub_exists : forall (P : SubsetProp E) (x y : Subset E P)
                             (OR' : OrderRelation (Subset E P) (SubsetRelation P R)),
                      exists lub, LeastUpperBound (Subset E P) (SubsetRelation P R) OR' x y lub;
  CLsubset_glb_exists : forall (P : SubsetProp E) (x y : Subset E P)
                             (OR' : OrderRelation (Subset E P) (SubsetRelation P R)),
                      exists glb, GreatestUpperBound (Subset E P) (SubsetRelation P R) OR' x y glb;
}.

(* 
E is a complete partial order (for short, CPO) 
if it has an infimum and is such that any chain of elements of E has a least upper bound in E
*)  
Class CompletePartialOrder (E : Type) (R : relation E) (OR: OrderRelation E R) := {
  CPOgreatest_exists : exists inf, GreatestElement E R inf;
  CPOsubset_lub_exists : forall (P : SubsetProp E) (x y : Subset E P)
                             (OR' : OrderRelation (Subset E P) (SubsetRelation P R)),
                      exists lub, LeastUpperBound (Subset E P) (SubsetRelation P R) OR' x y lub;
 }.

 Definition Monotonic (A : Type) (B : Type) (f : A -> B) (R_a : relation A) (R_b : relation B)
                     (OR_a : OrderRelation A R_a) (OR_b : OrderRelation B R_b) : Prop :=
  forall (x y : A), R_a x y -> R_b (f x) (f y).

Definition Image (A : Type) (R : relation A) (image : A) : Prop := exists a, R a image.


(* 
f : E -> F
assuming that E and F are CPOs, we say that f is continuous 
if and only if the image of any chain G of E by f has a least upper bound, 
that is, such that ⊔{f(x) | x ∈ G} = f(⊔G).

For all subset proposition P on E, if lub is a least upper bound for f()
*)
Definition Continuous (E F: Type) (RE : relation E) (RF : relation F) (ORE : OrderRelation E RE) (P : SubsetProp E)
                     (ORF : OrderRelation F RF) (CPOE : CompletePartialOrder E RE ORE) (CPOF : CompletePartialOrder F RF ORF)
                     (f : E -> F) : Prop :=
  forall (x y : Subset E P) (OSRE : (OrderRelation (Subset E P) (SubsetRelation P RE))), 
  exists (lub lub' : Subset E P), LeastUpperBound F RF ORF ((SubsetFunc P f) x) ((SubsetFunc P f) y) ((SubsetFunc P f) lub) ->
                             LeastUpperBound (Subset E P) (SubsetRelation P RE) OSRE x y lub' ->
                             (SubsetFunc P f) lub = (SubsetFunc P f) lub'.

Lemma monotone_impl_continuous : forall (A B: Type) (RA : relation A) (RB : relation B) (ORA : OrderRelation A RA) (P : SubsetProp A)
                                        (ORB : OrderRelation B RB) (E : CompletePartialOrder A RA ORA) (F : CompletePartialOrder B RB ORB)
                                        (f : A -> B),
  Continuous A B RA RB ORA P ORB E F f -> Monotonic A B f RA RB ORA ORB.
Proof.
  intros. unfold Continuous in H. unfold Monotonic. intros.
  pose proof (relation_is_ordered_in_subset A RA P). apply H1 in ORA as ORSA.
  destruct (H x y ORSA).
  unfold Continuous. intros.
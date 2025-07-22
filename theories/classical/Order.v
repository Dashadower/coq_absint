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
Definition Subset {E : Type} (P : SubsetProp E) := {e : E | P e}.
(* 
A subset Subset E P represent the elements e of E that satisfies
P e
*)

(* Given a relation defined on E, return the same relation that is defined on Subset E P *)
Definition SubsetRelation {E : Type} (P : SubsetProp E) (R : relation E) : relation (Subset P) :=
  fun (x y : Subset P) => R (proj1_sig x) (proj1_sig y).

From Coq Require Import ProofIrrelevance.

(* An ordered relation defined on E is also ordered on subsets of E *)
Lemma relation_is_ordered_in_subset : forall (E : Type) (R : relation E) (P : SubsetProp E),
  OrderRelation E R -> OrderRelation (Subset P) (SubsetRelation P R).
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
Definition SubsetFunc {E F : Type} (P : SubsetProp E) (f : E -> F) : (Subset P) -> F :=
  fun (x : Subset P) => f (proj1_sig x).

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
    

(* Definition Chain {E : Type} (P : SubsetProp E) (R : relation E) (OR : OrderRelation E R) : Prop := 
  forall (x y : Subset P), (SubsetRelation P R) x y \/ (SubsetRelation P R) y x.

Print Chain. *)

Class Chain {E : Type} {R : relation E} (P : SubsetProp E) `{OrderRelation E R} : Type := {
  Chaintotal : forall (x y : Subset P), R (proj1_sig x) (proj1_sig y) \/ R (proj1_sig y) (proj1_sig x)
}.

(* Definition is_chain {E : Type} (P : SubsetProp E) (R : relation E) (OR : OrderRelation E R) : Prop :=
  TotalOrder (Subset P) (SubsetRelation P R). *)

Definition GreatestElement {E : Type} {R : relation E} (OR : OrderRelation E R) (x : E) :=
  forall y, R y x.

Definition LeastElement {E : Type} {R : relation E} (OR : OrderRelation E R) (x : E) :=
  forall y, R x y.

Definition LeastUpperBound {E : Type} {R : relation E} (OR : OrderRelation E R) (x y lub : E) : Prop := 
  R x lub /\ R y lub /\ forall ub, R x ub -> R y ub -> R lub ub.

Definition GreatestLowerBound {E : Type} {R : relation E} (OR : OrderRelation E R) (x y glb : E) : Prop :=
  R glb x /\ R glb y /\ forall lb, R lb x -> R lb y -> R lb glb.

Definition LeastUpperBound_Subset {E : Type} {R : relation E} (P : SubsetProp E) (OR : OrderRelation E R) (lub : E) :=
  forall (x : Subset P), (R (proj1_sig x) lub /\ forall ub, R (proj1_sig x) ub -> R lub ub).

Definition GreatestLowerBound_Subset {E : Type} {R : relation E} (P : SubsetProp E) (OR : OrderRelation E R) (glb : E) :=
  forall (x : Subset P), (R glb (proj1_sig x) /\ forall lb, R lb (proj1_sig x) -> R lb glb).

Theorem LeastUpperBound_unique : forall {E : Type} {R : relation E} (OR : OrderRelation E R) (x y lub lub' : E),
  LeastUpperBound OR x y lub -> LeastUpperBound OR x y lub' -> lub = lub'.
Proof.
  intros. unfold LeastUpperBound in *. destruct H as [H1 [H2 H3]].
  destruct H0 as [H4 [H5 H6]]. inversion OR.
  apply H3 in H4.
  - apply H6 in H1.
    + apply OR_antisymmetric in H4.
      * symmetry. assumption.
      * assumption.
    + assumption.
  - assumption.
Qed.

Theorem GreatestLowerBound_unique : forall {E : Type} {R : relation E} (OR : OrderRelation E R) (x y glb glb' : E),
  GreatestLowerBound OR x y glb -> GreatestLowerBound OR x y glb' -> glb = glb'.
Proof.
  intros. unfold GreatestLowerBound in *. destruct H as [H1 [H2 H3]].
  destruct H0 as [H4 [H5 H6]].
  apply H3 in H4.
  - apply H6 in H1.
    + apply OR_antisymmetric in H1.
      * symmetry. assumption.
      * assumption.
    + assumption.
  - assumption.
Qed.


Class Lattice {E : Type} (R : relation E) `{OR : OrderRelation E R} := {
  Lattice_top : E;
  Lattice_bottom : E;
  Lgreatest_exists : GreatestElement OR Lattice_top;
  Lleast_exists : LeastElement OR Lattice_bottom;
  Llub_exists : forall x y, exists lub, LeastUpperBound OR x y lub;
  Lglb_exists : forall x y, exists glb, GreatestLowerBound OR x y glb;
}.

Print Lattice.

(* Class CompleteLattice (E : Type) (R : relation E) `{L : Lattice (relation E)} := {
  CL : E
}.

Print CompleteLattice. *)

Class CompleteLattice {E : Type} (R : relation E) `{L : Lattice E} := {
  CLsubset_lub_exists : forall (P : SubsetProp E),
                      exists lub : E, LeastUpperBound_Subset P OR lub;
  CLsubset_glb_exists : forall (P : SubsetProp E),
                      exists glb : E, GreatestLowerBound_Subset P OR glb;
}.

(* 
E is a complete partial order (for short, CPO) 
if it has an infimum(bottom) and is such that any chain of elements of E has a least upper bound in E
*)  
Class CompletePartialOrder {E : Type} {R : relation E} (OR: OrderRelation E R) := {
  CPO_bottom : E;
  CPOleast_exists : LeastElement OR CPO_bottom;
  CPOsubset_lub_exists : forall (P : SubsetProp E) (G : Chain P),
                      exists lub, LeastUpperBound_Subset P OR lub;
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

(* 
f : E -> E
R : relation E (E -> E -> Prop)
R_f : R (f x) (f x)
*)

Definition LeastUpperBound_Subset_lift_f {E F : Type} {R : relation F} (P : SubsetProp E) (ORF : OrderRelation F R) (f: E -> F) (lub : F) :=
  forall (x : Subset P), (R (f (proj1_sig x)) lub /\ forall ub, R (f(proj1_sig x)) ub -> R lub ub).

Definition Continuous {E F: Type} {RE : relation E} {RF : relation F} {ORE : OrderRelation E RE}
                     {ORF : OrderRelation F RF} (CPOE : CompletePartialOrder ORE) (CPOF : CompletePartialOrder ORF)
                     (f : E -> F) : Prop :=
  forall (P : SubsetProp E) (G : Chain P),
  exists (lub : F) (lub' : E), LeastUpperBound_Subset_lift_f P ORF f lub /\
                            LeastUpperBound_Subset P ORE lub' ->
                            lub = f lub'.


(* A continuous function is also monotone *)
Lemma continuous_impl_monotone : forall (E F: Type) (RE : relation E) (RF : relation F) (ORE : OrderRelation E RE) (P : SubsetProp E)
                                        (G : Chain P)
                                        (ORF : OrderRelation F RF) (CPOE : CompletePartialOrder ORE) (CPOF : CompletePartialOrder ORF)
                                        (f : E -> F),
  Continuous CPOE CPOF f -> Monotonic ORE ORF f.
Proof.
  intros. 
  pose proof Chaintotal.
  unfold Monotonic. intros.
  pose proof (CPOsubset_lub_exists P G) as lub_e. destruct lub_e as [lub_e Hlub]. unfold LeastUpperBound_Subset in Hlub.
  
  unfold Continuous in H. 
  unfold Monotonic. intros.
  destruct (H P) as [lub_fe [lub_e' [H1 [H2 H3]]]];[assumption|].
  clear H. unfold LeastUpperBound_Subset_lift_f in H1.
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
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
    

Definition Chain {E : Type} (P : SubsetProp E) {R : relation E} (OR : OrderRelation E R) : Prop := 
  forall (x y : Subset P), (SubsetRelation P R) x y \/ (SubsetRelation P R) y x.

Print Chain.

(* Class Chain {E : Type} {R : relation E} (P : SubsetProp E) `{OR : OrderRelation E R} : Type := {
  Chain_OR : OrderRelation (Subset P) (SubsetRelation P R);
  Chain_R : relation (Subset P);
  Chaintotal : forall (x y : Subset P), R (proj1_sig x) (proj1_sig y) \/ R (proj1_sig y) (proj1_sig x)
}. *)


Definition GreatestElement {E : Type} {R : relation E} (OR : OrderRelation E R) (x : E) :=
  forall y, R y x.

Definition LeastElement {E : Type} {R : relation E} (OR : OrderRelation E R) (x : E) :=
  forall y, R x y.

Definition LeastUpperBound {E : Type} {R : relation E} (OR : OrderRelation E R) (x y lub : E) : Prop := 
  R x lub /\ R y lub /\ forall ub, R x ub -> R y ub -> R lub ub.

Definition GreatestLowerBound {E : Type} {R : relation E} (OR : OrderRelation E R) (x y glb : E) : Prop :=
  R glb x /\ R glb y /\ forall lb, R lb x -> R lb y -> R lb glb.

Definition LeastUpperBound_set {E : Type} {R : relation E} (OR : OrderRelation E R) (lub : E) :=
  forall (x : E), R x lub /\ forall ub, R x ub -> R lub ub.

Definition LeastUpperBound_Subset {E : Type} {R : relation E} (P : SubsetProp E) (OR : OrderRelation E R) (lub : E) :=
  forall (x : Subset P), R (proj1_sig x) lub /\ (forall ub : E, (forall x : Subset P, R (proj1_sig x) ub) -> R lub ub).

Definition GreatestLowerBound_Subset {E : Type} {R : relation E} (P : SubsetProp E) (OR : OrderRelation E R) (glb : E) :=
  forall (x : Subset P), R glb (proj1_sig x) /\ (forall lb : E, (forall x : Subset P, R lb (proj1_sig x)) -> R lb glb).

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
  CPO_lub_exists : exists lub, LeastUpperBound_set OR lub;
  CPOsubset_lub_exists : forall (P : SubsetProp E) (G : Chain P OR),
                      exists lub, LeastUpperBound_Subset P OR lub;
 }.

 Definition Monotonic {E : Type} {F : Type} {RE : relation E} {RF : relation F}
                      (ORE : OrderRelation E RE) (ORF : OrderRelation F RF) (f : E -> F) : Prop :=
  forall (x y : E), RE x y -> RF (f x) (f y).


(* 
Scott Continuity
f : E -> F
assuming that E and F are CPOs, we say that f is continuous 
if and only if the image of any chain G of E by f has a least upper bound, 
that is, such that ⊔{f(x) | x ∈ G} = f(⊔G).

A function f : E -> F, where E and F are CPOs, is continuous when for all chains G of E,
the image of f on G has a lub ⊔{f(x) | x ∈ G}, and ⊔{f(x) | x ∈ G} = f(⊔G)
*)

(* Define the image of a subset on f *)
Definition ImageSubsetProp {E F : Type} (P : SubsetProp E) (func : E -> F) : SubsetProp F :=
  fun f => exists (e : E),  P e /\ func e = f.

Definition Continuous {E F : Type} {RE : relation E} {RF : relation F} {ORE : OrderRelation E RE}
                       {ORF : OrderRelation F RF} (CPOE : CompletePartialOrder ORE) (CPOF : CompletePartialOrder ORF)
                       (f : E -> F) : Prop := 
  forall (P : SubsetProp E) (G : Chain P ORE) (lub_e : E), 
  LeastUpperBound_Subset P ORE lub_e -> 
  exists (lub_fe : F), LeastUpperBound_Subset (ImageSubsetProp P f) ORF lub_fe /\ lub_fe = f lub_e.

(* A continuous function is also monotone *)
Lemma continuous_impl_monotone : forall (E F: Type) (RE : relation E) (RF : relation F) (ORE : OrderRelation E RE)
                                        (ORF : OrderRelation F RF) (CPOE : CompletePartialOrder ORE) (CPOF : CompletePartialOrder ORF)
                                        (f : E -> F),
  Continuous CPOE CPOF f -> Monotonic ORE ORF f.
Proof.
  intros.
  unfold Continuous in H.
  unfold Monotonic. intros.  (* lub_e = y, lub_fe = f lub_e , lub_fe = (f y) -> RF (f x) lub_fe *)
  remember (fun e : E => e = x \/ e = y) as PS eqn:EqPS.
  specialize (H PS).
  assert (ps_proj_value : (forall v : Subset PS, proj1_sig v = x \/ proj1_sig v = y)). {
    intros. unfold proj1_sig. destruct v. rewrite EqPS in p. destruct p; auto.
  }
  assert (ps_proj_f_value : (forall v : Subset (ImageSubsetProp PS f), proj1_sig v = f x \/ proj1_sig v = f y)).
  {
    intros. unfold proj1_sig. destruct v. unfold ImageSubsetProp in i. rewrite EqPS in i.
    destruct i. destruct H1. destruct H1. rewrite H1 in *; auto. rewrite H1 in *. auto.
  }
  assert (ps_is_chain : Chain PS ORE). {
    unfold Chain.
    intros.
    unfold SubsetRelation.
    unfold proj1_sig. destruct x0. destruct y0. rewrite EqPS in *.
    destruct p; destruct p0; subst; auto; left; apply OR_reflexive.
  }
  assert (y_is_lube : LeastUpperBound_Subset PS ORE y). {
    unfold LeastUpperBound_Subset. intros.
    pose proof (ps_proj_value x0) as vx0.
    destruct vx0. rewrite H1 in *.
    - split.
      + assumption.
      + intros. assert (PS y). {rewrite EqPS. right. reflexivity. } 
        specialize (H2 (exist _ y H3)). assumption.
    - rewrite H1 in *. split.
      + apply OR_reflexive.
      + intros. assert (PS y). {rewrite EqPS. right. reflexivity. }
        specialize (H2 (exist _ y H3)). assumption.
  }
  specialize (H ps_is_chain y). apply H in y_is_lube.
  destruct y_is_lube as [lub_fe [H1 H2]].
  unfold LeastUpperBound_Subset in H1.
  assert (ImageSubsetProp PS f (f x)). {
    unfold ImageSubsetProp. exists x.
    split.
    - rewrite EqPS. left. reflexivity.
    - reflexivity.
    }
   specialize (H1 (exist _ (f x) H3)). destruct H1. rewrite H2 in H1. apply H1.
Qed.


Definition FixedPoint {E : Type} {R : relation E} (OR : OrderRelation E R) (f : E -> E) (fp : E) : Prop :=
  fp = f fp.

(* For a function f : E -> E, the least fixed point of a function is a value lfp such that
lfp = f lfp and for all fixpoints, lfp <= fp *)
Definition LeastFixedPoint {E : Type} {R : relation E} (OR : OrderRelation E R) (f : E -> E) (lfp : E) :=
  FixedPoint OR f lfp -> forall fp, FixedPoint OR f fp -> R lfp fp.

(* Inductive KleeneChain {E : Type} {R : relation E} {OR : OrderRelation E R} (CPO : CompletePartialOrder OR) (f : E -> E) : E -> Prop :=
  | KC_bot : KleeneChain CPO f CPO_bottom
  | KC_succ (e : E) : KleeneChain CPO f e -> KleeneChain CPO f (f e). *)

(* Compute the element of the nth value of kleene chain f^n(CPO_Bottom) *)
Fixpoint fix_f {E : Type} {R : relation E} {OR : OrderRelation E R} (CPO : CompletePartialOrder OR) (f : E -> E) (n : nat) : E :=
  match n with
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

(* If f is a monotonic function, f^n <= F^{S n} *)
Lemma fix_f_monotone_on_n : forall {E : Type} {R : relation E} {OR : OrderRelation E R} (CPO : CompletePartialOrder OR) (f : E -> E) (n :nat),
  Monotonic OR OR f -> R (fix_f CPO f n) (fix_f CPO f (S n)).
Proof.
  intros E R OR CPO f n.
  generalize dependent E.
  induction n.
  - intros. simpl. apply CPO_bottom_lessthan_f_bottom.
  - intros. simpl. apply IHn with (CPO := CPO) in H as H1. simpl in H1.
    apply H. assumption.
Qed.

(* Kleene chain is monotonic on n *)
Lemma fix_f_ordered_on_n : forall {E : Type} {R : relation E} {OR : OrderRelation E R} (CPO : CompletePartialOrder OR) (f : E -> E) (n n' :nat),
  Monotonic OR OR f -> n < n' -> R (fix_f CPO f n) (fix_f CPO f n').
Proof.
  intros E R OR CPO f n n' H H'.
  generalize dependent E.
  induction H'.
  - intros. apply fix_f_monotone_on_n. assumption.
  - intros. specialize (IHH' _ _ _ _ _ H). pose proof (fix_f_monotone_on_n CPO f m).
    specialize (H0 H). apply OR_transitive with (y := (fix_f CPO f m)); assumption.
Qed.


(* Define the kleene chain as a prop *)
Definition fix_f_iterates {E : Type} {R : relation E} {OR : OrderRelation E R} (CPO : CompletePartialOrder OR) (f : E -> E) : E -> Prop :=
  fun (e : E) => exists n, e = fix_f CPO f n.

(* Prove that the above definition of the kleene chain is indeed a chain *)
Lemma fix_f_iterates_is_chain : forall {E : Type} {R : relation E} {OR : OrderRelation E R} (CPO : CompletePartialOrder OR) (f : E -> E),
  Monotonic OR OR f -> Chain (fix_f_iterates CPO f) OR.
Proof.
  unfold Chain.
  intros. destruct x. destruct y. unfold fix_f_iterates in f0. unfold fix_f_iterates in f1.
  destruct f0. destruct f1. 
  destruct (x1 <? x2) eqn:Eqb.
  apply Nat.ltb_lt in Eqb.
  apply (fix_f_ordered_on_n CPO f x1 x2) in H.
  - left. unfold SubsetRelation. rewrite e. rewrite e0. simpl. assumption.
  - assumption.
  - apply Nat.ltb_ge in Eqb.
    inversion Eqb.
    + left. unfold SubsetRelation. simpl. 
      assert (x = x0). {
        rewrite e. rewrite e0. induction x1; rewrite H0; simpl; reflexivity.

      }
      rewrite H1. apply OR_reflexive.
    + apply Nat.succ_le_mono in H0. rewrite H1 in H0. apply Arith_base.le_S_gt_stt in H0.
      apply (fix_f_ordered_on_n CPO f x2 x1) in H0.
      * right. unfold SubsetRelation. simpl. rewrite e. rewrite e0. assumption.
      * assumption.
Qed.

(* if e is an element of the chain fix_f_iterates, than (f e) is also an element *)
Lemma f_f_fix_iterates_in_chain : forall {E : Type} {R : relation E} {OR : OrderRelation E R} (CPO : CompletePartialOrder OR) (f : E -> E) (e : E),
  (fix_f_iterates CPO f) e -> (fix_f_iterates CPO f) (f e).
Proof.
  intros. destruct H. unfold fix_f_iterates. exists (S x). simpl. rewrite H. reflexivity. 
Qed.

(* The lub of the kleene chain is equal to the image of the chain of f. 
   This is obvious, since the kleene chain will also contain the value of
   f^{S n} for all n *)
Lemma f_lub_equals_lub : forall (E : Type) (R : relation E) (OR : OrderRelation E R) (CPO : CompletePartialOrder OR) (f : E -> E) (lub : E),
  Monotonic OR OR f ->
  LeastUpperBound_Subset (fix_f_iterates CPO f) OR lub ->
  LeastUpperBound_Subset (ImageSubsetProp (fix_f_iterates CPO f) f) OR lub.
Proof.
  intros.
  unfold LeastUpperBound_Subset.
  split.
  - intros. destruct x as [fe Hfe].
    unfold ImageSubsetProp in Hfe.
    destruct Hfe as [e [Hfe fe_ident]].
    apply f_f_fix_iterates_in_chain in Hfe as Hffe. simpl.
    unfold LeastUpperBound_Subset in H0. specialize (H0 (exist _ (f e) Hffe)).
    destruct H0. simpl in H0. rewrite fe_ident in H0. assumption.
  - intros ub. intros Hub.
    destruct x as [fe Hfe].
    unfold ImageSubsetProp in Hfe.
    destruct Hfe as [e [He fe_ident]].
    unfold LeastUpperBound_Subset in H0. specialize (H0 (exist _ e He)).
    simpl in H0. destruct H0. specialize (H1 ub).

    assert (forall x : Subset (fix_f_iterates CPO f), R (proj1_sig x) ub). {
      intros. destruct x.
      simpl. unfold fix_f_iterates in f0. destruct f0.
      induction x0.
      - simpl in H2. rewrite H2. apply CPOleast_exists.
      - assert ((ImageSubsetProp (fix_f_iterates CPO f) f) x). {
        unfold ImageSubsetProp. exists (fix_f CPO f x0).
        split.
          - unfold fix_f_iterates. exists x0. reflexivity.
          - simpl in H2. symmetry. assumption.
        }
        specialize (Hub (exist _ x H3)). simpl in Hub. assumption.
    }
    apply H1 in H2. assumption.
Qed.

(* For a continuous function f, The LFP of f is the least upper bound of the chain
   consisting of the values of the iterates of f *)
Theorem Kleene_fp : forall (E : Type) (R : relation E) (OR : OrderRelation E R) (CPO : CompletePartialOrder OR) (f : E -> E),
  Continuous CPO CPO f -> exists lfp, LeastFixedPoint OR f lfp /\
  LeastUpperBound_Subset (ImageSubsetProp (fix_f_iterates CPO f) f) OR lfp.
Proof.
  intros.
  apply continuous_impl_monotone in H as mono.
  apply fix_f_iterates_is_chain with (CPO := CPO) in mono as ischain_fixf.
  apply (CPOsubset_lub_exists (fix_f_iterates CPO f)) in ischain_fixf as Hfixf.
  destruct Hfixf as [lub_fixf Hlub_fixf].

  (* apply continuity to fixf chain *)
  unfold Continuous in H.
  specialize (H (fix_f_iterates CPO f)).
  apply H with (lub_e := lub_fixf) in ischain_fixf. 2: assumption.
  clear H.
  destruct ischain_fixf as [flub_fixf cont].
  destruct cont as [Hflub_fixf cont].

  unfold LeastFixedPoint.
  (* By applying the definition of continuity, we get f lub_fixf = flub_fixf.
     We now need to show that lub_fixf is a fixpoint of f, that is, f lub_fixf = lub_fixf 
     Note that flub_fixf is the lub of f applied to the fixf chain, which equals lub of fixf *) 
  exists lub_fixf.
  split.
  - (* lub_fixf is lfp *) intros. unfold FixedPoint in *.
    assert (forall n, R (fix_f CPO f n) fp). {
      intros n.
      induction n.
      - simpl. apply CPOleast_exists.
      - simpl. apply mono in IHn. rewrite <- H0 in IHn. assumption.
    }

    assert (forall n, R (fix_f CPO f n) lub_fixf). {
      intros n.
      induction n.
      - simpl. apply CPOleast_exists.
      - simpl. apply mono in IHn. rewrite <- H in IHn. assumption.
    }
    unfold LeastUpperBound_Subset in Hlub_fixf.
    assert ((fix_f_iterates CPO f) (fix_f CPO f 0)). {
      unfold fix_f_iterates. exists 0. reflexivity.
    }
    specialize (Hlub_fixf (exist _ (fix_f CPO f 0) H3)).
    destruct Hlub_fixf. specialize (H5 fp).
    assert (forall x : Subset (fix_f_iterates CPO f), R (proj1_sig x) fp). {
      intros. destruct x. unfold fix_f_iterates in f0. destruct f0.
      specialize (H1 x0). simpl. subst. assumption.
    }
    apply H5 in H6. assumption.
  - (* lub_fixf is lfp of f(G) *) apply f_lub_equals_lub in Hlub_fixf; assumption.
Qed.
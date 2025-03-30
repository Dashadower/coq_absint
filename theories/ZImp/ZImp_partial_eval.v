Print LoadPath.
From AbsInt.ZImp Require Import ZImp_partial.
From AbsInt Require Import Maps.
From Coq Require Import ZArith.
From Coq Require Import Nat.
From Coq Require Import Lia.

Inductive ceval_func_result : Type :=
  | CFTerminates (st : ceval_result)
  | CFDiverges.

Fixpoint ceval_func (st : ceval_result) (c : com) (fuel : nat) : ceval_func_result :=
  match fuel with
  | 0%nat => CFDiverges
  | S fuel' => 
    match st with
    | CError => CFTerminates CError
    | CNormal st' =>
      match c with
      | CSkip => CFTerminates st
      | CAsgn var_name a_exp => 
        match (aeval st' a_exp) with
        | ANormal a' => CFTerminates (CNormal (var_name |-> a' ; st'))
        | AError => CFTerminates CError
        end
      | CSeq c1 c2 =>
        match (ceval_func st c1 fuel') with
        | CFDiverges => CFDiverges
        | CFTerminates st'' => (ceval_func st'' c2 fuel')
        end
      | CIf b c1 c2 => 
        match (beval st' b) with
        | BError => CFTerminates CError
        | BNormal b' => 
          match b' with
          | true => ceval_func st c1 fuel'
          | false => ceval_func st c2 fuel'
          end
        end
      | CWhile b cbody =>
        match (beval st' b) with
        | BError => CFTerminates CError
        | BNormal b' =>
          match b' with
          | true => 
            match (ceval_func st cbody fuel') with
            | CFDiverges => CFDiverges
            | CFTerminates st'' => ceval_func st'' c fuel'
            end
          | false => CFTerminates st
          end
        end
      end
    end
  end.


Lemma ceval_func_step_more: forall f1 f2 st st' c,
  (f1 <= f2)%nat -> ceval_func st c f1 = CFTerminates st' -> ceval_func st c f2 = CFTerminates st'.
Proof.
  intros f1.
  induction f1 as [|f1']; intros f2 st st' c Hle Hceval.
  - simpl in Hceval. discriminate Hceval.
  - destruct f2.
    + inversion Hle.
    + assert (Hle': (f1' <= f2)%nat) by lia.
      destruct c.
      * simpl in Hceval. simpl. assumption.
      * inversion Hceval. simpl. reflexivity.
      * destruct (ceval_func st c1 f1') eqn:Eqcf.
        ** apply (IHf1' f2) in Eqcf as Eqcf2; try assumption. simpl in Hceval.
           rewrite Eqcf in Hceval.
           
           destruct st eqn:Eqst.
           *** simpl. rewrite Eqcf2. apply (IHf1' f2) in Hceval; assumption.
           *** simpl. assumption.
        ** destruct st eqn:Eqst.
           *** simpl in Hceval. rewrite Eqcf in Hceval. discriminate Hceval.
           *** simpl in Hceval. simpl. assumption.
      * destruct st eqn:Eqst.
        ** destruct (beval st0 b) eqn:Eqb.
           *** simpl in Hceval. destruct b0.
               **** rewrite Eqb in Hceval. apply (IHf1' f2) in Hceval; try assumption.
                    simpl. rewrite Eqb. assumption.
               **** rewrite Eqb in Hceval. apply (IHf1' f2) in Hceval; try assumption.
                    simpl. rewrite Eqb. assumption.
           *** simpl in Hceval. rewrite Eqb in Hceval. simpl. rewrite Eqb. assumption.
        ** simpl in Hceval. simpl. assumption.
      * destruct st eqn:Eqst.
        ** destruct (beval st0 b) eqn:Eqb.
           *** simpl in Hceval. destruct b0.
               **** rewrite Eqb in Hceval. destruct (ceval_func (CNormal st0) c f1') eqn:Eqce.
                    ***** apply (IHf1' f2) in Hceval; try assumption. simpl. rewrite Eqb.
                          apply (IHf1' f2) in Eqce; try assumption. rewrite Eqce. assumption.
                    ***** discriminate Hceval.
               **** rewrite Eqb in Hceval. simpl. rewrite Eqb. assumption.
           *** simpl. rewrite Eqb. simpl in Hceval. rewrite Eqb in Hceval. assumption.
        ** simpl. simpl in Hceval. assumption.
Qed. 
           

Theorem ceval_implies_ceval_func: forall c st st',
  st =[ c ]=> st' -> exists fuel, ceval_func st c fuel = CFTerminates st'.
Proof.
  intros c st st'.
  intros H.
  induction H; subst.
  - exists 1%nat. simpl. reflexivity.
  - exists 1%nat. simpl. rewrite H. reflexivity.
  - exists 1%nat. simpl. rewrite H. reflexivity.
  - destruct IHceval1. destruct IHceval2. exists (add x x0).
    destruct x.
    + simpl in *. discriminate H1.
    + simpl. destruct x0.
      * simpl in H2. discriminate H2.
      * simpl.
      
      
    


Theorem ceval_func_and_ceval_coincide: forall c st st',
  st =[ c ]=> st' <-> exists fuel, ceval_func st c fuel = CFTerminates st'.
Proof.
  intros c.
  split.
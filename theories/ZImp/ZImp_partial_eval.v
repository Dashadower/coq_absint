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
  CNormal st =[ c ]=> st' -> exists fuel, ceval_func (CNormal st) c fuel = CFTerminates st'.
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
      * apply ceval_func_step_more with (f2 := (x + S x0)%nat) in H1.
        ** rewrite H1. apply ceval_func_step_more with (f2 := (x + S x0)%nat) in H2.
           *** assumption.
           *** lia.
        ** lia.
  - destruct IHceval. exists (S x). destruct x.
    + simpl in H0. discriminate H0.
    + simpl in *. rewrite H0. reflexivity.
  - destruct IHceval1. destruct IHceval2. exists (S (x + x0))%nat.
    simpl. apply ceval_func_step_more with (f2 := (x + x0)%nat)in H1; try lia.
    rewrite H1. apply ceval_func_step_more with (f2 := (x + x0)%nat)in H2; try lia.
    assumption.
  - destruct IHceval. exists (S x). destruct x.
    + simpl in H1. discriminate H1.
    + simpl. simpl in H1. rewrite H1. rewrite H. reflexivity.
  - destruct IHceval. exists (S x). destruct x.
    + simpl in H1. discriminate H1.
    + simpl. simpl in H1. rewrite H1. rewrite H. reflexivity.
  - exists 1%nat. simpl. rewrite H. reflexivity.
  - destruct IHceval. exists (S x). simpl. rewrite H. assumption.
  - destruct IHceval. exists (S x). simpl. rewrite H. assumption.
  - exists 1%nat. simpl. rewrite H. reflexivity.
  - destruct IHceval1. destruct IHceval2. exists (S (x + x0)%nat).
    simpl. rewrite H. apply ceval_func_step_more with (f2 := (x + x0)%nat) in H2; try lia.
    rewrite H2. apply ceval_func_step_more with (f2 := (x + x0)%nat) in H3; try lia.
    assumption.
  - exists 1%nat. simpl. rewrite H. reflexivity.
  - destruct IHceval. exists (S x). simpl. rewrite H. rewrite H1. destruct x.
    + simpl in H1. discriminate H1.
    + simpl. reflexivity.
  - destruct IHceval1. destruct IHceval2. exists (S (x + x0)%nat). simpl.
    rewrite H. apply ceval_func_step_more with (f2 := (x + x0)%nat) in H2; try lia.
    rewrite H2. apply ceval_func_step_more with (f2 := (x + x0)%nat) in H3; try lia.
    assumption.
Qed.

Theorem ceval_fun_implies_ceval: forall c st st',
  (exists fuel, ceval_func (CNormal st) c fuel = CFTerminates st') -> (CNormal st) =[ c ]=> st'.
Proof.
  intros c st st' H. destruct H as [fuel H].
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction fuel.
  - intros. simpl in H. discriminate H.
  - intros. destruct c.
    + inversion H. apply E_Skip.
    + destruct (aeval st a) eqn:Eqa.
      * simpl in H. rewrite Eqa in H. inversion H. apply E_Asgn. assumption.
      * simpl in H. rewrite Eqa in H. inversion H. apply E_AsgnError. assumption.
    + simpl in H. destruct (ceval_func (CNormal st) c1 fuel) eqn:Eqc.
      * apply IHfuel in Eqc. destruct st0 eqn:Eqs.
        ** apply IHfuel in H. destruct st' eqn:Eqs'.
           *** apply E_Seq with (c2 := c2) (st' := st1) (st'' := st2) in Eqc; assumption.
           *** apply E_SeqError2 with (st' := st1); assumption.
        ** destruct st' eqn:Eqs'.
           *** destruct fuel.
               **** simpl in H. discriminate H.
               **** simpl in H. discriminate H.
           *** apply E_SeqError1. assumption.
      * discriminate H.
    + simpl in H. destruct (beval st b) eqn:Eqb.
      * destruct b0 eqn:Eqb'.
        ** apply IHfuel in H. destruct st' eqn:Eqst'.
           *** apply E_IfTrue; assumption.
           *** apply E_IfErrorTrue; assumption.
        ** apply IHfuel in H. destruct st' eqn:Eqst'.
           *** apply E_IfFalse; assumption.
           *** apply E_IfErrorFalse; assumption.
      * destruct st' eqn:Eqst'.
        ** discriminate H.
        ** apply E_IfError. assumption.
    + simpl in H. destruct (beval st b) eqn:Eqb.
      * (* beval st b = BNormal b0 *) destruct b0 eqn:Eqb'.
        -- (* beval st b = BNormal true*) destruct (ceval_func (CNormal st) c fuel) eqn:Eqc.
           ++ (* ceval_func (CNormal st) c fuel = CFTerminates st0 *) 
               destruct st0 eqn:Eqs.
               ** apply IHfuel in H. apply IHfuel in Eqc. 
                  destruct st'.
                  --- apply E_WhileTrue with (st' := st1); assumption.
                  --- apply E_WhileBodyUnrollError with (st' := st1); assumption. 
               ** apply IHfuel in Eqc as Eqc'. destruct st'.
                  --- destruct fuel; simpl in H; discriminate H.
                  --- apply E_WhileBodyError; assumption.
           ++ discriminate H.
        -- injection H. intros. rewrite <- H0. apply E_WhileFalse. assumption.
      * injection H. intros. rewrite <- H0. apply E_WhileGuardError. assumption.
Qed. 


(*
There exists some fuel value for ceval_func such that,
starting execution from a normal program state st,
ceval_func terminates with some execution result st',
if and only c can reduce to st' starting from a normal program state st by
the defined big-step semantics relation.
*)


Theorem ceval_func_and_ceval_coincide: forall c st st',
  CNormal st =[ c ]=> st' <-> exists fuel, ceval_func (CNormal st) c fuel = CFTerminates st'.
Proof.
  intros c.
  split.
  - apply ceval_implies_ceval_func.
  - apply ceval_fun_implies_ceval.
Qed.
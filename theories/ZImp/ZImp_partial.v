Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
Print LoadPath.
From AbsInt Require Import Maps.
From Coq Require Import ZArith.

Inductive aexp : Type :=
  | AInt (n : Z)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion AInt : Z >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.

Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
Open Scope Z_scope.
Open Scope com_scope.

Definition empty_st := empty (A := Z).

Print empty_st.

Definition state := partial_map Z.

Inductive ceval_result : Type :=
  | CNormal (st : state)
  | CError.

Inductive aeval_result : Type :=
  | ANormal (z : Z)
  | AError.

Inductive beval_result : Type :=
  | BNormal (b : bool)
  | BError.

Fixpoint aeval (st : state) (a : aexp) : aeval_result :=
  match a with
  | AInt n => ANormal n
  | AId x => 
    match (st x) with
    | Some v => ANormal v
    | None => AError
    end
  | <{a1 + a2}> => 
    match (aeval st a1) with
    | ANormal a1v => 
      match (aeval st a2) with
      | ANormal a2v => ANormal (a1v + a2v)
      | AError => AError
      end
    | AError => AError
    end
  | <{a1 - a2}> => 
    match (aeval st a1) with
    | ANormal a1v => 
      match (aeval st a2) with
      | ANormal a2v => ANormal (a1v - a2v)
      | AError => AError
      end
    | AError => AError
    end
  | <{a1 * a2}> => 
    match (aeval st a1) with
    | ANormal a1v => 
      match (aeval st a2) with
      | ANormal a2v => ANormal (a1v * a2v)
      | AError => AError
      end
    | AError => AError
    end
  end.

Fixpoint beval (st : state) (b : bexp) : beval_result :=
  match b with
  | BTrue => BNormal true
  | BFalse => BNormal false
  | BEq a1 a2 => 
    match (aeval st a1) with
    | ANormal ar1 =>
      match (aeval st a2) with
      | ANormal ar2 => BNormal (Z.eqb ar1 ar2)
      | AError => BError
      end
    | AError => BError
    end
  | BNeq a1 a2 =>
    match (aeval st a1) with
    | ANormal ar1 =>
      match (aeval st a2) with
      | ANormal ar2 => BNormal (negb (Z.eqb ar1 ar2))
      | AError => BError
      end
    | AError => BError
    end
  | BLe a1 a2 =>
    match (aeval st a1) with
    | ANormal ar1 =>
      match (aeval st a2) with
      | ANormal ar2 => BNormal (Z.leb ar1 ar2)
      | AError => BError
      end
    | AError => BError
    end
  | BGt a1 a2 =>
    match (aeval st a1) with
    | ANormal ar1 =>
      match (aeval st a2) with
      | ANormal ar2 => BNormal (negb (Z.leb ar1 ar2))
      | AError => BError
      end
    | AError => BError
    end
  | BNot b1 => 
    match (beval st b1) with 
    | BNormal true => BNormal false
    | BNormal false => BNormal true
    | BError => BError
    end
  | BAnd b1 b2 =>
    match (beval st b1) with
    | BNormal b1' =>
      match (beval st b2) with
      | BNormal b2' => BNormal (andb b1' b2')
      | BError => BError
      end
    | BError => BError
    end
  end.


Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'" :=
  CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
  (CAsgn x y)
     (in custom com at level 0, x constr at level 0,
      y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (CSeq x y)
    (in custom com at level 90,
     right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (CIf x y z)
    (in custom com at level 89, x at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (CWhile x y)
    (in custom com at level 89, x at level 99,
     y at level 99) : com_scope.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Reserved Notation
  "st '=[' c ']=>' st'"
  (at level 40, c custom com at level 99,
    st constr, st' constr at next level).

Inductive ceval : com -> ceval_result -> ceval_result -> Prop :=
  | E_Skip : forall st,
    CNormal st =[ skip ]=> CNormal st
  | E_Asgn : forall st a n x,
    aeval st a = ANormal n ->
    CNormal st =[ x := a ]=> CNormal (x |-> n ; st)
  | E_AsgnError : forall st a x,
    aeval st a = AError ->
    CNormal st =[x := a]=> CError
  | E_Seq : forall c1 c2 st st' st'',
    CNormal st  =[ c1 ]=> CNormal st'  ->
    CNormal st' =[ c2 ]=> CNormal st'' ->
    CNormal st  =[ c1 ; c2 ]=> CNormal st''
  | E_SeqError1 : forall c1 c2 st,
    CNormal st =[ c1 ]=> CError ->
    CNormal st  =[ c1 ; c2 ]=> CError
  | E_SeqError2 : forall c1 c2 st st',
    CNormal st =[ c1 ]=> CNormal st' ->
    CNormal st' =[ c2 ]=> CError ->
    CNormal st  =[ c1 ; c2 ]=> CError
  | E_IfTrue : forall st st' b c1 c2,
    beval st b = BNormal true ->
    CNormal st =[ c1 ]=> CNormal st' ->
    CNormal st =[ if b then c1 else c2 end]=> CNormal st'
  | E_IfFalse : forall st st' b c1 c2,
    beval st b = BNormal false ->
    CNormal st =[ c2 ]=> CNormal st' ->
    CNormal st =[ if b then c1 else c2 end]=> CNormal st'
  | E_IfError : forall st b c1 c2,
    beval st b = BError ->
    CNormal st =[ if b then c1 else c2 end ]=> CError
  | E_IfErrorTrue : forall st b c1 c2,
    beval st b = BNormal true ->
    CNormal st =[ c1 ]=> CError ->
    CNormal st =[ if b then c1 else c2 end ]=> CError
  | E_IfErrorFalse : forall st b c1 c2,
    beval st b = BNormal false ->
    CNormal st =[ c2 ]=> CError ->
    CNormal st =[ if b then c1 else c2 end ]=> CError
  | E_WhileFalse : forall b st c,
    beval st b = BNormal false ->
    CNormal st =[ while b do c end ]=> CNormal st
  | E_WhileTrue : forall st st' st'' b c,
    beval st b = BNormal true ->
    CNormal st  =[ c ]=> CNormal st' ->
    CNormal st' =[ while b do c end ]=> CNormal st'' ->
    CNormal st  =[ while b do c end ]=> CNormal st''
  | E_WhileGuardError : forall st b c,
    beval st b = BError ->
    CNormal st =[ while b do c end]=> CError
  | E_WhileBodyError : forall st b c,
    beval st b = BNormal true ->
    CNormal st =[ c ]=> CError ->
    CNormal st  =[ while b do c end ]=> CError
  (* | E_WhileBodyUnrollError : forall st st' b c,
    beval st b = BNormal true ->
    CNormal st =[ c ]=> CNormal st' ->
    CNormal st' =[ while b do c end ]=> CError ->
    CNormal st =[ while b do c end]=> CError *)

  where "st =[ c ]=> st'" := (ceval c st st').


Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2.
  - (* E_Skip *)
    inversion E2. reflexivity.
  - (* E_Asgn *)
    inversion E2; subst.
    + rewrite H in H4. injection H4. intros. subst. reflexivity.
    + rewrite H in H4. discriminate H4.
  - (* E_AsgnError *)
    inversion E2; subst.
    + rewrite H in H4. discriminate H4.
    + reflexivity.
  - (* E_Seq *)
    inversion E2;subst.
    + apply IHE1_2. apply IHE1_1 in H2. rewrite <- H2 in H4. assumption.
    + apply IHE1_1 in H3. rewrite H3 in E1_2. inversion E1_2.
    + apply IHE1_1 in H2. rewrite <- H2 in H4. apply IHE1_2 in H4. assumption.
  - (* E_SeqError1 *)
    inversion E2; subst.
    + apply IHE1 in H2. discriminate H2.
    + reflexivity.
    + reflexivity.
  - (* E_SeqError2 *)
    inversion E2; subst.
    + apply IHE1_1 in H2. rewrite <- H2 in H4. apply IHE1_2 in H4. discriminate H4.
    + reflexivity.
    + reflexivity.
  - (* E_IfTrue *)
    inversion E2; subst.
    + apply IHE1 in H6. assumption.
    + rewrite H in H5. discriminate H5.
    + rewrite H in H5. discriminate H5.
    + apply IHE1 in H6. assumption.
    + rewrite H in H5. discriminate H5. 
  - (* E_IfFalse *)
    inversion E2; subst.
    + rewrite H in H5. discriminate H5.
    + apply IHE1 in H6. assumption.
    + rewrite H in H5. discriminate H5.
    + rewrite H in H5. discriminate H5.
    + apply IHE1 in H6. discriminate H6.
  - (* E_IfError *)
    inversion E2; subst.
    + rewrite H in H5. discriminate H5.
    + rewrite H in H5. discriminate H5.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - (* E_IfErrorTrue *)
    inversion E2; subst; auto. rewrite H in H5. discriminate H5.
  - (* E_IfErrorFalse *)
    inversion E2; subst; auto. rewrite H in H5. discriminate H5.
  - (* E_WhileFalse *)
    inversion E2; subst.
    + reflexivity.
    + rewrite H in H3. discriminate H3.
    + rewrite H in H4. discriminate H4.
    + rewrite H in H3. discriminate H3.
  - (* E_WhileTrue *)
    inversion E2;subst.
    + rewrite H in H4. discriminate H4.
    + apply IHE1_1 in H4. rewrite <- H4 in *. apply IHE1_2 in H6. assumption.
    + rewrite H in H4. discriminate H4.
    + apply IHE1_1 in H5. discriminate H5.
  - (* E_WhileGuardError *)
    inversion E2; subst.
    + rewrite H in H4. discriminate H4.
    + rewrite H in H3. discriminate H3.
    + reflexivity.
    + reflexivity.
  - (* E_WhileBodyError *)
    inversion E2; subst.
    + rewrite H in H4. discriminate H4.
    + apply IHE1 in H4. discriminate H4.
    + reflexivity.
    + reflexivity.
Qed.

Theorem ceval_sound_fail : forall c st ,
  (exists st', CNormal st =[ c ]=> CNormal st') \/ CNormal st =[ c ]=> CError.
Proof.
  intros c.
  induction c; intros.
  - (* CSkip *) 
    left. exists st. apply E_Skip.
  - (* CAsgn *)
    destruct (aeval st a) eqn:Eq.
    + left. exists (x |-> z ; st). apply E_Asgn. assumption.
    + right. apply E_AsgnError. assumption.
  - (* CSeq *)
    destruct (IHc1 st).
    + (* C1 evals normally *)
      destruct H as [st' H1]. destruct (IHc2 st').
      * (* C2 evals normally *) 
        left. destruct H as [st'0 H2]. exists st'0. apply E_Seq with (st' := st'); assumption.
      * (* C2 errors *)
        right. apply E_SeqError2 with (c2 := c2) in H1; assumption.
    + (* C2 errors *)
      right. apply E_SeqError1. assumption.
  - (* CIf *)
    destruct (beval st b) eqn:Eqb.
    + destruct b0.
        * destruct (IHc1 st). destruct H as [st' H].
          ** (* C1 evals normally *)
             left. exists st'. apply E_IfTrue; assumption.
          ** (* C1 errors *)
             right. apply E_IfErrorTrue; assumption.
        * destruct (IHc1 st). 
          ** destruct H as [st' H]. destruct (IHc2 st).
             *** (* C2 evals normally*)
                 destruct H0 as [st'0 H1]. left. exists st'0. apply E_IfFalse; assumption.
             *** (* C2 errors *)
                 right. apply E_IfErrorFalse; assumption.
          ** destruct (IHc2 st).
             *** (* C2 evals normally *)
                 destruct H0 as [st'0 H1]. left. exists st'0. apply E_IfFalse; assumption.
             *** (* C2 errors *)
                 right. apply E_IfErrorFalse; assumption.
    + right. apply E_IfError. assumption.
  - (* CWhile *)
    destruct (beval st b) eqn:Eqb.
    + destruct b0.
      * (* true *) 
        destruct (IHc st).
        ** (* c evals normally *)
           destruct H as [st' H].
           Abort. (* big-step semantics does not allow us to reason about non-termination!! *)

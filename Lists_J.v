Require Export Basics_J.

Module NatList.
Inductive natprod : Type :=
 pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
 match p with
  | pair x y => x
 end.

Definition snd (p : natprod) : nat :=
 match p with
  | pair x y => y
 end.


Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
 match p with
  | (x,y) => x
 end.

Definition snd' (p : natprod) : nat :=
 match p with
  | (x,y) => y
 end.

Definition swap_pair (p : natprod) : natprod :=
 match p with
  | (x,y) => (y,x)
 end.

Theorem surjective_pairing' : forall (n m : nat), (n,m) = (fst (n,m), snd (n,m)).
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod), p = (fst p, snd p).
Proof.
intros p.
destruct p as (n,m).
simpl.
reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod), (snd p, fst p) = swap_pair p.
Proof.
intros.
destruct p as (n,m).
simpl.
reflexivity.
Qed.

Inductive natlist : Type :=
 | nil : natlist
 | cons : nat -> natlist -> natlist.

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)(at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
 match count with
  | O => nil
  | S count' => n :: (repeat n count')
 end.

Fixpoint length (l : natlist) : nat :=
 match l with
  | nil => O
  | h :: t => S (length t)
 end.

Fixpoint app (l1 l2 : natlist) : natlist :=
 match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
 end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof.
simpl.
reflexivity.
Qed.

Example test_app2: nil ++ [4,5] = [4,5].
Proof.
simpl.
reflexivity.
Qed.

Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof.
simpl.
reflexivity.
Qed.

Definition hd (default : nat)(l : natlist) : nat :=
 match l with
  | nil => default
  | h :: t => h
 end.

Eval simpl in (hd O [1,2,3,4,5]).

Definition tail (l : natlist) : natlist :=
 match l with
  | nil => nil
  | h :: t => t
 end.

Eval simpl in (tail [1,2,3,4,5]).

Example test_hd1 : hd O [1,2,3] = 1.
Proof.
simpl.
reflexivity.
Qed.

Example test_hd2 : hd O [] = 0.
Proof.
simpl.
reflexivity.
Qed.

Example test_tail : tail [1,2,3] = [2,3].
Proof.
simpl.
reflexivity.
Qed.

Definition bag := natlist.



(*-----<<< Inference about the lists >>>------*)
Theorem nil_app : forall (l : natlist), [] ++ l = l.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem tl_lentgh_pred : forall (l : natlist), pred (length l) = length (tail l).
Proof.
intros.
destruct l.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.


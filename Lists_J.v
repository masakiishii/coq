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

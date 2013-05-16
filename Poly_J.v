Require Export Lists_J.

Inductive list (X : Type) : Type :=
 | nil : list X
 | cons : X -> list X -> list X.

Fixpoint length (X : Type) (l : list X) : nat :=
 match l with
  | nil => O
  | cons h t => S (length X t)
 end.

Example test_length1: length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof.
intros.
simpl.
reflexivity.
Qed.

Example test_length2: length bool (cons bool true (nil bool)) = 1.
Proof.
simpl.
reflexivity.
Qed.

Fixpoint app (X : Type) (l1 l2 : list X) : (list X) :=
 match l1 with
  | nil => l2
  | cons h t => cons X h (app X t l2)
 end.

Fixpoint snoc (X : Type) (l : list X) (v : X) : (list X) :=
 match l with
  | nil => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
 end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil => nil X
  | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof.
reflexivity.
Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof.
reflexivity.
Qed.

Fixpoint length' (X : Type) (l : list X) : nat :=
 match l with
  | nil => O
  | cons h t => S ( length' _ t)
 end.

Definition list123 := cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X:Type} (l:list X) : nat :=
 match l with
  | nil => O
  | cons h t => S (length'' t)
 end.

(*-------<<< Pairs polymorphic >>>--------*)
Inductive prod (X Y : Type) : Type :=
 | pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).
Notation " X * Y " := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
 match p with 
  |(x,y) => x
 end.

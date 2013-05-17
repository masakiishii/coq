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

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

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

Definition snd {X Y : Type} (p : X * Y) : Y :=
 match p with
  |(x,y) => y
 end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
 match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
 end.

Fixpoint combine' {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
 match lx,ly with
  | [],_ => []
  | _,[] => []
  | x::tx, y::ty => (x,y) :: (combine' tx ty)
 end.

Check @combine.
Eval simpl in (combine [1,2] [false,false,true,true]).

(*-------<<< Polymorphic option >>>--------*)

Inductive option (X : Type) : Type :=
 | Some : X -> option X
 | None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

(* ---------<<< Function as a data >>>---------- *)


Definition doit3times {X : Type} (f:X -> X) (n : X) : X := f (f (f n)).

Check @doit3times.

Example test_doit3times : doit3times minustwo 9 = 3.
Proof.
reflexivity.
Qed.

Example test_doit3times' : doit3times negb true = false.
Proof.
reflexivity.
Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof.
reflexivity.
Qed.

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y, prod_curry (prod_uncurry f) x y = f x y.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y), prod_uncurry (prod_curry f) p = f p.
Proof.
intros.
destruct p.
reflexivity.
Qed.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : (list X) :=
 match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t) else filter test t
 end.

Example test_filter1 : filter evenb [1,2,3,4] = [2,4].
Proof.
reflexivity.
Qed.

Eval simpl in (filter evenb [1,2,3,4,5,6,7]).

Definition length_is_1 {X : Type} (l : list X) : bool := beq_nat (length l) 1.

Eval simpl in (filter length_is_1 [ [1,2], [3], [4], [5,6,7], [], [8] ]).


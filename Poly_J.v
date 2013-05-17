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

(* ---------<<< Map function >>>---------- *)

Fixpoint map {X Y:Type} (f:X -> Y) (l:list X)
             : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n,oddb n]) [2,1,2,5]
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity. Qed.

(* -------<<< Fold function >>>--------- *)



Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X: Type} (f: nat -> X) (k:nat) (x:X) : nat -> X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(* -------<<< unfold tactic >>>--------- *)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity. Qed.

Theorem override_eq : forall {X:Type} x k (f:nat -> X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity. Qed.


Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
Admitted.

(* -------<<< Inversion >>>--------*)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity. Qed.

Theorem silly5 : forall (n m o : nat),
     [n,m] = [o,o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.



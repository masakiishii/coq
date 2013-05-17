Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Theorem andb_true_elim1 : forall (b c : bool),
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity. Qed.

Theorem plus_0_r : forall (n:nat), n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall (n:nat),
  n * 0 = 0.
Proof.
Admitted.

Theorem plus_n_Sm : forall (n m : nat),
  S (n + m) = n + (S m).
Proof.
Admitted.

Theorem plus_comm : forall (n m : nat),
  n + m = m + n.
Proof.
Admitted.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
Admitted.

Theorem plus_assoc' : forall (n m p : nat),
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_assoc : forall (n m p : nat),
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem beq_nat_refl : forall (n : nat),
  true = beq_nat n n.
Proof.
Admitted.

Theorem mult_0_plus' : forall (n m : nat),
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall (n m p q : nat),
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Admitted.

Theorem plus_rearrange : forall (n m p q : nat),
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity. Qed.

Theorem plus_swap : forall (n m p : nat),
  n + (m + p) = m + (n + p).
Proof.
Admitted.

Theorem mult_comm : forall (m n : nat),
 m * n = n * m.
Proof.
Admitted.

Theorem evenb_n__oddb_Sn : forall (n : nat),
  evenb n = negb (evenb (S n)).
Proof.
Admitted.

Theorem ble_nat_refl : forall (n:nat),
  true = ble_nat n n.
Proof.
Admitted.

Theorem zero_nbeq_S : forall (n:nat),
  beq_nat 0 (S n) = false.
Proof.
Admitted.

Theorem andb_false_r : forall (b : bool),
  andb b false = false.
Proof.
Admitted.

Theorem plus_ble_compat_l : forall (n m p : nat),
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
Admitted.

Theorem S_nbeq_0 : forall (n:nat),
  beq_nat (S n) 0 = false.
Proof.
Admitted.

Theorem mult_1_l : forall (n:nat), 1 * n = n.
Proof.
Admitted.

Theorem all3_spec : forall (b c : bool),
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
Admitted.

Theorem mult_plus_distr_r : forall (n m p : nat),
  (n + m) * p = (n * p) + (m * p).
Proof.
Admitted.

Theorem mult_assoc : forall (n m p : nat),
  n * (m * p) = (n * m) * p.
Proof.
Admitted.

Theorem plus_swap' : forall (n m p : nat),
  n + (m + p) = m + (n + p).
Proof.
Admitted.


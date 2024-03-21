Inductive bool : Type :=
  | true
  | false.
  
Definition neg (a:bool) : bool :=
 match a with
 |true =>false
 |false => true
 end.
   
Definition and (a:bool) (b:bool) : bool :=
  match a with
  | false =>false
  | true => b
  end.

Definition or (a:bool) (b:bool) : bool :=
  match a with
  | true => true
  | false => b
  end.
  
Example test_or1: (or true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_or2: (or false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_or3: (or false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_or4: (or true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (and x y).
Notation "x || y" := (or x y).
Example test_or5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Check true.
Check true : bool.
Check and.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof. intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.


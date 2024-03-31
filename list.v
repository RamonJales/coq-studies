From LF Require Export Induction.
Module NatList.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
  
Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.
  
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
  
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
  (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
  Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
  Proof. reflexivity. Qed.
  
Definition hd (default : nat) (l1 : natlist) : nat :=
  match l1 with
  |nil => default
  | x :: xs => x
  end.
  
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
  
Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
  
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | x :: xs => if x=? 0 then nonzeros xs 
    else x :: (nonzeros xs)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  |nil => l2
  |x :: xs => match l2 with
              |nil => x::xs
              |y::ys => x :: y ::
                  (alternate xs ys)
              end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
  Proof. reflexivity. Qed.
Compute alternate ([1;2]) ([3;4]).

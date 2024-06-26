From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 2 3) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
  
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
  
Compute (fst (pair 3 5)).
  
Notation "( x , y )" := (pair x y).

Compute (snd (3,5)).

Definition swap_pair (p : natprod) :
natprod :=
  match p with
  |(x,y) => (y,x)
  end.
  
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl.
  reflexivity.
Qed.
  
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
  

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive comparison : Type :=
  | Eq
  | Lt
  | Gt.
  
Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.
  
Compute letter_comparison B A.

Compute letter_comparison D D.

Compute letter_comparison B F.

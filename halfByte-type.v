Inductive bit: Type :=
  |B1
  |B0.
Inductive halfByte: Type :=
  |bits (b0 b1 b3 b4 : bit).

Check (bits B0 B0 B0 B0) : halfByte.

Definition all_zero (hb : halfByte) : bool :=
  match hb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).

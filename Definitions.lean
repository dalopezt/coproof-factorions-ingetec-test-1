import Mathlib

-- Generated from goal prompt
def digitFactorialSum (n : ℕ) : ℕ :=
  (Nat.digits 10 n).map Nat.factorial |>.sum

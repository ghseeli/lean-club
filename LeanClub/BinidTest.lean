import Mathlib.Data.Nat.Choose.Basic

#check Nat.choose

open Nat

def a (n : ℤ) : ℤ :=
  match (n % 3) with
  | 0 => 1
  | 1 => -1
  | _ => 0

#eval a 5
#eval a 6

lemma a_rec (n : ℤ) : a n = - a (n-1) - a (n-2) := by
  sorry

theorem BQ175 (n : ℕ) : ∑ k : Fin (n + 1), (-1 : ℤ)^(n-k) * (n-k).choose k = a n := by
  sorry

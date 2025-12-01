/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

Aristotle encountered an error processing this file. The team has been notified.

-/

import Mathlib.Data.Finite.Sum

theorem Raney (n : ℕ) (xs : ℕ → ℤ) (hper : ∀ (i : ℕ), xs i = xs (i+n)) (hsum : ∑ (i ∈ Fin n), xs i = 1): ∃ j : Fin n, ∀ g : Fin n, ∑ (k : Fin g.succ), xs (j + k) > 0 := by
  sorry

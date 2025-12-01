import Mathlib.Data.Finite.Sum

theorem Raney (n : ℕ) (xs : ℕ → ℤ) (hper : ∀ (i : ℕ), xs i = xs (i+n)) (hsum : ∑ (i ∈ Fin n), xs i = 1): ∃ j : Fin n, ∀ g : Fin n, ∑ (k : Fin g.succ), xs (j + k) > 0 := by
  sorry

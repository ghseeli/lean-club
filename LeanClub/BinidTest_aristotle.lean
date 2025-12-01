/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- lemma a_rec (n : ℤ) : a n = - a (n-1) - a (n-2)

- theorem BQ175 (n : ℕ) : ∑ k : Fin (n + 1), (-1 : ℤ)^(n-k) * (n-k).choose k = a n
-/

import Mathlib


open Nat

def a (n : ℤ) : ℤ :=
  match (n % 3) with
  | 0 => 1
  | 1 => -1
  | _ => 0

lemma a_rec (n : ℤ) : a n = - a (n-1) - a (n-2) := by
  -- By definition of $a$, we know that $a(n) = 1$ if $n \equiv 0 \pmod{3}$, $a(n) = -1$ if $n \equiv 1 \pmod{3}$, and $a(n) = 0$ if $n \equiv 2 \pmod{3}$.
  have h_cases : ∀ n : ℤ, a n = if n % 3 = 0 then 1 else if n % 3 = 1 then -1 else 0 := by
    aesop;
    · obtain ⟨ k, rfl ⟩ := h; norm_num [ a ] ;
    · unfold a; aesop;
    · unfold a; aesop;
  rw [ h_cases, h_cases, h_cases ] ; split_ifs <;> omega;

theorem BQ175 (n : ℕ) : ∑ k : Fin (n + 1), (-1 : ℤ)^(n-k) * (n-k).choose k = a n := by
  have h_sum : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * Nat.choose (n - k) k = a n := by
    -- We'll use induction to prove that the sum equals $a_n$ for all $n$.
    have h_ind : ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * Nat.choose (n - k) k) = if n % 3 = 0 then 1 else if n % 3 = 1 then -1 else 0 := by
      -- Now let's assume the induction hypothesis that the statement holds for all $m < n$.
      have h_ind : ∀ n ≥ 3, (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * Nat.choose (n - k) k) = - (∑ k ∈ Finset.range (n - 1 + 1), (-1 : ℤ) ^ (n - 1 - k) * Nat.choose (n - 1 - k) k) - (∑ k ∈ Finset.range (n - 2 + 1), (-1 : ℤ) ^ (n - 2 - k) * Nat.choose (n - 2 - k) k) := by
        intro n hn
        have h_split : ∑ k ∈  Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * Nat.choose (n - k) k = ∑ k ∈  Finset.range (n - 1 + 1), (-1 : ℤ) ^ (n - k) * Nat.choose (n - k) k + (-1 : ℤ) ^ (n - (n - 1)) * Nat.choose (n - (n - 1)) (n - 1) + (-1 : ℤ) ^ (n - n) * Nat.choose (n - n) n := by
          rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.sum_range_succ ];
          cases n <;> trivial;
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.sum_range_succ', Nat.choose_succ_succ ];
        rw [ Finset.sum_congr rfl fun x hx => by rw [ show n - x = n - ( x + 1 ) + 1 from by linarith [ Nat.sub_add_cancel ( show x + 1 ≤ n from by linarith [ Finset.mem_range.mp hx ] ), Nat.sub_add_cancel ( show x ≤ n from by linarith [ Finset.mem_range.mp hx ] ) ] ] ] ; norm_num [ pow_succ, Nat.choose_succ_succ, Finset.sum_add_distrib ] ; ring_nf;
        norm_num [ add_comm, add_left_comm, Finset.sum_add_distrib ] ; ring;
        cases n <;> norm_num at *;
      -- By induction, we can conclude that the statement holds for all $n$.
      intro n
      induction' n using Nat.strong_induction_on with n ih;
      rcases n with ( _ | _ | _ | n ) <;> simp_all +decide;
      norm_num [ Nat.add_mod ] ; have := Nat.mod_lt n zero_lt_three; interval_cases n % 3 <;> trivial;
    unfold a; aesop;
    all_goals omega;
  rw [ ← h_sum, Finset.sum_range ]

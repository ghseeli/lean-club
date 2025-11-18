import Mathlib

/-!
# Pfaffian

The Pfaffian of an alternating matrix

## Main definitions

## Main results

## TODO

* Define alternating matrices
* Define perfect matchings
* Define crossing number of perfect matching
* Define Pfaffian

## References

-/
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α]
variable {R : Type u} [CommRing R]

#check ∀ (x : α), true
def IsAlt {n : Finset α} (A : Matrix n n R) :=
  (∀ (i j : n), A j i = - (A i j)) ∧ (∀ (i : n), A i i = 0)

-- Unclear if LT is the right thing
-- Switch LT to LinearOrder
structure PerfectMatching (α : Type u) [Fintype α] [DecidableEq α] [LinearOrder α] where
  edges : Finset (α × α)
  ordered : ∀ b ∈ edges, b.1 < b.2
  disjoint : ∀ b₁ ∈ edges, ∀ b₂ ∈ edges,
    -- TODO Make this more elegant
    -- switched to Disjoint {b₁.1, b₁.2} {b₂.1, b₂.2}
    b₁ ≠ b₂ -> Disjoint ({b₁.1, b₁.2} : Finset α) ({b₂.1, b₂.2} : Finset α)
    -- b₁.1 ≠ b₂.1 ∧ b₁.1 ≠ b₂.2 ∧ b₁.2 ≠ b₂.1 ∧ b₁.2 ≠ b₂.2

  --union : ⋃ b ∈ edges, {b.1, b.2} = Set.univ := by decide
  union : ∀ (i : α), ∃ b ∈ edges, (i = b.1 ∨ i = b.2)


-- The following are attempts at examples
def pm_ex : PerfectMatching (Fin 4) :=
  ⟨{(0,1), (2,3)},
      by decide,by decide, by decide⟩

#eval pm_ex.edges

open scoped BigOperators
open Finset

-- 1b) If a perfect matching on S exists, then |S|is even.

def block {α} [Fintype α] [DecidableEq α] (b : α × α) : Finset α :=
  {b.1, b.2}

lemma block_card_two
    (M : PerfectMatching α) {b : α × α} (hb : b ∈ M.edges) :
    (block b).card = 2 :=
by
  classical
  -- from b.1 < b.2 we get b.1 ≠ b.2
  have hne : b.1 ≠ b.2 := ne_of_lt (M.ordered b hb)
  -- card {b.1, b.2} = 2 if b.1 ≠ b.2
  simp [block, hne]

theorem PerfectMatching.card_even (M : PerfectMatching α) :
  Even (Fintype.card α) := by
    classical

    -- The union of all blocks is all of α (perfect matching)
    have hcover :
        (M.edges.biUnion block : Finset α) = Finset.univ :=
      by
        ext i; constructor
        · intro _
          exact Finset.mem_univ _
        · intro _
          rcases M.union i with ⟨b, hb, hi⟩
          refine Finset.mem_biUnion.mpr ?_
          refine ⟨b, hb, ?_⟩
          rcases hi with rfl | rfl <;> simp [block]

    -- Now compute |α| as sum over blocks
    have hcard :
        Fintype.card α =
          ∑ b ∈ M.edges, (block b).card :=
      by
        -- |α| = |univ| = |⋃ blocks|
        have :
            (Finset.univ : Finset α).card =
              (M.edges.biUnion block).card :=
          by simp [hcover.symm]
        -- use card_biUnion with pairwise disjoint blocks
        have hsum :
            (M.edges.biUnion block).card =
              ∑ b ∈ M.edges, (block b).card :=
          by
            refine Finset.card_biUnion ?_
            intro b₁ hb₁ b₂ hb₂ hneq
            exact M.disjoint b₁ hb₁ b₂ hb₂ hneq
        -- combine
        have h_univ :
            (Finset.univ : Finset α).card = Fintype.card α :=
          by simpa using
            (Finset.card_univ : (Finset.univ : Finset α).card = Fintype.card α)
        calc
          Fintype.card α
              = (Finset.univ : Finset α).card := h_univ.symm
          _ = (M.edges.biUnion block).card := this
          _ = ∑ b ∈ M.edges, (block b).card := hsum

    -- Substitute each block.card = 2 and simplify
    have hsum2 :
        ∑ b ∈ M.edges, (block b).card = M.edges.card + M.edges.card :=
      by
        -- rewrite each term as 2
        have :
            ∑ b ∈ M.edges, (block b).card =
              ∑ b ∈ M.edges, (2 : ℕ) :=
          by
            refine Finset.sum_congr rfl ?_
            intro b hb
            apply block_card_two M hb
        -- sum of a constant over a finite set
        have h1 :
            ∑ b ∈ M.edges, (1 : ℕ) = M.edges.card :=
          by
            simpa using
              (Finset.card_eq_sum_ones (s := M.edges)).symm
        calc
          ∑ b ∈ M.edges, (block b).card
              = ∑ b ∈ M.edges, (2 : ℕ) := this
          _ = ∑ b ∈ M.edges, ((1 : ℕ) + 1) := by simp
          _ = (∑ b ∈ M.edges, (1 : ℕ)) +
              (∑ b ∈ M.edges, (1 : ℕ)) := by rw [Finset.sum_add_distrib]
          _ = M.edges.card + M.edges.card := by simp [h1]

    -- So |α| = 2 * |edges|, hence even
    refine ⟨M.edges.card, ?_⟩
    rw [hcard, hsum2]

example (M : PerfectMatching (Fin 4)) :
    Even (Fintype.card (Fin 4)) :=
  PerfectMatching.card_even M

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

def IsAlt (A : Matrix α α R) :=
  (∀ i j, A j i = - (A i j)) ∧ (∀ i, A i i = 0)

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
    (block b).card = 2 := by
    have hne : b.1 ≠ b.2 := ne_of_lt (M.ordered b hb)
    simp [block, hne]


lemma blocks_cover (M : PerfectMatching α) :
    (M.edges.biUnion block : Finset α) = Finset.univ := by
  ext i; constructor
  · intro _; exact Finset.mem_univ _
  · intro _
    rcases M.union i with ⟨b, hb, hi⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨b, hb, ?_⟩
    rcases hi with rfl | rfl <;> simp [block]


lemma card_eq_sum_block_card (M : PerfectMatching α) :
    Fintype.card α = ∑ b ∈ M.edges, (block b).card := by
  -- cardinality of the union of blocks as a sum
  calc
    Fintype.card α
        = (Finset.univ : Finset α).card := (Finset.card_univ (α := α)).symm
    _ = (M.edges.biUnion block : Finset α).card := by
          simp [blocks_cover M]
    _ = ∑ b ∈ M.edges, (block b).card := Finset.card_biUnion M.disjoint



theorem PerfectMatching.card_eq_twice_card_edges (M : PerfectMatching α) :
  Fintype.card α = 2 * M.edges.card :=
  calc Fintype.card α
    _ = ∑ b ∈ M.edges, (block b).card := card_eq_sum_block_card M
    _ = ∑ b ∈ M.edges, (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro b hb
        apply block_card_two M hb
        -- sum of a constant over a finite set
    _ = 2 * M.edges.card := by simp [mul_comm]

theorem PerfectMatching.card_even (M : PerfectMatching α) :
  Even (Fintype.card α) := by
    refine ⟨M.edges.card, ?_⟩
    rw [PerfectMatching.card_eq_twice_card_edges M]
    simp [two_mul]

theorem even_card_of_exists_PerfectMatching
    (h : Nonempty (PerfectMatching α)) :
    Even (Fintype.card α) := by
  obtain ⟨M⟩ := h
  exact PerfectMatching.card_even M

example : Even (Fintype.card (Fin 4)) :=
  even_card_of_exists_PerfectMatching (.intro pm_ex)

#check PerfectMatching.card_even pm_ex

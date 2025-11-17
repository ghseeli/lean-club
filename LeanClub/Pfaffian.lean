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
variable {α : Type u}
variable {R : Type u} [CommRing R]

#check ∀ (x : α), true
def IsAlt {n : Finset α} (A : Matrix n n R) :=
  (∀ (i j : n), A j i = - (A i j)) ∧ (∀ (i : n), A i i = 0)

-- Unclear if LT is the right thing
structure PerfectMatching (n : Finset α) [LT n] where
  edges : Finset (n × n)
  ordered : ∀ b ∈ edges, b.1 < b.2
  disjoint : ∀ b₁ ∈ edges, ∀ b₂ ∈ edges,
    --Disjoint {b₁.1, b₁.2} {b₂.1, b₂.2}
    -- TODO Make this more elegant
    b₁ ≠ b₂ -> b₁.1 ≠ b₂.1 ∧ b₁.1 ≠ b₂.2 ∧ b₁.2 ≠ b₂.1 ∧ b₁.2 ≠ b₂.2

  --union : ⋃ b ∈ edges, {b.1, b.2} = Set.univ := by decide
  union : ∀ i ∈ n, ∃ b ∈ edges, (i = b.1 ∨ i = b.2)

-- The following are attempts at examples
def ex0 : Fin 4 := 0
def ex1 : Fin 4 := 1
def ex2 : Fin 4 := 2
def ex3 : Fin 4 := 3

#eval (Finset.univ : Finset (Fin 4))
def pm_ex : PerfectMatching (Finset.univ : Finset (Fin 4)) :=
  ⟨{(ex0,ex1), (ex2,ex3)},
      by decide,by decide, by decide⟩

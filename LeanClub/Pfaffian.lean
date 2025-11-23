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

-- The alternatingness of a matrix.
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

def pm_ex2 : PerfectMatching (Fin 8) :=
  ⟨{(0,5), (1,3), (2,4), (6,7)},
      by decide, by simp, by decide⟩

/- "by decide" exceeds maximum recursion depth! -/

#eval pm_ex.edges

open scoped BigOperators

open Finset

-- 1b) If a perfect matching on S exists, then |S| is even.

def set {α} [Fintype α] [DecidableEq α] (b : α × α) : Finset α :=
  {b.1, b.2}

lemma block_card_two
    (M : PerfectMatching α) {b : α × α} (hb : b ∈ M.edges) :
    (set b).card = 2 := by
    have hne : b.1 ≠ b.2 := ne_of_lt (M.ordered b hb)
    simp [_root_.set, hne]

lemma blocks_cover (M : PerfectMatching α) :
    (M.edges.biUnion set : Finset α) = Finset.univ := by
  ext i; constructor
  · intro _; exact Finset.mem_univ _
  · intro _
    rcases M.union i with ⟨b, hb, hi⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨b, hb, ?_⟩
    rcases hi with rfl | rfl <;> simp [_root_.set]

lemma card_eq_sum_block_card (M : PerfectMatching α) :
    Fintype.card α = ∑ b ∈ M.edges, (set b).card := by
  -- cardinality of the union of blocks as a sum
  calc
    Fintype.card α
        = (Finset.univ : Finset α).card := (Finset.card_univ (α := α)).symm
    _ = (M.edges.biUnion set : Finset α).card := by
          simp [blocks_cover M]
    _ = ∑ b ∈ M.edges, (set b).card := Finset.card_biUnion M.disjoint

theorem PerfectMatching.card_eq_twice_card_edges (M : PerfectMatching α) :
  Fintype.card α = 2 * M.edges.card :=
  calc Fintype.card α
    _ = ∑ b ∈ M.edges, (set b).card := card_eq_sum_block_card M
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

-- In a perfect matching, each element of α lies in EXACTLY
-- one block.
theorem PerfectMatching.unique_block (M : PerfectMatching α) :
  ∀ (i : α), ∃! b ∈ M.edges, i ∈ set b := by
    intro i
    obtain ⟨b, hbedge, hbi⟩ := M.union i
    use b
    simp_rw [_root_.set]
    constructor
    · simp
      exact ⟨hbedge, hbi⟩
    intro y ⟨hyedge, hyi⟩
    nth_rw 2 [← mem_singleton] at hbi
    have hb : i ∈ ({b.1, b.2} : Finset α) := mem_insert.mpr hbi
    have hne : (({b.1, b.2} : Finset α) ∩ ({y.1, y.2} : Finset α) : Finset α).Nonempty := by
      use i
      rw [mem_inter]
      exact ⟨hb, hyi⟩
    rw [← not_disjoint_iff_nonempty_inter] at hne
    by_contra hneq
    change (y ≠ b) at hneq
    symm at hneq
    have hdj : Disjoint {b.1, b.2} {y.1, y.2} := M.disjoint b hbedge y hyedge hneq
    contradiction

-- The edge (block) of M containing a given element
def PerfectMatching.block (M : PerfectMatching α) : α → α × α :=
  fun i => Finset.choose (fun (b : α × α) => (i ∈ set b))
                         (M.edges : Finset (α × α)) (PerfectMatching.unique_block M i)

#eval PerfectMatching.block pm_ex 0

#eval PerfectMatching.block pm_ex 1

#eval PerfectMatching.block pm_ex 2

#eval PerfectMatching.block pm_ex 3

#eval PerfectMatching.block pm_ex2 1

#eval PerfectMatching.block pm_ex2 3

theorem PerfectMatching.block_spec (M : PerfectMatching α) (i : α) :
    (PerfectMatching.block M i ∈ M.edges) ∧ (i ∈ set (PerfectMatching.block M i)) :=
  choose_spec _ _ _

theorem PerfectMatching.block_uni (M : PerfectMatching α) (i : α) (b : α × α)
    (hbe : b ∈ M.edges) (hib : i ∈ set b)
    : b = PerfectMatching.block M i := by
  have h2 : (b ∈ M.edges) ∧ (i ∈ set b) := ⟨hbe, hib⟩
  apply (PerfectMatching.unique_block M i).unique
  · exact h2
  · exact (PerfectMatching.block_spec M i)

def first_or_second_if_not (pair : α × α) (i : α) := if pair.1 = i then pair.2 else pair.1

#eval first_or_second_if_not (0, 2) 3

#eval first_or_second_if_not (0, 2) 2

#eval first_or_second_if_not (0, 2) 0

-- The partner of a given element of α in M:
def PerfectMatching.partner (M : PerfectMatching α) : α → α :=
  fun i => first_or_second_if_not (M.block i) i

#eval pm_ex2.partner 0

#eval pm_ex2.partner 5

#eval pm_ex2.partner 1

#eval pm_ex2.partner 2

theorem PerfectMatching.partner_block (M : PerfectMatching α) (i : α) :
    set (M.block i) = {i, M.partner i} := by
  rcases hiab : (M.block i) with ⟨a, b⟩
  have hwut : (M.block i ∈ M.edges) ∧ (i ∈ _root_.set (M.block i)) := M.block_spec i
  rw [hiab] at hwut
  simp [_root_.set] at hwut ⊢
  simp [partner]
  rw [hiab]
  simp [first_or_second_if_not]
  cases (Decidable.eq_or_ne a i)
  case inl hia =>
    simp [hia]
  case inr hina =>
    simp [hina]
    have hina2 : i ≠ a := Ne.symm hina
    obtain ⟨-, hw2⟩ := hwut
    have : i = b := Or.resolve_left hw2 hina2
    rw [this]
    exact pair_comm a b

theorem PerfectMatching.partner_block_aristotle (M : PerfectMatching α) (i : α) :
    set (M.block i) = {i, M.partner i} := by
  -- Aristotle's proof, clarified:
  let ⟨a, b, hab, ⟨hi1, hi2⟩⟩ :
      ∃ a b : α, a < b
                ∧ i ∈ ({a, b} : Finset α)
                ∧ M.block i = (a, b) := by
    have := M.block_spec i;
    exact ⟨ (M.block i).1, (M.block i).2, M.ordered (M.block i) this.1, this.2, rfl ⟩;
  unfold PerfectMatching.partner
  unfold first_or_second_if_not
  simp_all
  cases (Decidable.eq_or_ne a i)
  case inl hia =>
    simp_rw [hia, _root_.set]
    rfl
  case inr hia =>
    simp_rw [hia, _root_.set]
    simp
    rw [Finset.pair_comm]
    congr 1
    symm
    exact Or.resolve_left hi1 (Ne.symm hia)

lemma eq_of_two_sets_equal (a b c : α) (h : ({a, b} : Finset α) = {a, c}) : b = c := by
  have : b ∈ ({a, c} : Finset α) := by
    rw [← h]; apply mem_insert_of_mem
    rw [mem_singleton]
  have hb : b = a ∨ b = c
    := by rw [Finset.mem_insert, mem_singleton] at this; apply this
  have : c ∈ ({a, b} : Finset α) := by
    rw [h]; apply mem_insert_of_mem
    rw [mem_singleton]
  have hc : c = a ∨ c = b
    := by rw [Finset.mem_insert, mem_singleton] at this; apply this
  cases hb
  case inl hb =>
    cases hc
    case inl hc =>
      rw [hb, ← hc]
    case inr hc =>
      symm; exact hc
  case inr hb =>
    exact hb

theorem PerfectMatching.partner_same_block (M : PerfectMatching α) (i : α) :
    M.block i = M.block (M.partner i) := by
  apply PerfectMatching.block_uni
  · show M.block i ∈ M.edges
    exact (PerfectMatching.block_spec M i).1
  show M.partner i ∈ _root_.set (M.block i)
  rw [M.partner_block i]
  exact mem_insert_of_mem (mem_singleton.mpr rfl)

theorem PerfectMatching.partner_invol (M : PerfectMatching α) : M.partner ∘ M.partner = id := by
  ext i; simp
  apply eq_of_two_sets_equal (M.partner i)
  rw [← PerfectMatching.partner_block]
  rw [pair_comm (M.partner i) i]
  rw [← PerfectMatching.partner_block]
  congr 1
  symm
  exact M.partner_same_block i

/-
theorem PerfectMatching.partner_invol_aristotle (M : PerfectMatching α) : M.partner ∘ M.partner = id := by
  -- Proof generated by Aristotle:
  ext i
  -- By definition of partner, we know that the block containing i is {i, partner i}.
  have h_block : set (M.block i) = {i, M.partner i} := PerfectMatching.partner_block M i;
  -- By definition of partner, we know that the block containing partner i is {partner i, partner (partner i)}.
  have h_block_partner : set (M.block (M.partner i)) = {M.partner i, M.partner (M.partner i)} := by
    -- By definition of partner, we know that the block containing partner i is {partner i, partner (partner i)} by the same reasoning as for i.
    apply PerfectMatching.partner_block;
  -- Since these blocks are disjoint and cover all elements, the only way for both to be true is if partner (partner i) equals i.
  have h_unique : M.block i = M.block (M.partner i) := by
    have := M.unique_block ( M.partner i );
    convert this.unique _ _ <;>
    simp_all only [mem_insert, mem_singleton, or_true, and_true]
    · exact M.block_spec i |>.1;
    · simp
      exact M.block_spec _ |>.1;
  simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
  grind -ring
-/

def open_interval (p : α × α) := {x : α // p.1 < x ∧ x < p.2}

#check open_interval (0, 3)

example : (3 : ℕ) ∈ open_interval ((1 : ℕ), (4 : ℕ)) := by

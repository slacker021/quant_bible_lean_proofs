import Mathlib.Data.Set.Basic

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 3 - Cartesian Products and Relations
# Auditor Target: 'Theorem: Fundamental Contract of Ordered Coordinates'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

-- 2. DOMAIN SPECIFICATIONS
variable {α : Type*}

/-- The Kuratowski definition of an ordered pair: (x, y) := {{x}, {x, y}} -/
def kuratowskiPair (x y : α) : Set (Set α) :=
  {{x}, {x, y}}

-- 3. THE TARGET THEOREMS
/-- Reverse Direction (Sufficiency): Coordinate assignments uniquely reconstruct the pair. -/
theorem kuratowski_pair_eq_of_eq {x y u v : α} (hx : x = u) (hy : y = v) :
    kuratowskiPair x y = kuratowskiPair u v := by
  rw [hx, hy]

/-- Forward Direction (Necessity): Pair identity forces coordinate identity.
    Faithfully formalizes the two exhaustive cases of the Kuratowski contract:
    Case 1: x = y (singleton collapse)
    Case 2: x ≠ y (two distinct member sets) -/
theorem eq_of_kuratowski_pair_eq {x y u v : α}
    (h : kuratowskiPair x y = kuratowskiPair u v) :
    x = u ∧ y = v := by
  have hu_mem : {u} ∈ kuratowskiPair x y := by
    rw [h]
    exact Or.inl rfl
  have hx_u : x = u := by
    rcases hu_mem with h1 | h2
    · have : u ∈ ({x} : Set α) := h1 ▸ rfl
      exact this.symm
    · have : x ∈ ({u} : Set α) := h2 ▸ Or.inl rfl
      exact this
  subst hx_u
  have h_pair : kuratowskiPair x y = kuratowskiPair x v := h
  by_cases hxy : x = y
  · -- Case 1: Assume x = y
    have h_xv : ({x, v} : Set α) ∈ kuratowskiPair x y := by
      rw [h_pair]
      exact Or.inr rfl
    have hv_eq_x : v = x := by
      rcases h_xv with h1 | h2
      · have : v ∈ ({x} : Set α) := h1 ▸ Or.inr rfl
        exact this
      · have : v ∈ ({x, y} : Set α) := h2 ▸ Or.inr rfl
        rcases this with rfl | hv
        · rfl
        · rw [hv, hxy]
    subst hxy hv_eq_x
    exact ⟨rfl, rfl⟩
  · -- Case 2: Assume x ≠ y
    have h_xy : ({x, y} : Set α) ∈ kuratowskiPair x v := by
      rw [← h_pair]
      exact Or.inr rfl
    have h_eq : ({x, y} : Set α) = {x, v} := by
      rcases h_xy with h1 | h2
      · have hy_x : y = x := by
          have : y ∈ ({x} : Set α) := h1 ▸ Or.inr rfl
          exact this
        exact False.elim (hxy hy_x.symm)
      · exact h2
    have hy_v : y = v := by
      have : y ∈ ({x, v} : Set α) := h_eq ▸ Or.inr rfl
      rcases this with rfl | hy
      · exact False.elim (hxy rfl)
      · exact hy
    exact ⟨rfl, hy_v⟩

/-- Full Logical Equivalence: The Fundamental Contract of Ordered Coordinates. -/
theorem kuratowski_pair_iff (x y u v : α) :
    kuratowskiPair x y = kuratowskiPair u v ↔ x = u ∧ y = v :=
  ⟨eq_of_kuratowski_pair_eq, fun ⟨hx, hy⟩ => kuratowski_pair_eq_of_eq hx hy⟩

/-- Type-Theoretic Identity (Canonical Product Projections):
    Bridging equivalence on Lean's native Prod type. -/
theorem prod_eq_iff (x u : α) (y v : α) :
    (x, y) = (u, v) ↔ x = u ∧ y = v :=
  ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩,
   by rintro ⟨rfl, rfl⟩; rfl⟩

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies non-vacuity over an inhabited domain with distinct coordinates. -/
lemma kuratowski_pair_witness :
    ∃ (α : Type) (x y u v : α),
      x ≠ y ∧ (kuratowskiPair x y = kuratowskiPair u v ↔ x = u ∧ y = v) := by
  use ℕ, 1, 2, 1, 2
  refine ⟨by decide, kuratowski_pair_iff 1 2 1 2⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms kuratowski_pair_eq_of_eq
#print axioms eq_of_kuratowski_pair_eq
#print axioms kuratowski_pair_iff
#print axioms prod_eq_iff
#print axioms kuratowski_pair_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

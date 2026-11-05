import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 3 - Cartesian Products and Relations
# Auditor Target: 'Theorem: Empty Product Identity'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

-- 2. DOMAIN SPECIFICATIONS
variable {α β : Type*} (X : Set α) (Y : Set β)

-- 3. THE TARGET THEOREMS
/-- Forward Direction: An empty factor collapses the Cartesian product.
    (X = ∅) ∨ (Y = ∅) → X ×ˢ Y = ∅ -/
theorem empty_prod_forward (h : X = ∅ ∨ Y = ∅) : X ×ˢ Y = ∅ := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨hx, hy⟩
    cases h with
    | inl hX =>
      rw [hX] at hx
      exact False.elim hx
    | inr hY =>
      rw [hY] at hy
      exact False.elim hy
  · intro h_empty
    exact False.elim h_empty

/-- Reverse Direction (Contrapositive Characterization): An empty product forces
    emptiness of at least one coordinate space.
    X ×ˢ Y = ∅ → (X = ∅) ∨ (Y = ∅) -/
theorem empty_prod_reverse (h : X ×ˢ Y = ∅) : X = ∅ ∨ Y = ∅ := by
  by_cases hX : X = ∅
  · exact Or.inl hX
  · right
    by_contra hY
    have hX_ne : X.Nonempty := nonempty_iff_ne_empty.mpr hX
    have hY_ne : Y.Nonempty := nonempty_iff_ne_empty.mpr hY
    rcases hX_ne with ⟨x, hx⟩
    rcases hY_ne with ⟨y, hy⟩
    have h_in : (x, y) ∈ X ×ˢ Y := ⟨hx, hy⟩
    rw [h] at h_in
    exact False.elim h_in

/-- Full Logical Equivalence: The Empty Product Identity. -/
theorem empty_prod_iff : X ×ˢ Y = ∅ ↔ X = ∅ ∨ Y = ∅ :=
  ⟨empty_prod_reverse X Y, empty_prod_forward X Y⟩

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Demonstrates that the empty product identity holds
    with a concrete empty factor and non-empty factor. -/
lemma empty_prod_witness :
    ∃ (α β : Type) (X : Set α) (Y : Set β),
      X = ∅ ∧ Y.Nonempty ∧ (X ×ˢ Y = ∅ ↔ X = ∅ ∨ Y = ∅) := by
  use ℕ, ℕ, ∅, Set.univ
  refine ⟨rfl, ⟨0, Set.mem_univ 0⟩, empty_prod_iff ∅ Set.univ⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms empty_prod_forward
#print axioms empty_prod_reverse
#print axioms empty_prod_iff
#print axioms empty_prod_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

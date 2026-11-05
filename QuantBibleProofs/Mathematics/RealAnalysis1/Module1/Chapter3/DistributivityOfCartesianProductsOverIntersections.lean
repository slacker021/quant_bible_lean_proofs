import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 3 - Cartesian Products and Relations
# Auditor Target: 'Theorem: Distributivity of Cartesian Products over Intersections'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

-- 2. DOMAIN SPECIFICATIONS
variable {α β : Type*} (X X' : Set α) (Y Y' : Set β)

-- 3. THE TARGET THEOREMS
/-- Forward Inclusion: (X ×ˢ Y) ∩ (X' ×ˢ Y') ⊆ (X ∩ X') ×ˢ (Y ∩ Y') -/
theorem prod_inter_distrib_subset_forward :
    (X ×ˢ Y) ∩ (X' ×ˢ Y') ⊆ (X ∩ X') ×ˢ (Y ∩ Y') := by
  rintro ⟨a, b⟩ ⟨⟨hX, hY⟩, ⟨hX', hY'⟩⟩
  exact ⟨⟨hX, hX'⟩, ⟨hY, hY'⟩⟩

/-- Reverse Inclusion: (X ∩ X') ×ˢ (Y ∩ Y') ⊆ (X ×ˢ Y) ∩ (X' ×ˢ Y') -/
theorem prod_inter_distrib_subset_reverse :
    (X ∩ X') ×ˢ (Y ∩ Y') ⊆ (X ×ˢ Y) ∩ (X' ×ˢ Y') := by
  rintro ⟨a, b⟩ ⟨⟨hX, hX'⟩, ⟨hY, hY'⟩⟩
  exact ⟨⟨hX, hY⟩, ⟨hX', hY'⟩⟩

/-- Extensional Set Identity: (X ×ˢ Y) ∩ (X' ×ˢ Y') = (X ∩ X') ×ˢ (Y ∩ Y') -/
theorem prod_inter_distrib_eq :
    (X ×ˢ Y) ∩ (X' ×ˢ Y') = (X ∩ X') ×ˢ (Y ∩ Y') :=
  Subset.antisymm (prod_inter_distrib_subset_forward X X' Y Y')
                  (prod_inter_distrib_subset_reverse X X' Y Y')

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies non-vacuity with non-empty intersections. -/
lemma prod_inter_distrib_witness :
    ∃ (α β : Type) (X X' : Set α) (Y Y' : Set β),
      (X ∩ X').Nonempty ∧ (Y ∩ Y').Nonempty ∧
      ((X ×ˢ Y) ∩ (X' ×ˢ Y') = (X ∩ X') ×ˢ (Y ∩ Y')) := by
  use ℕ, ℕ, {1, 2}, {2, 3}, {4, 5}, {5, 6}
  refine ⟨⟨2, ⟨Or.inr rfl, Or.inl rfl⟩⟩,
          ⟨5, ⟨Or.inr rfl, Or.inl rfl⟩⟩,
          prod_inter_distrib_eq {1, 2} {2, 3} {4, 5} {5, 6}⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms prod_inter_distrib_subset_forward
#print axioms prod_inter_distrib_subset_reverse
#print axioms prod_inter_distrib_eq
#print axioms prod_inter_distrib_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

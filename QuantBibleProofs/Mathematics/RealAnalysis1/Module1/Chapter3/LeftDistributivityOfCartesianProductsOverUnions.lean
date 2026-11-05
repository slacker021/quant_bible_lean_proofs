import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 3 - Cartesian Products and Relations
# Auditor Target: 'Theorem: Left-Distributivity of Cartesian Products over Unions'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

-- 2. DOMAIN SPECIFICATIONS
variable {α β : Type*} (X Z : Set α) (Y : Set β)

-- 3. THE TARGET THEOREMS
/-- Forward Inclusion: (X ×ˢ Y) ∪ (Z ×ˢ Y) ⊆ (X ∪ Z) ×ˢ Y -/
theorem prod_union_distrib_subset_forward :
    (X ×ˢ Y) ∪ (Z ×ˢ Y) ⊆ (X ∪ Z) ×ˢ Y := by
  rintro ⟨a, b⟩ (⟨hX, hY⟩ | ⟨hZ, hY⟩)
  · exact ⟨Or.inl hX, hY⟩
  · exact ⟨Or.inr hZ, hY⟩

/-- Reverse Inclusion: (X ∪ Z) ×ˢ Y ⊆ (X ×ˢ Y) ∪ (Z ×ˢ Y) -/
theorem prod_union_distrib_subset_reverse :
    (X ∪ Z) ×ˢ Y ⊆ (X ×ˢ Y) ∪ (Z ×ˢ Y) := by
  rintro ⟨a, b⟩ ⟨(hX | hZ), hY⟩
  · exact Or.inl ⟨hX, hY⟩
  · exact Or.inr ⟨hZ, hY⟩

/-- Extensional Set Identity: (X ×ˢ Y) ∪ (Z ×ˢ Y) = (X ∪ Z) ×ˢ Y -/
theorem prod_union_distrib_eq :
    (X ×ˢ Y) ∪ (Z ×ˢ Y) = (X ∪ Z) ×ˢ Y :=
  Subset.antisymm (prod_union_distrib_subset_forward X Z Y)
                  (prod_union_distrib_subset_reverse X Z Y)

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies non-vacuity on non-empty disjoint sets. -/
lemma prod_union_distrib_witness :
    ∃ (α β : Type) (X Z : Set α) (Y : Set β),
      X.Nonempty ∧ Z.Nonempty ∧ Y.Nonempty ∧
      ((X ×ˢ Y) ∪ (Z ×ˢ Y) = (X ∪ Z) ×ˢ Y) := by
  use ℕ, ℕ, {1}, {2}, {3}
  refine ⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, prod_union_distrib_eq {1} {2} {3}⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms prod_union_distrib_subset_forward
#print axioms prod_union_distrib_subset_reverse
#print axioms prod_union_distrib_eq
#print axioms prod_union_distrib_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

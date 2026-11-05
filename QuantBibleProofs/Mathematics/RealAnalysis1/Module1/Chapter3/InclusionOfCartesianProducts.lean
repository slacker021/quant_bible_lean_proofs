import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 3 - Cartesian Products and Relations
# Auditor Target: 'Theorem: Inclusion of Cartesian Products'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

-- 2. DOMAIN SPECIFICATIONS
variable {α β : Type*} (A X : Set α) (B Y : Set β)

-- 3. THE TARGET THEOREMS
/-- Forward Direction: Factor-wise containment implies product containment.
    (A ⊆ X) ∧ (B ⊆ Y) → A ×ˢ B ⊆ X ×ˢ Y -/
theorem prod_subset_prod_forward (hA : A ⊆ X) (hB : B ⊆ Y) :
    A ×ˢ B ⊆ X ×ˢ Y := by
  intro ⟨a, b⟩ ⟨ha, hb⟩
  exact ⟨hA ha, hB hb⟩

/-- Reverse Direction: Product containment implies factor-wise containment
    under non-emptiness of the factors.
    A ×ˢ B ⊆ X ×ˢ Y → (A ⊆ X) ∧ (B ⊆ Y) -/
theorem prod_subset_prod_reverse (h : A ×ˢ B ⊆ X ×ˢ Y)
    (ha_ne : A.Nonempty) (hb_ne : B.Nonempty) :
    A ⊆ X ∧ B ⊆ Y := by
  rcases ha_ne with ⟨a₀, ha₀⟩
  rcases hb_ne with ⟨b₀, hb₀⟩
  constructor
  · intro a ha
    have hab : (a, b₀) ∈ A ×ˢ B := ⟨ha, hb₀⟩
    exact (h hab).1
  · intro b hb
    have hab : (a₀, b) ∈ A ×ˢ B := ⟨ha₀, hb⟩
    exact (h hab).2

/-- Full Logical Equivalence under Non-emptiness: Inclusion of Cartesian Products. -/
theorem prod_subset_prod_iff (ha_ne : A.Nonempty) (hb_ne : B.Nonempty) :
    A ×ˢ B ⊆ X ×ˢ Y ↔ (A ⊆ X ∧ B ⊆ Y) :=
  ⟨fun h => prod_subset_prod_reverse A X B Y h ha_ne hb_ne,
   fun ⟨hA, hB⟩ => prod_subset_prod_forward A X B Y hA hB⟩

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies the equivalence on non-empty, nested subsets. -/
lemma prod_subset_prod_witness :
    ∃ (α β : Type) (A X : Set α) (B Y : Set β),
      A.Nonempty ∧ B.Nonempty ∧
      (A ×ˢ B ⊆ X ×ˢ Y ↔ (A ⊆ X ∧ B ⊆ Y)) := by
  use ℕ, ℕ, {1}, {1, 2}, {3}, {3, 4}
  refine ⟨⟨1, rfl⟩, ⟨3, rfl⟩, prod_subset_prod_iff {1} {1, 2} {3} {3, 4} ⟨1, rfl⟩ ⟨3, rfl⟩⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms prod_subset_prod_forward
#print axioms prod_subset_prod_reverse
#print axioms prod_subset_prod_iff
#print axioms prod_subset_prod_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter3

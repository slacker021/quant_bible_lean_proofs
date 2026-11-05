import Mathlib.Data.Set.Basic

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 2 - Naive Set Theory
# Auditor Target: 'Proposition: De Morgan's Laws of Set Complements'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter2

-- 2. DOMAIN SPECIFICATIONS
variable {α : Type*}

-- 3. THE TARGET THEOREMS
/-- Proposition 1: De Morgan's Law for Union Complement.
    (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ -/
theorem compl_union (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  · intro h
    constructor
    · intro hA
      exact h (Or.inl hA)
    · intro hB
      exact h (Or.inr hB)
  · rintro ⟨hA, hB⟩ (hAx | hBx)
    · exact hA hAx
    · exact hB hBx

/-- Proposition 2: De Morgan's Law for Intersection Complement.
    (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ -/
theorem compl_inter (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  constructor
  · intro h
    by_cases hA : x ∈ A
    · right
      intro hB
      exact h ⟨hA, hB⟩
    · left
      exact hA
  · rintro (hA | hB) ⟨hAx, hBx⟩
    · exact hA hAx
    · exact hB hBx

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies De Morgan's laws hold over an inhabited domain
    with two non-empty sets. -/
lemma de_morgan_witness :
    ∃ (α : Type) (A B : Set α),
      A.Nonempty ∧ B.Nonempty ∧
      ((A ∪ B)ᶜ = Aᶜ ∩ Bᶜ) ∧
      ((A ∩ B)ᶜ = Aᶜ ∪ Bᶜ) := by
  use ℕ, {1}, {2}
  refine ⟨⟨1, rfl⟩, ⟨2, rfl⟩, compl_union _ _, compl_inter _ _⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms compl_union
#print axioms compl_inter
#print axioms de_morgan_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter2

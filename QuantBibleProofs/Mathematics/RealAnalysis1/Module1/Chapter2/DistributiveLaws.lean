import Mathlib.Data.Set.Basic

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 2 - Naive Set Theory
# Auditor Target: Proposition: Distributive Laws of Intersection and Union'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter2

-- 2. DOMAIN SPECIFICATIONS
variable {α : Type*}

-- 3. THE TARGET THEOREMS
/-- Proposition 1: Left-distributivity of intersection over union.
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) -/
theorem inter_union_distrib (A B C : Set α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · rintro ⟨hA, (hB | hC)⟩
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hC⟩
  · rintro (⟨hA, hB⟩ | ⟨hA, hC⟩)
    · exact ⟨hA, Or.inl hB⟩
    · exact ⟨hA, Or.inr hC⟩

/-- Proposition 2: Left-distributivity of union over intersection.
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) -/
theorem union_inter_distrib (A B C : Set α) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · rintro (hA | ⟨hB, hC⟩)
    · exact ⟨Or.inl hA, Or.inl hA⟩
    · exact ⟨Or.inr hB, Or.inr hC⟩
  · rintro ⟨(hA₁ | hB), (hA₂ | hC)⟩
    · exact Or.inl hA₁
    · exact Or.inl hA₁
    · exact Or.inl hA₂
    · exact Or.inr ⟨hB, hC⟩

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Demonstrates that the distributive identities hold over
    an inhabited domain with three non-empty, mutually distinct singleton sets.
    Discharged cleanly using definitionally inhabited singletons without ambiguous disjunctions. -/
lemma distrib_laws_witness :
    ∃ (α : Type) (A B C : Set α),
      A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
      (A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)) ∧
      (A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)) := by
  use ℕ, {1}, {2}, {3}
  refine ⟨⟨1, rfl⟩,
          ⟨2, rfl⟩,
          ⟨3, rfl⟩,
          inter_union_distrib _ _ _,
          union_inter_distrib _ _ _⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms inter_union_distrib
#print axioms union_inter_distrib
#print axioms distrib_laws_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter2

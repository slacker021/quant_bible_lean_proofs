import Mathlib.Data.Set.Basic

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 2 - Naive Set Theory
# Auditor Target: 'Lemma: Fundamental Properties of Complementation'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter2

-- 2. DOMAIN SPECIFICATIONS
variable {α : Type*}

-- 3. THE TARGET THEOREMS
/-- Lemma 1: Joint containment characterization of the union.
    A subset A and a subset B are both contained in S if and only if
    their union A ∪ B is contained in S. -/
theorem union_subset_iff (A B S : Set α) :
    (A ⊆ S ∧ B ⊆ S) ↔ A ∪ B ⊆ S := by
  constructor
  · rintro ⟨hA, hB⟩ x (hAx | hBx)
    · exact hA hAx
    · exact hB hBx
  · intro h
    constructor
    · intro x hx
      exact h (Or.inl hx)
    · intro x hx
      exact h (Or.inr hx)

/-- Lemma 2: Order-reversing contraposition of set inclusion.
    A is a subset of B if and only if the complement of B is a subset
    of the complement of A. -/
theorem compl_subset_compl_iff (A B : Set α) :
    A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  constructor
  · intro h x hBc ha
    exact hBc (h ha)
  · intro h x ha
    by_contra hb
    exact (h hb) ha

/-- Lemma 3: Involution of set complementation (Double Complement).
    The complement of the complement of A is identical to A. -/
theorem compl_compl_eq (A : Set α) :
    (Aᶜ)ᶜ = A := by
  ext x
  constructor
  · intro hx
    by_contra ha
    exact hx ha
  · intro ha hAc
    exact hAc ha

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that all three complementation properties hold
    simultaneously over an inhabited universe with non-empty nested sets. -/
lemma elementary_set_compl_witness :
    ∃ (α : Type) (A B S : Set α),
      A.Nonempty ∧ B.Nonempty ∧ S.Nonempty ∧ A ⊆ B ∧ B ⊆ S ∧
      ((A ⊆ S ∧ B ⊆ S) ↔ A ∪ B ⊆ S) ∧
      (A ⊆ B ↔ Bᶜ ⊆ Aᶜ) ∧
      (Aᶜ)ᶜ = A := by
  use ℕ, {1}, {1, 2}, Set.univ
  refine ⟨⟨1, rfl⟩, ⟨1, Or.inl rfl⟩, ⟨0, Set.mem_univ 0⟩, ?_, ?_,
          union_subset_iff _ _ _, compl_subset_compl_iff _ _, compl_compl_eq _⟩
  · intro x hx
    exact Or.inl hx
  · intro x _
    exact Set.mem_univ x

-- 5. KERNEL AUDIT INSPECTION
#print axioms union_subset_iff
#print axioms compl_subset_compl_iff
#print axioms compl_compl_eq
#print axioms elementary_set_compl_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter2

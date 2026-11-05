import Mathlib.Data.Set.Basic

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 4 - Functions and Cardinality
# Auditor Target: 'Proposition: Preimages of Differences and Complements'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

-- 2. DOMAIN SPECIFICATIONS
variable {X Y : Type*} (f : X → Y) (A' B' : Set Y)

-- 3. THE TARGET THEOREMS

/-- Proposition 1: Preimage of Set Difference.
    The preimage operator distributes over relative set differences:
    f⁻¹(A' \ B') = f⁻¹(A') \ f⁻¹(B'). -/
theorem preimage_diff_eq : f ⁻¹' (A' \ B') = (f ⁻¹' A') \ (f ⁻¹' B') := by
  ext x
  calc
    x ∈ f ⁻¹' (A' \ B') ↔ f x ∈ A' \ B'                     := Iff.rfl
    _                   ↔ (f x ∈ A') ∧ ¬(f x ∈ B')          := Iff.rfl
    _                   ↔ (x ∈ f ⁻¹' A') ∧ ¬(x ∈ f ⁻¹' B')   := Iff.rfl
    _                   ↔ x ∈ (f ⁻¹' A') \ (f ⁻¹' B')       := Iff.rfl

/-- Proposition 2 (Method 2: Pointwise Verification): Preimage of Absolute Complement.
    The preimage of the complement is the complement of the preimage. -/
theorem preimage_compl_eq : f ⁻¹' (A'ᶜ) = (f ⁻¹' A')ᶜ := by
  ext x
  calc
    x ∈ f ⁻¹' (A'ᶜ) ↔ f x ∈ A'ᶜ          := Iff.rfl
    _               ↔ ¬(f x ∈ A')        := Iff.rfl
    _               ↔ ¬(x ∈ f ⁻¹' A')    := Iff.rfl
    _               ↔ x ∈ (f ⁻¹' A')ᶜ    := Iff.rfl

/-- Proposition 2 (Method 1: Algebraic Reduction): Preimage of Absolute Complement.
    Derives complement preservation algebraically from set difference and f⁻¹(Y) = X. -/
theorem preimage_compl_eq_algebraic : f ⁻¹' (A'ᶜ) = (f ⁻¹' A')ᶜ := by
  calc
    f ⁻¹' (A'ᶜ) = f ⁻¹' (univ \ A')            := by rw [compl_eq_univ_diff]
    _           = (f ⁻¹' univ) \ (f ⁻¹' A')     := preimage_diff_eq f univ A'
    _           = univ \ (f ⁻¹' A')             := by rw [preimage_univ]
    _           = (f ⁻¹' A')ᶜ                   := by rw [← compl_eq_univ_diff]

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that difference and complementation preimages admit
    concrete non-empty instances under the identity mapping. -/
lemma preimages_diff_compl_witness :
    ∃ (X Y : Type) (f : X → Y) (A' B' : Set Y),
      A'.Nonempty ∧ B'.Nonempty ∧
      (f ⁻¹' (A' \ B') = (f ⁻¹' A') \ (f ⁻¹' B')) ∧
      (f ⁻¹' (A'ᶜ) = (f ⁻¹' A')ᶜ) := by
  use ℕ, ℕ, id, {0, 1}, {1}
  refine ⟨⟨0, Or.inl rfl⟩, ⟨1, rfl⟩, preimage_diff_eq id {0, 1} {1}, preimage_compl_eq id {0, 1}⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms preimage_diff_eq
#print axioms preimage_compl_eq
#print axioms preimage_compl_eq_algebraic
#print axioms preimages_diff_compl_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

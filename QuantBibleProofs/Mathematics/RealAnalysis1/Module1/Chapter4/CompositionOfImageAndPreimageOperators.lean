import Mathlib.Data.Set.Basic

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 4 - Functions and Cardinality
# Auditor Target: 'Proposition: Composition of Image and Preimage Operators'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

-- 2. DOMAIN SPECIFICATIONS
variable {X Y : Type*} (f : X → Y) (A : Set X) (B' : Set Y)

-- 3. THE TARGET THEOREMS
/-- Proposition 1: Expansion Bound.
    For any mapping f : X → Y and subset A ⊆ X, A ⊆ f⁻¹(f(A)). -/
theorem subset_preimage_image : A ⊆ f ⁻¹' (f '' A) := by
  intro x hxA
  -- Show that x ∈ f ⁻¹' (f '' A), which requires f(x) ∈ f '' A:
  exact ⟨x, hxA, rfl⟩

/-- Proposition 2: Contraction Bound.
    For any mapping f : X → Y and subset B' ⊆ Y, f(f⁻¹(B')) ⊆ B'. -/
theorem image_preimage_subset : f '' (f ⁻¹' B') ⊆ B' := by
  intro y hy
  -- y ∈ f '' (f ⁻¹' B') implies ∃ x ∈ f ⁻¹' B' with f(x) = y:
  rcases hy with ⟨x, hxPre, hfxy⟩
  -- Since x ∈ f ⁻¹' B', f(x) ∈ B':
  have hfxB : f x ∈ B' := hxPre
  -- Since y = f(x), y ∈ B':
  subst hfxy
  exact hfxB

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that both bounds hold simultaneously on non-empty,
    non-degenerate sets. -/
lemma composition_image_preimage_witness :
    ∃ (X Y : Type) (f : X → Y) (A : Set X) (B' : Set Y),
      A.Nonempty ∧ B'.Nonempty ∧
      (A ⊆ f ⁻¹' (f '' A)) ∧ (f '' (f ⁻¹' B') ⊆ B') := by
  use ℕ, ℕ, id, {0}, {1}
  refine ⟨⟨0, rfl⟩, ⟨1, rfl⟩, subset_preimage_image id {0}, image_preimage_subset id {1}⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms subset_preimage_image
#print axioms image_preimage_subset
#print axioms composition_image_preimage_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

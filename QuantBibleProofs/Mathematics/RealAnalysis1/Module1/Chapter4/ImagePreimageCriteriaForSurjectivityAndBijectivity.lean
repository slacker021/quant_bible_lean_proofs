import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 4 - Functions and Cardinality
# Auditor Target: 'Proposition: Image-Preimage Criteria for Surjectivity and Bijectivity'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set Function

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

-- 2. DOMAIN SPECIFICATIONS
variable {X Y : Type*} (f : X → Y)

-- 3. THE TARGET THEOREMS

/-- Proposition 1: Surjectivity Criterion via Preimage Contraction Equality.
    A mapping f : X → Y is surjective if and only if for every subset B' ⊆ Y,
    f(f⁻¹(B')) = B'. -/
theorem surjective_iff_image_preimage_eq :
    Surjective f ↔ ∀ B' : Set Y, f '' (f ⁻¹' B') = B' := by
  constructor
  · -- Forward direction: Surjective f ⟹ ∀ B', f(f⁻¹(B')) = B'
    intro hSurj B'
    apply Subset.antisymm
    · rintro y ⟨x, hxPre, rfl⟩
      exact hxPre
    · intro y hy
      rcases hSurj y with ⟨x, rfl⟩
      exact ⟨x, hy, rfl⟩
  · -- Reverse direction: (∀ B', f(f⁻¹(B')) = B') ⟹ Surjective f
    intro hEq y
    have hSingleton : f '' (f ⁻¹' {y}) = {y} := hEq {y}
    have hyMem : y ∈ {y} := mem_singleton y
    rw [← hSingleton] at hyMem
    rcases hyMem with ⟨x, _, hfxy⟩
    exact ⟨x, hfxy⟩

/-- Proposition 2: Bijectivity Criterion via Dual Operator Identities.
    A mapping f : X → Y is bijective if and only if both operator identities hold:
    (1) ∀ A ⊆ X, f⁻¹(f(A)) = A
    (2) ∀ B' ⊆ Y, f(f⁻¹(B')) = B' -/
theorem bijective_iff_preimage_image_and_image_preimage_eq :
    Bijective f ↔ (∀ A : Set X, f ⁻¹' (f '' A) = A) ∧ (∀ B' : Set Y, f '' (f ⁻¹' B') = B') := by
  constructor
  · -- Forward direction: Bijective ⟹ Dual Identities
    intro ⟨hInj, hSurj⟩
    constructor
    · intro A
      apply Subset.antisymm
      · intro x hx
        rcases hx with ⟨a, haA, hfa⟩
        have heq : a = x := hInj hfa
        rw [← heq]
        exact haA
      · intro x hxA
        exact ⟨x, hxA, rfl⟩
    · exact (surjective_iff_image_preimage_eq f).mp hSurj
  · -- Reverse direction: Dual Identities ⟹ Bijective
    intro ⟨hLeft, hRight⟩
    have hSurj : Surjective f := (surjective_iff_image_preimage_eq f).mpr hRight
    have hInj : Injective f := by
      intro x₁ x₂ hfx
      have hx2 : x₂ ∈ f ⁻¹' (f '' {x₁}) := by
        change f x₂ ∈ f '' {x₁}
        exact ⟨x₁, mem_singleton x₁, hfx⟩
      rw [hLeft {x₁}] at hx2
      have hx2_eq : x₂ = x₁ := mem_singleton_iff.mp hx2
      exact hx2_eq.symm
    exact ⟨hInj, hSurj⟩

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that both surjectivity and bijectivity criteria admit
    a concrete inhabited witness via the identity mapping on natural numbers. -/
lemma surjectivity_bijectivity_criteria_witness :
    ∃ (X Y : Type) (f : X → Y),
      Bijective f ∧
      (Surjective f ↔ ∀ B' : Set Y, f '' (f ⁻¹' B') = B') ∧
      ((∀ A : Set X, f ⁻¹' (f '' A) = A) ∧ (∀ B' : Set Y, f '' (f ⁻¹' B') = B')) := by
  use ℕ, ℕ, id
  have hBij : Bijective (id : ℕ → ℕ) := bijective_id
  have hSurj : Surjective (id : ℕ → ℕ) := surjective_id
  have hDual := (bijective_iff_preimage_image_and_image_preimage_eq (id : ℕ → ℕ)).mp hBij
  exact ⟨hBij, ⟨fun _ => hDual.2, fun _ => hSurj⟩, hDual⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms surjective_iff_image_preimage_eq
#print axioms bijective_iff_preimage_image_and_image_preimage_eq
#print axioms surjectivity_bijectivity_criteria_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

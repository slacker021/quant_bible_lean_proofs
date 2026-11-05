import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 4 - Functions and Cardinality
# Auditor Target: 'Theorem: Equivalent Characterizations of Injectivity'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set Function

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

-- 2. DOMAIN SPECIFICATIONS
variable {X Y : Type*} (f : X → Y)

-- 3. THE TARGET THEOREMS: STANDALONE IMPLICATIONS FORMING THE CIRCULAR CHAIN

/-- Theorem 1: (1) ⟹ (2).
    Injectivity implies exact preimage-image recovery. -/
theorem injective_imp_preimage_image_eq (hInj : Injective f) :
    ∀ A : Set X, f ⁻¹' (f '' A) = A := by
  intro A
  apply HasSubset.Subset.antisymm
  · intro x hx
    rcases hx with ⟨a, ha, hfa⟩
    have heq : a = x := hInj hfa
    rw [← heq]
    exact ha
  · intro x hxA
    exact ⟨x, hxA, rfl⟩

/-- Theorem 2: (2) ⟹ (3).
    Preimage-image recovery implies direct image distributivity over intersection. -/
theorem preimage_image_eq_imp_image_inter_eq
    (h2 : ∀ A : Set X, f ⁻¹' (f '' A) = A) :
    ∀ A B : Set X, f '' (A ∩ B) = (f '' A) ∩ (f '' B) := by
  intro A B
  apply HasSubset.Subset.antisymm
  · intro y hy
    rcases hy with ⟨x, ⟨hxA, hxB⟩, hfxy⟩
    exact ⟨⟨x, hxA, hfxy⟩, ⟨x, hxB, hfxy⟩⟩
  · rintro y ⟨⟨x₁, hx₁A, hfx₁⟩, ⟨x₂, hx₂B, hfx₂⟩⟩
    have hx₁_preB : x₁ ∈ f ⁻¹' (f '' B) := by
      change f x₁ ∈ f '' B
      exact ⟨x₂, hx₂B, hfx₂.trans hfx₁.symm⟩
    have hx₁B : x₁ ∈ B := by
      rwa [h2 B] at hx₁_preB
    exact ⟨x₁, ⟨hx₁A, hx₁B⟩, hfx₁⟩

/-- Theorem 3: (3) ⟹ (4).
    Direct image distributivity over intersection preserves pairwise disjointness. -/
theorem image_inter_eq_imp_disjoint_image
    (h3 : ∀ A B : Set X, f '' (A ∩ B) = (f '' A) ∩ (f '' B)) :
    ∀ A B : Set X, A ∩ B = ∅ → (f '' A) ∩ (f '' B) = ∅ := by
  intro A B hDisj
  rw [← h3 A B, hDisj, image_empty]

/-- Theorem 4: (4) ⟹ (5).
    Preservation of disjointness implies preservation of relative complements. -/
theorem disjoint_image_imp_image_diff_eq
    (h4 : ∀ A B : Set X, A ∩ B = ∅ → (f '' A) ∩ (f '' B) = ∅) :
    ∀ A B : Set X, B ⊆ A → f '' (A \ B) = (f '' A) \ (f '' B) := by
  intro A B _
  apply HasSubset.Subset.antisymm
  · intro y hy
    rcases hy with ⟨x, ⟨hxA, hnxB⟩, hfxy⟩
    constructor
    · exact ⟨x, hxA, hfxy⟩
    · rintro ⟨x', hx'B, hfx'⟩
      have hDisj : (A \ B) ∩ B = ∅ := sdiff_inter_self
      have hImageDisj := h4 (A \ B) B hDisj
      have hyInter : y ∈ (f '' (A \ B)) ∩ (f '' B) := ⟨⟨x, ⟨hxA, hnxB⟩, hfxy⟩, ⟨x', hx'B, hfx'⟩⟩
      rw [hImageDisj] at hyInter
      exact hyInter
  · intro y hy
    rcases hy with ⟨⟨x, hxA, hfxy⟩, hnyB⟩
    have hnxB : x ∉ B := by
      intro hxB
      exact hnyB ⟨x, hxB, hfxy⟩
    exact ⟨x, ⟨hxA, hnxB⟩, hfxy⟩

/-- Theorem 5: (5) ⟹ (1).
    Preservation of relative complements implies injectivity. -/
theorem image_diff_eq_imp_injective
    (h5 : ∀ A B : Set X, B ⊆ A → f '' (A \ B) = (f '' A) \ (f '' B)) :
    Injective f := by
  intro x₁ x₂ hEq
  by_contra hNe
  let A : Set X := {x₁, x₂}
  let B : Set X := {x₂}
  have hBA : B ⊆ A := by
    intro x hx
    exact Or.inr hx
  have hDiff : A \ B = {x₁} := by
    ext x
    constructor
    · rintro ⟨hxA, hnxB⟩
      rcases hxA with hx1 | hx2
      · exact mem_singleton_iff.mpr hx1
      · exact (hnxB hx2).elim
    · intro hx
      have hx1 : x = x₁ := mem_singleton_iff.mp hx
      refine ⟨Or.inl hx1, ?_⟩
      intro hxB
      have hx2 : x = x₂ := mem_singleton_iff.mp hxB
      have h12 : x₁ = x₂ := hx1.symm.trans hx2
      exact hNe h12
  have hApplied := h5 A B hBA
  rw [hDiff] at hApplied
  have hfx1 : f x₁ ∈ f '' ({x₁} : Set X) := ⟨x₁, mem_singleton x₁, rfl⟩
  rw [hApplied] at hfx1
  rcases hfx1 with ⟨_, hnot⟩
  have hfx1_in_B : f x₁ ∈ f '' B := ⟨x₂, mem_singleton x₂, hEq.symm⟩
  exact hnot hfx1_in_B

/-- Master Equivalence Theorem: Five Equivalent Set-Theoretic Characterizations of Injectivity. -/
theorem injective_tfae :
    Injective f ↔
    (∀ A : Set X, f ⁻¹' (f '' A) = A) ∧
    (∀ A B : Set X, f '' (A ∩ B) = (f '' A) ∩ (f '' B)) ∧
    (∀ A B : Set X, A ∩ B = ∅ → (f '' A) ∩ (f '' B) = ∅) ∧
    (∀ A B : Set X, B ⊆ A → f '' (A \ B) = (f '' A) \ (f '' B)) := by
  constructor
  · intro hInj
    have h2 := injective_imp_preimage_image_eq f hInj
    have h3 := preimage_image_eq_imp_image_inter_eq f h2
    have h4 := image_inter_eq_imp_disjoint_image f h3
    have h5 := disjoint_image_imp_image_diff_eq f h4
    exact ⟨h2, h3, h4, h5⟩
  · rintro ⟨_, _, _, h5⟩
    exact image_diff_eq_imp_injective f h5

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that the equivalence admits non-degenerate models,
    demonstrated via the identity mapping on natural numbers. -/
lemma equivalent_injectivity_witness :
    ∃ (X Y : Type) (f : X → Y),
      Injective f ∧
      (∀ A : Set X, f ⁻¹' (f '' A) = A) ∧
      (∀ A B : Set X, f '' (A ∩ B) = (f '' A) ∩ (f '' B)) := by
  use ℕ, ℕ, id
  have hInj : Injective (id : ℕ → ℕ) := injective_id
  have h2 := injective_imp_preimage_image_eq (id : ℕ → ℕ) hInj
  have h3 := preimage_image_eq_imp_image_inter_eq (id : ℕ → ℕ) h2
  exact ⟨hInj, h2, h3⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms injective_imp_preimage_image_eq
#print axioms preimage_image_eq_imp_image_inter_eq
#print axioms image_inter_eq_imp_disjoint_image
#print axioms disjoint_image_imp_image_diff_eq
#print axioms image_diff_eq_imp_injective
#print axioms injective_tfae
#print axioms equivalent_injectivity_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

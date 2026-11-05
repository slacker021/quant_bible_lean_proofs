import Mathlib.Data.Set.Basic

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 4 - Functions and Cardinality
# Auditor Target: 'Proposition: Properties of the Direct Image'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

-- 2. DOMAIN SPECIFICATIONS
variable {X Y : Type*} (f : X → Y) (A B : Set X)

-- 3. THE TARGET THEOREMS

/-- Proposition 1: Monotonicity of Direct Image.
    If A ⊆ B, then f(A) ⊆ f(B). -/
theorem image_mono (hAB : A ⊆ B) : f '' A ⊆ f '' B := by
  intro y hy
  -- By definition of direct image, ∃ x ∈ A such that f(x) = y:
  rcases hy with ⟨x, hxA, hfxy⟩
  -- Since A ⊆ B, x ∈ B:
  have hxB : x ∈ B := hAB hxA
  -- Therefore, y = f(x) ∈ f '' B:
  exact ⟨x, hxB, hfxy⟩

/-- Proposition 2: Non-emptiness Preservation.
    If A is non-empty, then its direct image f(A) is non-empty. -/
theorem image_nonempty (hA : A.Nonempty) : (f '' A).Nonempty := by
  -- There exists a witness element x₀ ∈ A:
  rcases hA with ⟨x₀, hx₀⟩
  -- Its image y₀ = f(x₀) belongs to f '' A:
  exact ⟨f x₀, x₀, hx₀, rfl⟩

/-- Proposition 3: Intersection Sub-distributivity.
    The direct image of an intersection is contained within the intersection of the direct images:
    f(A ∩ B) ⊆ f(A) ∩ f(B). -/
theorem image_inter_subset : f '' (A ∩ B) ⊆ (f '' A) ∩ (f '' B) := by
  intro y hy
  rcases hy with ⟨x, ⟨hxA, hxB⟩, hfxy⟩
  have hyA : y ∈ f '' A := ⟨x, hxA, hfxy⟩
  have hyB : y ∈ f '' B := ⟨x, hxB, hfxy⟩
  exact ⟨hyA, hyB⟩

/-- Proposition 4: Union Distributivity.
    The direct image of a union is identically the union of the direct images:
    f(A ∪ B) = f(A) ∪ f(B). -/
theorem image_union_eq : f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by
  apply HasSubset.Subset.antisymm
  · -- Forward inclusion: f '' (A ∪ B) ⊆ (f '' A) ∪ (f '' B)
    intro y hy
    rcases hy with ⟨x, hxAB, hfxy⟩
    cases hxAB with
    | inl hxA =>
      have hyA : y ∈ f '' A := ⟨x, hxA, hfxy⟩
      exact Or.inl hyA
    | inr hxB =>
      have hyB : y ∈ f '' B := ⟨x, hxB, hfxy⟩
      exact Or.inr hyB
  · -- Reverse inclusion via monotonicity:
    have h1 : f '' A ⊆ f '' (A ∪ B) := image_mono f A (A ∪ B) subset_union_left
    have h2 : f '' B ⊆ f '' (A ∪ B) := image_mono f B (A ∪ B) subset_union_right
    exact union_subset h1 h2

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that direct image properties admit concrete non-empty
    subsets under the identity mapping. -/
lemma direct_image_properties_witness :
    ∃ (X Y : Type) (f : X → Y) (A B : Set X),
      A.Nonempty ∧ B.Nonempty ∧
      (f '' (A ∪ B) = (f '' A) ∪ (f '' B)) ∧
      (f '' (A ∩ B) ⊆ (f '' A) ∩ (f '' B)) := by
  use ℕ, ℕ, id, {0}, {1}
  refine ⟨⟨0, rfl⟩, ⟨1, rfl⟩, image_union_eq id {0} {1}, image_inter_subset id {0} {1}⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms image_mono
#print axioms image_nonempty
#print axioms image_inter_subset
#print axioms image_union_eq
#print axioms direct_image_properties_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

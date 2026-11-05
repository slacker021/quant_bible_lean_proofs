import Mathlib.Data.Set.Basic

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 4 - Functions and Cardinality
# Auditor Target: 'Lemma: Fundamental Boolean Properties of Preimages'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

-- 2. DOMAIN SPECIFICATIONS
variable {X Y : Type*} (f : X → Y) (A' B' : Set Y)

-- 3. THE TARGET THEOREMS

/-- Lemma 1: Monotonicity of Preimage.
    Subsetting in the codomain preserves containment under the preimage operator. -/
theorem preimage_mono (hAB : A' ⊆ B') : f ⁻¹' A' ⊆ f ⁻¹' B' := by
  intro x hx
  -- x ∈ f ⁻¹' A' ⟹ f(x) ∈ A':
  have hfxA : f x ∈ A' := hx
  -- A' ⊆ B' ⟹ f(x) ∈ B':
  have hfxB : f x ∈ B' := hAB hfxA
  -- Therefore x ∈ f ⁻¹' B':
  exact hfxB

/-- Lemma 2: Distributivity of Preimage over Intersection (Intersection Preservation).
    The preimage of an intersection is identically the intersection of the preimages. -/
theorem preimage_inter_eq : f ⁻¹' (A' ∩ B') = (f ⁻¹' A') ∩ (f ⁻¹' B') := by
  ext x
  calc
    x ∈ f ⁻¹' (A' ∩ B') ↔ f x ∈ A' ∩ B'                   := Iff.rfl
    _                  ↔ (f x ∈ A') ∧ (f x ∈ B')         := Iff.rfl
    _                  ↔ (x ∈ f ⁻¹' A') ∧ (x ∈ f ⁻¹' B') := Iff.rfl
    _                  ↔ x ∈ (f ⁻¹' A') ∩ (f ⁻¹' B')     := Iff.rfl

/-- Lemma 3: Distributivity of Preimage over Union (Union Preservation).
    The preimage of a union is identically the union of the preimages. -/
theorem preimage_union_eq : f ⁻¹' (A' ∪ B') = (f ⁻¹' A') ∪ (f ⁻¹' B') := by
  ext x
  calc
    x ∈ f ⁻¹' (A' ∪ B') ↔ f x ∈ A' ∪ B'                   := Iff.rfl
    _                  ↔ (f x ∈ A') ∨ (f x ∈ B')         := Iff.rfl
    _                  ↔ (x ∈ f ⁻¹' A') ∨ (x ∈ f ⁻¹' B') := Iff.rfl
    _                  ↔ x ∈ (f ⁻¹' A') ∪ (f ⁻¹' B')     := Iff.rfl

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that the Boolean preimage identities hold on non-empty,
    distinct sets under a concrete mapping. -/
lemma preimage_properties_witness :
    ∃ (X Y : Type) (f : X → Y) (A' B' : Set Y),
      A'.Nonempty ∧ B'.Nonempty ∧
      (f ⁻¹' (A' ∩ B') = (f ⁻¹' A') ∩ (f ⁻¹' B')) ∧
      (f ⁻¹' (A' ∪ B') = (f ⁻¹' A') ∪ (f ⁻¹' B')) := by
  use ℕ, ℕ, id, {0}, {1}
  refine ⟨⟨0, rfl⟩, ⟨1, rfl⟩, preimage_inter_eq id {0} {1}, preimage_union_eq id {0} {1}⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms preimage_mono
#print axioms preimage_inter_eq
#print axioms preimage_union_eq
#print axioms preimage_properties_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

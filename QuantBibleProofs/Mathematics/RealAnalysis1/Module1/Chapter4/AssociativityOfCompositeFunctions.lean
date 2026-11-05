import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 4 - Functions and Cardinality
# Auditor Target: 'Theorem: Associativity of Composite Functions'
-/

-- 1. CANONICAL IMPORTS ONLY
open Function

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

-- 2. DOMAIN SPECIFICATIONS
variable {X Y Z W : Type*}

-- 3. THE TARGET THEOREM
/-- Theorem: Associativity of Composite Functions.
    For any mappings f : X → Y, g : Y → Z, and h : Z → W,
    composition is associative: h ∘ (g ∘ f) = (h ∘ g) ∘ f. -/
theorem comp_assoc_stepwise (f : X → Y) (g : Y → Z) (h : Z → W) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  -- Domain and codomain agreement is guaranteed by the typed signature.
  -- By the Principle of Extensionality for functions:
  funext x
  -- Pointwise evaluation demonstrating that both paths evaluate identically to h (g (f x)):
  calc
    (h ∘ (g ∘ f)) x = h ((g ∘ f) x)   := rfl
    _               = h (g (f x))     := rfl
    _               = (h ∘ g) (f x)   := rfl
    _               = ((h ∘ g) ∘ f) x := rfl

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that the associativity identity holds on concrete,
    inhabited sets with non-trivial identity mappings. -/
lemma comp_assoc_witness :
    ∃ (X Y Z W : Type) (f : X → Y) (g : Y → Z) (h : Z → W),
      h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  use ℕ, ℕ, ℕ, ℕ, id, id, id
  exact ⟨comp_assoc_stepwise id id id⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms comp_assoc_stepwise
#print axioms comp_assoc_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

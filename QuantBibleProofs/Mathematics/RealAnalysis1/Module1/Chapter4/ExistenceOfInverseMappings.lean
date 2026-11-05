import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 4 - Functions and Cardinality
# Auditor Target: 'Theorem: Existence and Uniqueness of Inverse Mappings'
-/

-- 1. CANONICAL IMPORTS ONLY
open Function

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

-- 2. DOMAIN SPECIFICATIONS
variable {X Y : Type*} (f : X → Y)

-- 3. THE TARGET THEOREMS

/-- Theorem: Existence and Characterization of Inverse Mappings.
    A mapping f : X → Y admits a two-sided inverse g : Y → X if and only if f is bijective. -/
theorem inverse_mapping_exists_iff_bijective :
    (∃ g : Y → X, g ∘ f = id ∧ f ∘ g = id) ↔ Bijective f := by
  constructor
  · -- Necessity: (∃ g, g ∘ f = id ∧ f ∘ g = id) ⟹ Bijective f
    rintro ⟨g, hgf, hfg⟩
    constructor
    · -- Injectivity:
      intro x₁ x₂ hEq
      calc
        x₁ = (g ∘ f) x₁ := by rw [hgf, id_eq]
        _  = g (f x₁)   := rfl
        _  = g (f x₂)   := by rw [hEq]
        _  = (g ∘ f) x₂ := rfl
        _  = x₂         := by rw [hgf, id_eq]
    · -- Surjectivity:
      intro y
      use g y
      calc
        f (g y) = (f ∘ g) y := rfl
        _       = id y      := by rw [hfg]
        _       = y         := rfl
  · -- Sufficiency: Bijective f ⟹ (∃ g, g ∘ f = id ∧ f ∘ g = id)
    intro ⟨hInj, hSurj⟩
    -- Construct g using classical choice on non-empty fiber sets:
    choose g hg using hSurj
    refine ⟨g, ?_, ?_⟩
    · -- g ∘ f = id
      funext x
      apply hInj
      exact hg (f x)
    · -- f ∘ g = id
      funext y
      exact hg y

/-- Theorem: Uniqueness of Two-Sided Inverse Mappings.
    If g₁ and g₂ are both two-sided inverses of f, then g₁ = g₂. -/
theorem inverse_mapping_uniqueness (g₁ g₂ : Y → X)
    (h₁ : g₁ ∘ f = id ∧ f ∘ g₁ = id)
    (h₂ : g₂ ∘ f = id ∧ f ∘ g₂ = id) :
    g₁ = g₂ := by
  rcases h₁ with ⟨hg1f, _⟩
  rcases h₂ with ⟨_, hfg2⟩
  funext y
  calc
    g₁ y = g₁ (id y)        := rfl
    _    = g₁ ((f ∘ g₂) y)  := by rw [hfg2]
    _    = (g₁ ∘ f) (g₂ y)  := rfl
    _    = id (g₂ y)        := by rw [hg1f]
    _    = g₂ y             := rfl

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that bijective mappings admit valid, unique inverses
    on concrete inhabited spaces. -/
lemma inverse_mapping_witness :
    ∃ (X Y : Type) (f : X → Y) (g : Y → X),
      Bijective f ∧ g ∘ f = id ∧ f ∘ g = id := by
  use ℕ, ℕ, id, id
  exact ⟨bijective_id, rfl, rfl⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms inverse_mapping_exists_iff_bijective
#print axioms inverse_mapping_uniqueness
#print axioms inverse_mapping_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

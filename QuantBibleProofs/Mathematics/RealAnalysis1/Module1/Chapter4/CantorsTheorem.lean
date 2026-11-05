import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

/-!
# Volume: Real Analysis 1
# Module: Module 1 - General Mathematical Concepts and Notation
# Chapter: Chapter 4 - Functions and Cardinality
# Auditor Target: 'Theorem: Cantor\'s Theorem'
-/

-- 1. CANONICAL IMPORTS ONLY
open Set Function

namespace QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

-- 2. DOMAIN SPECIFICATIONS
variable {X : Type*}

-- 3. THE TARGET THEOREMS

/-- Section 1: Weak Cardinality Dominance.
    The canonical mapping sending each element x to its singleton {x} is an injection
    from X into its power set 𝒫(X). -/
theorem cantor_singleton_injective :
    Injective (fun x : X => ({x} : Set X)) := by
  intro x₁ x₂ hEq
  have hMem : x₁ ∈ ({x₂} : Set X) := by
    rw [← hEq]
    exact mem_singleton x₁
  exact mem_singleton_iff.mp hMem

/-- Section 2: Strict Cardinality Separation.
    For every set X, there exists no surjective mapping from X onto its power set 𝒫(X). -/
theorem cantor_not_surjective (g : X → Set X) : ¬ Surjective g := by
  intro hSurj
  -- Construct the diagonal set D := { x ∈ X | x ∉ g(x) }:
  let D : Set X := { x | x ∉ g x }
  -- By surjectivity, there exists a witness element d ∈ X such that g(d) = D:
  rcases hSurj D with ⟨d, hd⟩
  -- Evaluate whether d ∈ D, generating a contradiction in both branches:
  have hiff : d ∈ D ↔ d ∉ D := by
    calc
      d ∈ D ↔ d ∉ g d := Iff.rfl
      _     ↔ d ∉ D   := by rw [hd]
  -- A proposition equivalent to its own negation is contradictory:
  by_cases h : d ∈ D
  · have hnot : d ∉ D := hiff.mp h
    exact hnot h
  · have hin : d ∈ D := hiff.mpr h
    exact h hin

/-- Corollary: Non-existence of Bijective Correspondences with the Power Set.
    Because no mapping from X into 𝒫(X) can be surjective, no bijection can exist. -/
theorem cantor_not_bijective (g : X → Set X) : ¬ Bijective g := by
  intro ⟨_, hSurj⟩
  exact cantor_not_surjective g hSurj

-- 4. THE NON-VACUITY WITNESS
/-- Companion Witness: Verifies that Cantor's theorem holds on an inhabited universe
    equipped with a concrete mapping into its power set. -/
lemma cantor_witness :
    ∃ (X : Type) (g : X → Set X),
      Injective (fun x : X => ({x} : Set X)) ∧ ¬ Surjective g ∧ ¬ Bijective g := by
  use ℕ, (fun _ => ∅)
  refine ⟨cantor_singleton_injective, cantor_not_surjective _, cantor_not_bijective _⟩

-- 5. KERNEL AUDIT INSPECTION
#print axioms cantor_singleton_injective
#print axioms cantor_not_surjective
#print axioms cantor_not_bijective
#print axioms cantor_witness

end QuantBibleProofs.Mathematics.RealAnalysis1.Module1.Chapter4

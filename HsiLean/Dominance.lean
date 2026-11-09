import HsiLean.Basic
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

def UniversallyDominant (δ : Semimeasure) : Prop :=
  δ.Enumerable ∧ ∀ μ : Semimeasure, μ.Enumerable → ∃ c > 0, ∀ x, c * μ x ≤ δ x

theorem exists_dominant_not_universalSemimeasure:
  ∃ δ, UniversallyDominant δ ∧ ¬ IsUniversalMixture δ := by
  sorry

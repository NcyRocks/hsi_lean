import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic
import HsiLean.Basic

theorem mixtureSets_eq_universalMixtures
    (ν : ℕ → Semimeasure)
    (W : WoodInterface)
    (hν_enum : UniformlyEnumerable ν)
    (hν_univ : ContainsAllUniversalMixtures ν)
    (μ : ℕ → Semimeasure)
    (hμ_enum : UniformlyEnumerable μ)
    (hμ_univ : ContainsAllUniversalMixtures μ) :
    MixtureClass ν = MixtureClass μ := by

    rw [mixtureClass_eq_universalMixtures ν W hν_enum hν_univ]
    rw [mixtureClass_eq_universalMixtures μ W hμ_enum hμ_univ]

theorem union_mixtureClasses_eq_universalMixtures
    (W : WoodInterface)
    (N : Set (ℕ → Semimeasure))
    (hN_nonempty : N.Nonempty)
    (hN : ∀ ν ∈ N, UniformlyEnumerable ν ∧ ContainsAllUniversalMixtures ν) :
    ⋃ ν ∈ N, MixtureClass ν = {ξ | IsUniversalMixture ξ} := by
  obtain ⟨v₀, hv₀⟩ := hN_nonempty
  apply Set.Subset.antisymm
  · intro ξ hξ
    rw [Set.mem_iUnion₂] at hξ
    obtain ⟨ν, hν, hξν⟩ := hξ
    rw [mixtureClass_eq_universalMixtures ν W (hN ν hν).1 (hN ν hν).2] at hξν
    -- hξν : ξ ∈ {ξ | IsUniversalMixture ξ}, which is exactly the goal
    exact hξν
  · sorry

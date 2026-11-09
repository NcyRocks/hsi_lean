import Mathlib.Probability.Martingale.Convergence
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Posteriors over a countable class of measures

Statements: Claude, 2026-11-09, checked by Nathan before the run. Proofs: the agent.

Source: Cohen & Hutter 2020, *Pessimism About Unknown Unknowns Inspires Conservatism*,
Appendix C (`PIBBSS\refs\arxiv\2006.08753\main.tex`, from ~line 880): the posterior-stability
lemma, "Overtaking is Unlikely" (`lem:overtaking`) and "Sum of limits" (`lem:sumoflimits`, ~line 939).

Setting: infinite binary sequences `ℕ → Bool`; a countable class of probability measures `Q i`
with prior weights `w i` summing to one; the true environment is `Q i₀`, with `w i₀ ≠ 0`
(the paper's global assumption that the truth has positive prior weight).
-/

namespace HsiLean.Posterior

open MeasureTheory Filter ENNReal Topology

/-- The first `t` bits of `ω`. -/
def pre (ω : ℕ → Bool) (t : ℕ) : List Bool := List.ofFn fun i : Fin t => ω i

/-- The cylinder of sequences that begin with `x`. -/
def cyl (x : List Bool) : Set (ℕ → Bool) := {ω | pre ω x.length = x}

variable (Q : ℕ → Measure (ℕ → Bool)) (w : ℕ → ℝ≥0∞)

/-- The Bayes mixture on finite strings: `ξ(x) = Σ_i w_i Q_i(x)`. -/
noncomputable def mix (x : List Bool) : ℝ≥0∞ := ∑' i, w i * Q i (cyl x)

/-- The posterior weight of `Q i` after seeing `x`: `w(Q_i | x) = w_i Q_i(x) / ξ(x)`. -/
noncomputable def post (i : ℕ) (x : List Bool) : ℝ≥0∞ := w i * Q i (cyl x) / mix Q w x

variable [∀ i, IsProbabilityMeasure (Q i)]

/-- Posteriors sum to one wherever the mixture is positive. -/
theorem tsum_post (hw : ∑' i, w i = 1) (x : List Bool) (hx : mix Q w x ≠ 0) :
    ∑' i, post Q w i x = 1 := by
  sorry

/-- **Overtaking is unlikely** (Cohen–Hutter `lem:overtaking`, from Hutter 2009 Lemma 4):
`P[R(x_{<t}) / P(x_{<t}) ≥ c infinitely often] ≤ 1/c`, written without division. -/
theorem overtaking (P R : Measure (ℕ → Bool)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure R] (c : ℝ≥0∞) (hc : c ≠ 0) :
    P {ω | ∃ᶠ t in atTop, c * P (cyl (pre ω t)) ≤ R (cyl (pre ω t))} ≤ c⁻¹ := by
  sorry

/-- **Posteriors converge** (Cohen–Hutter's posterior-stability lemma, from Hutter 2016
Thm 4): each posterior weight converges with probability one under the true measure. -/
theorem post_converges (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0) (i : ℕ) :
    ∀ᵐ ω ∂(Q i₀), ∃ L, Tendsto (fun t => post Q w i (pre ω t)) atTop (𝓝 L) := by
  sorry

/-- **Sum of limits** (Cohen–Hutter `lem:sumoflimits`): with probability one under the true
measure, every posterior converges and the limits still sum to one — no posterior mass
escapes to infinity. -/
theorem sum_of_limits (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0) :
    ∀ᵐ ω ∂(Q i₀), ∃ L : ℕ → ℝ≥0∞,
      (∀ i, Tendsto (fun t => post Q w i (pre ω t)) atTop (𝓝 (L i))) ∧ ∑' i, L i = 1 := by
  sorry

end HsiLean.Posterior

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

/-! ## The Bayes-mixture measure -/

/-- The Bayes mixture as a measure on `ℕ → Bool`: `μ_ξ := Σ_i w_i • Q_i`. -/
noncomputable def mixMeasure : Measure (ℕ → Bool) := Measure.sum (fun i => w i • Q i)

variable [∀ i, IsProbabilityMeasure (Q i)]

/-- Cylinders are determined by finitely many coordinates, so they are measurable. -/
lemma cyl_measurable (x : List Bool) : MeasurableSet (cyl x) := by
  have h : cyl x = ⋂ i : Fin x.length, {ω : ℕ → Bool | ω i.val = x[i.val]} := by
    ext ω
    simp only [cyl, pre, Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h i => ?_, fun h => ?_⟩
    · have hget : (List.ofFn (fun j : Fin x.length => ω j.val))[i.val]? = x[i.val]? := by
        rw [h]
      simpa [List.getElem?_ofFn, i.isLt] using hget
    · apply List.ext_getElem
      · simp
      · intro j h1 h2
        simp only [List.getElem_ofFn]
        exact h ⟨j, by simpa using h2⟩
  rw [h]
  exact MeasurableSet.iInter fun i =>
    (measurable_pi_apply i.val) (MeasurableSet.singleton _)

/-- The mixture measure evaluated on a cylinder matches `mix`. -/
lemma mixMeasure_cyl (x : List Bool) : mixMeasure Q w (cyl x) = mix Q w x := by
  rw [mixMeasure, Measure.sum_apply _ (cyl_measurable x)]
  rfl

/-- The mixture measure is a probability measure when the prior weights sum to one. -/
lemma isProbabilityMeasure_mixMeasure (hw : ∑' i, w i = 1) :
    IsProbabilityMeasure (mixMeasure Q w) where
  measure_univ := by
    rw [mixMeasure, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact hw

/-- Each weighted summand is dominated by the mixture measure. -/
lemma smul_le_mixMeasure (i : ℕ) : w i • Q i ≤ mixMeasure Q w := by
  exact Measure.le_sum _ i

/-- When `w i ≠ 0` and `w i ≠ ∞`, `Q i` is absolutely continuous w.r.t. the mixture measure. -/
lemma absolutelyContinuous_mixMeasure (i : ℕ) (hwi : w i ≠ 0) (hwi' : w i ≠ ⊤) :
    Q i ≪ mixMeasure Q w := by
  intro s hs
  have hle : (w i • Q i) s ≤ mixMeasure Q w s := smul_le_mixMeasure Q w i s
  rw [Measure.smul_apply, smul_eq_mul] at hle
  rw [hs, le_zero_iff, mul_eq_zero] at hle
  rcases hle with h | h
  · exact absurd h hwi
  · exact h

/-- Posteriors sum to one wherever the mixture is positive. -/
theorem tsum_post (hw : ∑' i, w i = 1) (x : List Bool) (hx : mix Q w x ≠ 0) :
    ∑' i, post Q w i x = 1 := by
  have h_mix_le_one : mix Q w x ≤ 1 := by
    unfold mix
    calc ∑' i, w i * Q i (cyl x)
        ≤ ∑' i, w i * 1 :=
          ENNReal.tsum_le_tsum fun i => by gcongr; exact prob_le_one
      _ = ∑' i, w i := by simp
      _ = 1 := hw
  have h_mix_ne_top : mix Q w x ≠ ⊤ := ne_top_of_le_ne_top one_ne_top h_mix_le_one
  simp only [post, ENNReal.div_eq_inv_mul]
  rw [ENNReal.tsum_mul_left]
  change (mix Q w x)⁻¹ * mix Q w x = 1
  exact ENNReal.inv_mul_cancel hx h_mix_ne_top

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

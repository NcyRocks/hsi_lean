-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-10 and has NOT been reviewed by Nathan.
import HsiLean.Rate

/-!
# The rate theorem's hypothesis `∑' a, P j a ≤ 1` cannot be dropped

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-10. Not reviewed by Nathan.

Formalises the counterexample in `paper-drafts/UNAPPROVED_hsi_rate.tex` (the remark
"Assumption (ii) cannot be dropped"), which concerns `eq:hsi-convergence` in
`paper/ALT format.tex`, §"Optimality properties".

## The example

* Items: `Bool`, with `false` standing for the string `0` and `true` for the string `00`. The
  item set `{0, 00}` is not prefix-free.
* `cexP 0` — the true model: probability `1/2` for each item.
* `cexP 1` — a model giving probability `1` to *each* item (the semimeasure concentrated on
  `000…` gives probability one to both `0` and `00`). Its values sum to `2` over the items.
* `cexP j = 0` for `j ≥ 2`.
* `cexW` — weight `1/2` on each of the models `0` and `1`.

Every hypothesis of `HsiLean.Rate.IIDFromModel` holds except `model_sub` (at `j = 1`), and the
expected excess log-loss on the `ν`-th item tends to `-1`, not to `0`.

In this example the excess does not depend on the data at all: for a dataset of `n` items it is
`-1 - log₂ ((2⁻ⁿ⁻¹ + 1) / (2⁻ⁿ + 1))` (`excess_cex`).

## Which reading of an item's probability this file uses (added 2026-11-11)

There are three readings of "the probability a model `ν` gives to the item `x`" under which the
rate holds: (a) conditioned on the item's length (Nathan's intended reading;
`HsiRateLength.lean`); (b) the stopping model, the paper's `lm:bijection` (the probability that
a machine's output is exactly `x`, i.e. `ν x - ν (x0) - ν (x1)`; `HsiRateStop.lean`); (c) `ν x` with items
restricted to a prefix-free set (`HsiRate.lean`).

This file uses NONE of them: it takes the item's probability to be `ν x` itself, over the item
set `{0, 00}`, which is not prefix-free, with no conditioning on length. So it shows what goes
wrong when the reading is left unstated; it is not a counterexample to (a), (b) or (c). Under
reading (a) the same example has excess exactly `0`
(`HsiLean.HsiRateLength.rate_counterexample_length`): given the length, the "true" model and the
`000…` model make the same prediction.
-/

namespace HsiLean.RateCounterexample

open MeasureTheory ProbabilityTheory Filter ENNReal Topology HsiLean.Rate

/-- The models. `cexP 0` is uniform on the two items; `cexP 1` gives each item probability one;
all other models are zero. -/
noncomputable def cexP : ℕ → Bool → ℝ≥0∞ :=
  fun j _ => if j = 0 then 2⁻¹ else if j = 1 then 1 else 0

/-- The weights: `1/2` on model `0` and on model `1`, zero elsewhere. -/
noncomputable def cexW : ℕ → ℝ≥0∞ := fun j => if j < 2 then 2⁻¹ else 0

/-! ## Which hypotheses of the rate theorem hold -/

/-- **[UNAPPROVED STATEMENT]** The true model `cexP 0` is a probability distribution on the
items. -/
theorem tsum_cexP_zero : ∑' a, cexP 0 a = 1 := by
  simp only [cexP, if_true, tsum_fintype, Fintype.sum_bool]
  exact ENNReal.inv_two_add_inv_two

/-- **[UNAPPROVED STATEMENT]** The second model's values sum to `2` over the items. -/
theorem tsum_cexP_one : ∑' a, cexP 1 a = 2 := by
  simp [cexP, tsum_fintype, one_add_one_eq_two]

/-- **[UNAPPROVED STATEMENT]** The hypothesis `model_sub` of the rate theorem fails. -/
theorem not_model_sub : ¬ ∀ j, ∑' a, cexP j a ≤ 1 := by
  intro h
  have h1 := h 1
  rw [tsum_cexP_one] at h1
  exact absurd h1 (by norm_num)

/-- **[UNAPPROVED STATEMENT]** The weights sum to one (so `weight_sub` holds). -/
theorem tsum_cexW : ∑' j, cexW j = 1 := by
  rw [tsum_eq_sum (s := Finset.range 2) (fun j hj => by simp_all [cexW])]
  simp [cexW, Finset.sum_range_succ, ENNReal.inv_two_add_inv_two]

/-- **[UNAPPROVED STATEMENT]** The true model has positive weight (`weight_pos` holds). -/
theorem cexW_zero_ne_zero : cexW 0 ≠ 0 := by simp [cexW]

/-- **[UNAPPROVED STATEMENT]** There is a probability space carrying an i.i.d. sequence of items
drawn from the true model `cexP 0`: so `meas`, `indep` and `law` hold as well, and `model_sub`
is the only hypothesis of the rate theorem that fails. -/
theorem exists_iid_cex :
    ∃ Pr : Measure (ℕ → Bool), IsProbabilityMeasure Pr ∧
      (∀ ν, Measurable (fun ω : ℕ → Bool => ω ν)) ∧
      iIndepFun (fun ν (ω : ℕ → Bool) => ω ν) Pr ∧
      ∀ ν a, Pr ((fun ω : ℕ → Bool => ω ν) ⁻¹' {a}) = cexP 0 a := by
  let p : PMF Bool := ⟨cexP 0, ENNReal.summable.hasSum_iff.mpr tsum_cexP_zero⟩
  refine ⟨Measure.infinitePi (fun _ : ℕ => p.toMeasure), inferInstance,
    fun ν => measurable_pi_apply ν, ?_, fun ν a => ?_⟩
  · exact iIndepFun_infinitePi (P := fun _ : ℕ => p.toMeasure) (X := fun _ a => a)
      (fun _ => measurable_id)
  · rw [← Measure.map_apply (measurable_pi_apply ν) (measurableSet_singleton a),
      Measure.infinitePi_map_eval, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
    rfl

/-! ## The excess, computed -/

lemma lik_cexP_zero (xs : List Bool) : lik cexP 0 xs = 2⁻¹ ^ xs.length := by
  induction xs with
  | nil => simp [lik]
  | cons a xs ih =>
    have h : lik cexP 0 (a :: xs) = cexP 0 a * lik cexP 0 xs := by simp [lik]
    rw [h, ih, List.length_cons, pow_succ']
    simp [cexP]

lemma lik_cexP_one (xs : List Bool) : lik cexP 1 xs = 1 := by
  induction xs with
  | nil => simp [lik]
  | cons a xs ih =>
    have h : lik cexP 1 (a :: xs) = cexP 1 a * lik cexP 1 xs := by simp [lik]
    rw [h, ih]
    simp [cexP]

lemma mixL_cex (xs : List Bool) :
    mixL cexP cexW xs = 2⁻¹ * 2⁻¹ ^ xs.length + 2⁻¹ := by
  unfold mixL
  rw [tsum_eq_sum (s := Finset.range 2) (fun j hj => by simp_all [cexW])]
  simp [cexW, Finset.sum_range_succ, lik_cexP_zero, lik_cexP_one]

lemma toReal_mixL_cex (xs : List Bool) :
    (mixL cexP cexW xs).toReal = 2⁻¹ * ((2⁻¹ : ℝ) ^ xs.length + 1) := by
  have ht : (2⁻¹ : ℝ≥0∞) * 2⁻¹ ^ xs.length ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp))
  rw [mixL_cex, ENNReal.toReal_add ht (by simp)]
  simp
  ring

/-- **[UNAPPROVED STATEMENT]** In the example the excess log-loss does not depend on the data:
after any dataset `xs` of `n` items, the excess on any new item `a` is
`-1 - log₂ ((2⁻ⁿ⁻¹ + 1) / (2⁻ⁿ + 1))`. -/
theorem excess_cex (xs : List Bool) (a : Bool) :
    excess cexP cexW 0 xs a
      = -1 - Real.logb 2 (((2⁻¹ : ℝ) ^ (xs.length + 1) + 1) / ((2⁻¹ : ℝ) ^ xs.length + 1)) := by
  have h1 : (cexP 0 a).toReal = 2⁻¹ := by simp [cexP]
  have h2 : (pred cexP cexW xs a).toReal
      = ((2⁻¹ : ℝ) ^ (xs.length + 1) + 1) / ((2⁻¹ : ℝ) ^ xs.length + 1) := by
    unfold pred
    rw [ENNReal.toReal_div, toReal_mixL_cex, toReal_mixL_cex, List.length_append,
      List.length_singleton]
    rw [mul_div_mul_left _ _ (by norm_num : (2⁻¹ : ℝ) ≠ 0)]
  unfold excess
  rw [h1, h2, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]

/-- The excess after `n` items, as a sequence of reals. -/
noncomputable def cexExcess (n : ℕ) : ℝ :=
  -1 - Real.logb 2 (((2⁻¹ : ℝ) ^ (n + 1) + 1) / ((2⁻¹ : ℝ) ^ n + 1))

lemma tendsto_cexExcess : Tendsto cexExcess atTop (𝓝 (-1)) := by
  have hp : Tendsto (fun n : ℕ => (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hp1 : Tendsto (fun n : ℕ => (2⁻¹ : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hp
  have hr : Tendsto (fun n : ℕ => ((2⁻¹ : ℝ) ^ (n + 1) + 1) / ((2⁻¹ : ℝ) ^ n + 1))
      atTop (𝓝 ((0 + 1) / (0 + 1))) :=
    (hp1.add_const 1).div (hp.add_const 1) (by norm_num)
  have hl := (hr.log (by norm_num)).div_const (Real.log 2)
  have hfin := (tendsto_const_nhds (x := (-1 : ℝ))).sub hl
  have e : cexExcess = fun n : ℕ =>
      -1 - Real.log (((2⁻¹ : ℝ) ^ (n + 1) + 1) / ((2⁻¹ : ℝ) ^ n + 1)) / Real.log 2 := rfl
  rw [e]
  simpa using hfin

/-! ## The expected excess tends to `-1` -/

section Prob

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma excessAt_cex (X : ℕ → Ω → Bool) (ν : ℕ) (ω : Ω) :
    excessAt cexP cexW 0 X ν ω = cexExcess ν := by
  unfold excessAt
  rw [excess_cex]
  simp [cexExcess, dataPrefix]

/-- **[UNAPPROVED STATEMENT]** In the example, on any probability space and for any sequence of
items `X` (in particular an i.i.d. sequence drawn from the true model, which exists by
`exists_iid_cex`), the expected excess log-loss on the `ν`-th item tends to `-1` as `ν → ∞`. -/
theorem tendsto_expected_excess_cex (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → Bool) :
    Tendsto (fun ν => ∫ ω, excessAt cexP cexW 0 X ν ω ∂Pr) atTop (𝓝 (-1)) := by
  have e : (fun ν => ∫ ω, excessAt cexP cexW 0 X ν ω ∂Pr) = cexExcess := by
    funext ν
    simp [excessAt_cex]
  rw [e]
  exact tendsto_cexExcess

/-- **[UNAPPROVED STATEMENT]** So the conclusion of `HsiLean.Rate.tendsto_expected_excess`
(the paper's `eq:hsi-convergence`) is false in the example: the expected excess does not tend
to `0`. -/
theorem not_tendsto_expected_excess_cex (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → Bool) :
    ¬ Tendsto (fun ν => ∫ ω, excessAt cexP cexW 0 X ν ω ∂Pr) atTop (𝓝 0) := by
  intro h
  have := tendsto_nhds_unique h (tendsto_expected_excess_cex Pr X)
  norm_num at this

/-- **[UNAPPROVED STATEMENT]** The counterexample in one statement: there is a probability
space with an i.i.d. sequence of items drawn from the true model `cexP 0`, the weights sum to
at most one, the true model has positive weight, `model_sub` fails, and the expected excess
log-loss tends to `-1`. -/
theorem rate_counterexample :
    ∃ (Pr : Measure (ℕ → Bool)) (X : ℕ → (ℕ → Bool) → Bool), IsProbabilityMeasure Pr ∧
      (¬ ∀ j, ∑' a, cexP j a ≤ 1) ∧
      ∑' j, cexW j ≤ 1 ∧
      cexW 0 ≠ 0 ∧
      (∀ ν, Measurable (X ν)) ∧
      iIndepFun X Pr ∧
      (∀ ν a, Pr (X ν ⁻¹' {a}) = cexP 0 a) ∧
      Tendsto (fun ν => ∫ ω, excessAt cexP cexW 0 X ν ω ∂Pr) atTop (𝓝 (-1)) := by
  obtain ⟨Pr, hPr, hm, hi, hl⟩ := exists_iid_cex
  exact ⟨Pr, fun ν ω => ω ν, hPr, not_model_sub, tsum_cexW.le, cexW_zero_ne_zero, hm, hi, hl,
    tendsto_expected_excess_cex Pr _⟩

end Prob

end HsiLean.RateCounterexample

-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.HsiRate
import HsiLean.RateCounterexample

/-!
# HSI end to end, with item probabilities CONDITIONED ON THE ITEM'S LENGTH

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-11. Not reviewed by Nathan.

Source: `paper/ALT format.tex`, §"Optimality properties" (`eq:hsi-error-bound`,
`eq:hsi-convergence`) and `thm:enums-of-ums=ums`. The reading of a dataset item used here is
Nathan's (2026-11-11); the paper does not state it.

## Three readings of "the probability a model gives to a dataset item `x`"

(a) **Conditioned on length (this file).** Given that an item has `n` symbols, model `ν` gives
    content `x` (with `|x| = n`) probability `ν x`. E.g. the machine that always outputs `00…`
    predicts `0` with certainty given length 1 and `00` with certainty given length 2. Items may
    have ANY lengths; no prefix-free restriction.
(b) **The stopping model** (the paper's `lm:bijection`): the probability that the machine's
    output is exactly `x`, i.e. `ν x - ν (x0) - ν (x1)` (`HsiRateStop.lean`).
(c) **Prefix-free items** (`HsiRate.lean`): the probability of `x` is `ν x`, and items are
    restricted to a prefix-free set.

## Setting

A dataset item is a finite string of any length (equivalently a pair (length, content): a
string determines its length, so the item type is `List Bool`, which is in bijection with
`Σ n, {x : List Bool // x.length = n}` by `Equiv.sigmaFiberEquiv`).

* `lam n` — the probability that an item has length `n` (any length distribution; it is the
  same for every model).
* `lenModel lam ν j x = lam |x| * ν j x` — model `j`'s probability of the item `x`: its length,
  then its content given its length.
* `contentModel ν j x = ν j x` — the content-given-length probability alone.

## Results

* `tsum_length_le_one` — the bridge: a semimeasure sums to at most one over the strings of each
  length `n`.
* `tsum_lenModel_le_one` — so each `lenModel lam ν j` sums to at most one over ALL strings.
* `pred_lenModel`, `excess_lenModel`, `excessAt_lenModel_ae_eq` — `lam` cancels: the conditioned
  predictor is `lam |a|` times the content predictor, and the excess log-loss is exactly the
  excess of the content-given-length predictor, with no `lam` in it.
* `hsi_rate_length` — the rate of `Rate.lean` for the content-given-length excess.
* `hsi_end_to_end_length` — the headline: spine theorem + rate, no prefix-free restriction.
* `hsi_end_to_end_length_enum` — the same for `Wood.enum` and any enumerable truth.
* `exists_iid_length_items` — the hypotheses are not vacuous.
* `rate_counterexample_length` — the `{0, 00}` example of `RateCounterexample.lean`, re-read
  with length-conditioning: the excess is exactly `0` at every position.
-/

namespace HsiLean.HsiRateLength

open MeasureTheory ProbabilityTheory Filter ENNReal Topology HsiLean.Rate HsiLean.HsiRate

/-! ## The bridge: semimeasures sum to at most one over the strings of each length -/

/-- **[UNAPPROVED STATEMENT]** The strings of length `n` form a prefix-free set. -/
theorem prefixFree_length (n : ℕ) : PrefixFree {x : List Bool | x.length = n} := by
  intro x hx y hy hxy
  exact hxy.eq_of_length (hx.trans hy.symm)

/-- **[UNAPPROVED STATEMENT]** The bridge: for every `n`, a semimeasure sums to at most one over
the strings of length `n`. -/
theorem tsum_length_le_one (μ : Semimeasure) (n : ℕ) :
    ∑' x : {x : List Bool // x.length = n}, μ x.1 ≤ 1 :=
  tsum_le_one_of_prefixFree μ (prefixFree_length n)

/-- A semimeasure gives every string mass at most one. -/
lemma apply_le_one (μ : Semimeasure) (x : List Bool) : μ x ≤ 1 :=
  (ENNReal.le_tsum (f := fun y : {y : List Bool // y.length = x.length} => μ y.1)
    ⟨x, rfl⟩).trans (tsum_length_le_one μ x.length)

/-- A sum over all strings, grouped by length. -/
lemma tsum_by_length (f : List Bool → ℝ≥0∞) :
    ∑' x, f x = ∑' n, ∑' x : {x : List Bool // x.length = n}, f x.1 := by
  rw [← (Equiv.sigmaFiberEquiv (List.length : List Bool → ℕ)).tsum_eq f, ENNReal.tsum_sigma']
  rfl

/-! ## The models -/

/-- The content-given-length probability: given that an item has `|x|` symbols, model `j` gives
content `x` probability `ν j x`. -/
noncomputable def contentModel (ν : ℕ → Semimeasure) : ℕ → List Bool → ℝ≥0∞ :=
  fun j x => ν j x

/-- Model `j`'s probability of the item `x`: the probability `lam |x|` of its length, times the
probability `ν j x` of its content given its length. The length distribution `lam` is the same
for every model. -/
noncomputable def lenModel (lam : ℕ → ℝ≥0∞) (ν : ℕ → Semimeasure) : ℕ → List Bool → ℝ≥0∞ :=
  fun j x => lam x.length * ν j x

/-- **[UNAPPROVED STATEMENT]** If the length probabilities sum to at most one, then
`x ↦ lam |x| * μ x` sums to at most one over ALL finite strings. This is the hypothesis
`model_sub` of `Rate.lean`, with no prefix-free restriction. -/
theorem tsum_lenModel_le_one (lam : ℕ → ℝ≥0∞) (hlam : ∑' n, lam n ≤ 1) (μ : Semimeasure) :
    ∑' x : List Bool, lam x.length * μ x ≤ 1 := by
  rw [tsum_by_length]
  refine le_trans (ENNReal.tsum_le_tsum fun n => ?_) hlam
  have e : ∀ x : {x : List Bool // x.length = n}, lam x.1.length * μ x.1 = lam n * μ x.1 :=
    fun x => by rw [x.2]
  rw [tsum_congr e, ENNReal.tsum_mul_left]
  calc lam n * ∑' x : {x : List Bool // x.length = n}, μ x.1
      ≤ lam n * 1 := mul_le_mul' le_rfl (tsum_length_le_one μ n)
    _ = lam n := mul_one _

/-! ## The length distribution cancels -/

/-- The probability of the lengths of an ordered dataset: `∏ᵢ lam |xᵢ|`. -/
noncomputable def lenW (lam : ℕ → ℝ≥0∞) (xs : List (List Bool)) : ℝ≥0∞ :=
  (xs.map fun x => lam x.length).prod

lemma lenW_append (lam : ℕ → ℝ≥0∞) (xs : List (List Bool)) (a : List Bool) :
    lenW lam (xs ++ [a]) = lenW lam xs * lam a.length := by
  simp [lenW]

lemma lenW_le_one {lam : ℕ → ℝ≥0∞} (h : ∀ n, lam n ≤ 1) (xs : List (List Bool)) :
    lenW lam xs ≤ 1 := by
  induction xs with
  | nil => simp [lenW]
  | cons a xs ih =>
    have e : lenW lam (a :: xs) = lam a.length * lenW lam xs := by simp [lenW]
    rw [e]
    calc lam a.length * lenW lam xs ≤ 1 * 1 := mul_le_mul' (h _) ih
      _ = 1 := one_mul 1

lemma lik_lenModel (lam : ℕ → ℝ≥0∞) (ν : ℕ → Semimeasure) (j : ℕ) (xs : List (List Bool)) :
    lik (lenModel lam ν) j xs = lenW lam xs * lik (contentModel ν) j xs := by
  induction xs with
  | nil => simp [lik, lenW]
  | cons a xs ih =>
    have e1 : lik (lenModel lam ν) j (a :: xs)
        = lenModel lam ν j a * lik (lenModel lam ν) j xs := by simp [lik]
    have e2 : lik (contentModel ν) j (a :: xs)
        = contentModel ν j a * lik (contentModel ν) j xs := by simp [lik]
    have e3 : lenW lam (a :: xs) = lam a.length * lenW lam xs := by simp [lenW]
    rw [e1, e2, e3, ih]
    simp only [lenModel, contentModel]
    ring

lemma mixL_lenModel (lam : ℕ → ℝ≥0∞) (ν : ℕ → Semimeasure) (w : ℕ → ℝ≥0∞)
    (xs : List (List Bool)) :
    mixL (lenModel lam ν) w xs = lenW lam xs * mixL (contentModel ν) w xs := by
  unfold mixL
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [lik_lenModel]
  ring

lemma lik_le_one_of_le {α : Type*} (P : ℕ → α → ℝ≥0∞) (hP : ∀ j a, P j a ≤ 1) (j : ℕ)
    (xs : List α) : lik P j xs ≤ 1 := by
  induction xs with
  | nil => simp [lik]
  | cons a xs ih =>
    have h : lik P j (a :: xs) = P j a * lik P j xs := by simp [lik]
    rw [h]
    calc P j a * lik P j xs ≤ 1 * 1 := mul_le_mul' (hP j a) ih
      _ = 1 := one_mul 1

lemma mixL_le_one_of_le {α : Type*} (P : ℕ → α → ℝ≥0∞) (w : ℕ → ℝ≥0∞) (hP : ∀ j a, P j a ≤ 1)
    (hw : ∑' j, w j ≤ 1) (xs : List α) : mixL P w xs ≤ 1 := by
  refine le_trans (ENNReal.tsum_le_tsum fun j => ?_) hw
  calc w j * lik P j xs ≤ w j * 1 := mul_le_mul' le_rfl (lik_le_one_of_le P hP j xs)
    _ = w j := mul_one _

/-- **[UNAPPROVED STATEMENT]** The length distribution cancels from the posterior: after a
dataset `xs` whose lengths all have positive (finite) probability, the conditioned predictor's
probability of a new item `a` is the probability `lam |a|` of its length times the
content-given-length predictor, which does not involve `lam`. -/
theorem pred_lenModel (lam : ℕ → ℝ≥0∞) (ν : ℕ → Semimeasure) (w : ℕ → ℝ≥0∞)
    (xs : List (List Bool)) (a : List Bool) (h0 : lenW lam xs ≠ 0) (ht : lenW lam xs ≠ ⊤) :
    pred (lenModel lam ν) w xs a = lam a.length * pred (contentModel ν) w xs a := by
  unfold pred
  rw [mixL_lenModel, mixL_lenModel, lenW_append, mul_assoc,
    ENNReal.mul_div_mul_left _ _ h0 ht, mul_div_assoc]

/-- **[UNAPPROVED STATEMENT]** The length distribution cancels from the excess: whenever the
true model gives the dataset `xs` followed by `a` positive probability (lengths and contents),
the excess log-loss of the conditioned predictor on `a` equals the excess log-loss of the
content-given-length predictor, relative to the true model's content-given-length probability.
`lam` does not appear on the right-hand side. -/
theorem excess_lenModel (lam : ℕ → ℝ≥0∞) (hlam : ∑' n, lam n ≤ 1) (ν : ℕ → Semimeasure)
    (w : ℕ → ℝ≥0∞) (hw : ∑' j, w j ≤ 1) {j₀ : ℕ} (hw0 : w j₀ ≠ 0)
    {xs : List (List Bool)} {a : List Bool}
    (hl : lik (lenModel lam ν) j₀ (xs ++ [a]) ≠ 0) :
    excess (lenModel lam ν) w j₀ xs a = excess (contentModel ν) w j₀ xs a := by
  have hlam1 : ∀ n, lam n ≤ 1 := fun n => (ENNReal.le_tsum n).trans hlam
  have hQ1 : ∀ j x, contentModel ν j x ≤ 1 := fun j x => apply_le_one (ν j) x
  rw [lik_lenModel, lenW_append, lik_append] at hl
  have h1 := mul_ne_zero_iff.mp hl
  obtain ⟨hL0, hla0⟩ := mul_ne_zero_iff.mp h1.1
  obtain ⟨hlx, hqa⟩ := mul_ne_zero_iff.mp h1.2
  have hLt : lenW lam xs ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (lenW_le_one hlam1 xs)
  have hlat : lam a.length ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (hlam1 _)
  have hqat : contentModel ν j₀ a ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (hQ1 _ _)
  have hlxa : lik (contentModel ν) j₀ (xs ++ [a]) ≠ 0 := by
    rw [lik_append]
    exact mul_ne_zero hlx hqa
  have hm0 := mixL_ne_zero (contentModel ν) w hw0 hlx
  have hm0' := mixL_ne_zero (contentModel ν) w hw0 hlxa
  have hmt : mixL (contentModel ν) w xs ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (mixL_le_one_of_le _ w hQ1 hw xs)
  have hmt' : mixL (contentModel ν) w (xs ++ [a]) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (mixL_le_one_of_le _ w hQ1 hw _)
  have hq0 : pred (contentModel ν) w xs a ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hm0', hmt⟩
  have hqt : pred (contentModel ν) w xs a ≠ ⊤ := ENNReal.div_ne_top hmt' hm0
  have r1 : (lam a.length).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hla0, hlat⟩
  have r2 : (contentModel ν j₀ a).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hqa, hqat⟩
  have r3 : (pred (contentModel ν) w xs a).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hq0, hqt⟩
  have e : lenModel lam ν j₀ a = lam a.length * contentModel ν j₀ a := rfl
  unfold excess
  rw [pred_lenModel lam ν w xs a hL0 hLt, e, ENNReal.toReal_mul, ENNReal.toReal_mul,
    Real.logb_mul r1 r2, Real.logb_mul r1 r3]
  ring

/-! ## The rate, length-conditioned -/

section Prob

variable [MeasurableSpace (List Bool)] [MeasurableSingletonClass (List Bool)]
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSingletonClass (List Bool)] in
/-- **[UNAPPROVED STATEMENT]** The hypotheses of `Rate.lean` hold for length-conditioned HSI:
items = all finite strings, models = `lenModel lam ν j` (length, then content given length),
weights = the hyperprior weights `w`, data = independent draws `X 0, X 1, …`, each with length
distributed by `lam` and content given length by `ν j₀`. -/
theorem iidFromModel_lenModel (lam : ℕ → ℝ≥0∞) (hlam : ∑' n, lam n ≤ 1) (ν : ℕ → Semimeasure)
    (w : Weights) (j₀ : ℕ) (Pr : Measure Ω) (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = lam x.length * ν j₀ x) :
    IIDFromModel (lenModel lam ν) w.toFun j₀ Pr X :=
  ⟨fun j => tsum_lenModel_le_one lam hlam (ν j), w.tsum_le_one, (w.pos j₀).ne', hX, hind, hlaw⟩

/-- **[UNAPPROVED STATEMENT]** The length distribution cancels from the excess, almost surely:
on item `n`, the excess log-loss of the predictor built from the full item probabilities
`lam |x| * ν j x` equals the excess log-loss of the content-given-length predictor built from
`ν j x` alone. -/
theorem excessAt_lenModel_ae_eq (lam : ℕ → ℝ≥0∞) (hlam : ∑' n, lam n ≤ 1) (ν : ℕ → Semimeasure)
    (w : Weights) (j₀ : ℕ) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = lam x.length * ν j₀ x) (n : ℕ) :
    excessAt (lenModel lam ν) w.toFun j₀ X n
      =ᵐ[Pr] excessAt (contentModel ν) w.toFun j₀ X n := by
  have h := iidFromModel_lenModel lam hlam ν w j₀ Pr X hX hind hlaw
  filter_upwards [ae_lik_ne_zero h] with ω hω
  have hl := hω (n + 1)
  rw [dataPrefix_succ] at hl
  exact excess_lenModel lam hlam ν w.toFun w.tsum_le_one (w.pos j₀).ne' hl

/-- **[UNAPPROVED STATEMENT]** The rate of convergence for HSI over datasets, with item
probabilities conditioned on length. No prefix-free restriction.

Let `ν` be any family of semimeasures, `w` hyperprior weights, and `lam` a distribution over
lengths. Let `X 0, X 1, …` be independent random finite strings, each drawn by picking a length
`n` with probability `lam n` and then content `x` of that length with probability `ν j₀ x`.
Write `e n` for the excess log-loss (bits) of the conditioned content-given-length HSI predictor
on item `n`, having seen items `0, …, n-1`, relative to the true model `ν j₀`. (By
`excessAt_lenModel_ae_eq` this is also the excess for the full item probabilities: `lam`
cancels.) Then:

1. each `e n` has a finite expectation, and that expectation is `≥ 0`;
2. the expectations are summable, with total at most `-log₂ w j₀`;
3. for every `ε > 0`, at most `-log₂ w j₀ / ε` positions `n` have expected excess above `ε`;
4. the expected excess tends to `0` (`eq:hsi-convergence`). -/
theorem hsi_rate_length (lam : ℕ → ℝ≥0∞) (hlam : ∑' n, lam n ≤ 1) (ν : ℕ → Semimeasure)
    (w : Weights) (j₀ : ℕ) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = lam x.length * ν j₀ x) :
    (∀ n, Integrable (excessAt (contentModel ν) w.toFun j₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun j₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun j₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr) atTop (𝓝 0) := by
  have h := iidFromModel_lenModel lam hlam ν w j₀ Pr X hX hind hlaw
  have hae := fun n => excessAt_lenModel_ae_eq lam hlam ν w j₀ Pr X hX hind hlaw n
  have hd : ∀ n, ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr
      = ∫ ω, excessAt (lenModel lam ν) w.toFun j₀ X n ω ∂Pr :=
    fun n => (integral_congr_ae (hae n)).symm
  simp only [hd]
  exact ⟨fun n => ⟨(integrable_congr (hae n)).mp (integrable_excessAt h n),
      expected_excess_nonneg h n⟩,
    tsum_expected_excess_le h, fun ε hε => expected_excess_rate h hε, tendsto_expected_excess h⟩

/-! ## The headline -/

/-- **[UNAPPROVED STATEMENT]** HSI end to end, length-conditioned: no restriction on the strings.

Let `ν` be an effective enumeration of semimeasures in which every universal mixture appears
(the hypotheses of the spine theorem `thm:enums-of-ums=ums`), and `w` any admissible hyperprior
weights. Let `lam` be a distribution over lengths, and `X 0, X 1, …` independent random finite
strings, each drawn by picking a length `n` with probability `lam n` and then content `x` of
that length with probability `ν j₀ x`. Then

* the HSI mixture `∑ⱼ w j • ν j` is a universal mixture (by the spine theorem), and
* its content-given-length dataset predictor satisfies the rate of `hsi_rate_length`, with
  constant `-log₂ w j₀`. -/
theorem hsi_end_to_end_length (ν : ℕ → Semimeasure) (hν_enum : UniformlyEnumerable ν)
    (hν_univ : ContainsAllUniversalMixtures ν) (w : Weights)
    (lam : ℕ → ℝ≥0∞) (hlam : ∑' n, lam n ≤ 1)
    (j₀ : ℕ) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = lam x.length * ν j₀ x) :
    IsUniversalMixture (mixture ν w) ∧
    (∀ n, Integrable (excessAt (contentModel ν) w.toFun j₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun j₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun j₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (contentModel ν) w.toFun j₀ X n ω ∂Pr) atTop (𝓝 0) := by
  refine ⟨?_, hsi_rate_length lam hlam ν w j₀ Pr X hX hind hlaw⟩
  have hmem : mixture ν w ∈ MixtureClass ν := ⟨w, rfl⟩
  rw [Wood.mixtureClass_eq_universalMixtures' ν hν_enum hν_univ] at hmem
  exact hmem

/-- **[UNAPPROVED STATEMENT]** HSI end to end, length-conditioned, for the concrete enumeration
`Wood.enum` and an arbitrary enumerable truth.

Let `w` be any admissible hyperprior weights over `Wood.enum`, the enumeration of *all*
enumerable semimeasures. Let `μ` be any enumerable semimeasure, `lam` a distribution over
lengths, and `X 0, X 1, …` independent random finite strings, each drawn by picking a length `n`
with probability `lam n` and then content `x` of that length with probability `μ x`. Then the
HSI mixture is a universal mixture, and there is an index `j₀` with `Wood.enum j₀ = μ` (so
`w j₀ > 0`) for which the content-given-length dataset predictor satisfies the rate with
constant `-log₂ w j₀`. -/
theorem hsi_end_to_end_length_enum (w : Weights) (μ : Semimeasure) (hμ : μ.Enumerable)
    (lam : ℕ → ℝ≥0∞) (hlam : ∑' n, lam n ≤ 1)
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = lam x.length * μ x) :
    IsUniversalMixture (mixture Wood.enum w) ∧
    ∃ j₀, Wood.enum j₀ = μ ∧ 0 < w.toFun j₀ ∧
    (∀ n, Integrable (excessAt (contentModel Wood.enum) w.toFun j₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (contentModel Wood.enum) w.toFun j₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (contentModel Wood.enum) w.toFun j₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (contentModel Wood.enum) w.toFun j₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun j₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (contentModel Wood.enum) w.toFun j₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω, excessAt (contentModel Wood.enum) w.toFun j₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun j₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (contentModel Wood.enum) w.toFun j₀ X n ω ∂Pr)
      atTop (𝓝 0) := by
  obtain ⟨j₀, rfl⟩ := Wood.enum_complete μ hμ
  exact ⟨⟨Wood.enum, w, Wood.enum_uniformlyEnumerable, Wood.enum_complete, rfl⟩, j₀, rfl,
    w.pos j₀, hsi_rate_length lam hlam Wood.enum w j₀ Pr X hX hind hlaw⟩

/-- **[UNAPPROVED STATEMENT]** The hypotheses are not vacuous: whenever `lam` is a probability
distribution over lengths and the semimeasure `μ` is a probability distribution on the strings
of each length (`∑_{|x| = n} μ x = 1` for every `n`, i.e. `μ` is a measure), there is a
probability space carrying independent random strings, each drawn by picking a length from `lam`
and then content of that length from `μ`. -/
theorem exists_iid_length_items (lam : ℕ → ℝ≥0∞) (hlam : ∑' n, lam n = 1) (μ : Semimeasure)
    (hμ : ∀ n, ∑' x : {x : List Bool // x.length = n}, μ x.1 = 1) :
    ∃ Pr : Measure (ℕ → List Bool), IsProbabilityMeasure Pr ∧
      (∀ n, Measurable (fun ω : ℕ → List Bool => ω n)) ∧
      iIndepFun (fun n (ω : ℕ → List Bool) => ω n) Pr ∧
      ∀ n (x : List Bool),
        Pr ((fun ω : ℕ → List Bool => ω n) ⁻¹' {x}) = lam x.length * μ x := by
  have hsum : ∑' x : List Bool, lam x.length * μ x = 1 := by
    rw [tsum_by_length, ← hlam]
    refine tsum_congr fun n => ?_
    have e : ∀ x : {x : List Bool // x.length = n}, lam x.1.length * μ x.1 = lam n * μ x.1 :=
      fun x => by rw [x.2]
    rw [tsum_congr e, ENNReal.tsum_mul_left, hμ n, mul_one]
  obtain ⟨Pr, hPr, h⟩ := exists_iidFromModel (α := List Bool)
    (fun _ x => lam x.length * μ x) (fun j => if j = 0 then 1 else 0) 0
    (fun _ => hsum.le) (by simp) (by simp) hsum
  exact ⟨Pr, hPr, h.meas, h.indep, h.law⟩

end Prob

/-! ## The `{0, 00}` example of `RateCounterexample.lean`, re-read with length-conditioning

Items as in `RateCounterexample.lean`: `false` stands for the string `0` (length 1), `true` for
`00` (length 2). The data are sampled as there: each item with probability `1/2`. Read with
length-conditioning, this is: length 1 or 2 with probability `1/2` each, and the content is
certain given the length. The "true" model and the model concentrated on `000…` then make the
*same* content-given-length predictions (each gives `0` probability one at length 1 and `00`
probability one at length 2), so both give each item probability `1/2 * 1`. The models now sum
to at most one over the items, the rate theorem applies, and the excess is exactly `0`. -/

section Counterexample

open HsiLean.RateCounterexample

/-- The length distribution of the example: the items `0` (length 1) and `00` (length 2) have
length-probability `1/2` each. -/
noncomputable def cexLam : Bool → ℝ≥0∞ := fun _ => 2⁻¹

/-- The content-given-length probabilities of the example: models `0` (the truth) and `1` (the
machine that outputs `000…`) both give each item's content probability one given its length;
all other models are zero. -/
noncomputable def cexContent : ℕ → Bool → ℝ≥0∞ := fun j _ => if j < 2 then 1 else 0

/-- The length-conditioned item probabilities of the example: length, then content given
length. -/
noncomputable def cexLenP : ℕ → Bool → ℝ≥0∞ := fun j a => cexLam a * cexContent j a

lemma cexLenP_apply (j : ℕ) (a : Bool) : cexLenP j a = if j < 2 then 2⁻¹ else 0 := by
  by_cases hj : j < 2 <;> simp [cexLenP, cexLam, cexContent, hj]

/-- **[UNAPPROVED STATEMENT]** The sampling distribution is the one of
`RateCounterexample.lean`: the true model gives each of the two items probability `1/2`. -/
theorem cexLenP_zero : cexLenP 0 = cexP 0 := by
  funext a
  simp [cexLenP_apply, cexP]

/-- **[UNAPPROVED STATEMENT]** Under length-conditioning every model of the example sums to at
most one over the items, so `model_sub` (the hypothesis that failed in
`RateCounterexample.lean`) holds. -/
theorem tsum_cexLenP_le_one (j : ℕ) : ∑' a, cexLenP j a ≤ 1 := by
  by_cases hj : j < 2
  · simp [cexLenP_apply, hj, tsum_fintype]
  · simp [cexLenP_apply, hj]

lemma lik_cexLenP (j : ℕ) (hj : j < 2) (xs : List Bool) :
    lik cexLenP j xs = 2⁻¹ ^ xs.length := by
  induction xs with
  | nil => simp [lik]
  | cons a xs ih =>
    have h : lik cexLenP j (a :: xs) = cexLenP j a * lik cexLenP j xs := by simp [lik]
    rw [h, ih, List.length_cons, pow_succ', cexLenP_apply, if_pos hj]

lemma mixL_cexLen (xs : List Bool) : mixL cexLenP cexW xs = 2⁻¹ ^ xs.length := by
  unfold mixL
  rw [tsum_eq_sum (s := Finset.range 2) (fun j hj => by simp_all [cexW])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [lik_cexLenP 0 (by norm_num), lik_cexLenP 1 (by norm_num)]
  have e0 : cexW 0 = 2⁻¹ := by simp [cexW]
  have e1 : cexW 1 = 2⁻¹ := by simp [cexW]
  rw [e0, e1, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- **[UNAPPROVED STATEMENT]** In the example read with length-conditioning, the excess log-loss
is exactly `0`: after any dataset `xs`, on any new item `a`. -/
theorem excess_cexLen (xs : List Bool) (a : Bool) : excess cexLenP cexW 0 xs a = 0 := by
  have h1 : (cexLenP 0 a).toReal = 2⁻¹ := by simp [cexLenP_apply]
  have h2 : (pred cexLenP cexW xs a).toReal = 2⁻¹ := by
    unfold pred
    rw [mixL_cexLen, mixL_cexLen, List.length_append, List.length_singleton, pow_succ,
      ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    have hp : ((2 : ℝ≥0∞).toReal⁻¹) ^ xs.length ≠ 0 := by simp
    rw [mul_div_assoc, mul_div_cancel₀ _ hp]
    simp
  unfold excess
  rw [h1, h2, sub_self]

/-- **[UNAPPROVED STATEMENT]** The `{0, 00}` example, re-read with length-conditioning. There is
a probability space with an i.i.d. sequence of items sampled exactly as in
`RateCounterexample.rate_counterexample` (each item with probability `1/2`); every model now
sums to at most one over the items; and the expected excess log-loss is `0` at every position
(so it tends to `0`, not to `-1`). -/
theorem rate_counterexample_length :
    ∃ (Pr : Measure (ℕ → Bool)) (X : ℕ → (ℕ → Bool) → Bool), IsProbabilityMeasure Pr ∧
      (∀ j, ∑' a, cexLenP j a ≤ 1) ∧
      (∀ ν, Measurable (X ν)) ∧
      iIndepFun X Pr ∧
      (∀ ν a, Pr (X ν ⁻¹' {a}) = cexP 0 a) ∧
      (∀ ν a, Pr (X ν ⁻¹' {a}) = cexLenP 0 a) ∧
      (∀ ν, ∫ ω, excessAt cexLenP cexW 0 X ν ω ∂Pr = 0) ∧
      Tendsto (fun ν => ∫ ω, excessAt cexLenP cexW 0 X ν ω ∂Pr) atTop (𝓝 0) := by
  obtain ⟨Pr, hPr, hm, hi, hl⟩ := exists_iid_cex
  have h0 : ∀ ν, ∫ ω, excessAt cexLenP cexW 0 (fun ν (ω : ℕ → Bool) => ω ν) ν ω ∂Pr = 0 := by
    intro ν
    simp [excessAt, excess_cexLen]
  refine ⟨Pr, fun ν ω => ω ν, hPr, tsum_cexLenP_le_one, hm, hi, hl, ?_, h0, ?_⟩
  · intro ν a
    rw [hl, cexLenP_zero]
  · simp only [h0]
    exact tendsto_const_nhds

end Counterexample

end HsiLean.HsiRateLength

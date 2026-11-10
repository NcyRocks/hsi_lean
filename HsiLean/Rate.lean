-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-10 and has NOT been reviewed by Nathan.
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# A convergence rate for HSI over datasets (`eq:hsi-convergence`)

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-10. Not reviewed by Nathan.

Source: `paper/ALT format.tex`, §"Optimality properties" (`eq:hsi-error-bound`,
`eq:hsi-average-error-bound`, `eq:hsi-convergence`), and the 2026-09-07 TODO sketch under
`eq:hsi-convergence` in the arXiv source.

## Setting (the level of abstraction)

* `α` — the type of data items (the paper: finite binary strings `x_ν`). Countable.
* `P j a` — the probability that the `j`-th model gives to item `a` (the paper: `P_{U_j}(x)`).
  Each `P j` is a *sub*-probability mass function: `∑' a, P j a ≤ 1`.
* `w j` — the hyperprior weight of model `j` (the paper: `Η(U_j)`), with `∑' j, w j ≤ 1`.
* `j₀` — the index of the true model (the paper: `U_μ`), with `w j₀ ≠ 0`.
* `lik P j xs` — `P_{U_j}(X) = ∏ P_{U_j}(x_i)` for an ordered dataset `xs`.
* `mixL P w xs` — `P_Η(X) = ∑_j Η(U_j) P_{U_j}(X)`.
* `pred P w xs a` — the conditioned predictor `P_{Η(·|X)}(a) = P_Η(X, a) / P_Η(X)`.
* `excess P w j₀ xs a` — the excess log-loss, in bits, of that predictor on the new item `a`,
  relative to the true model: `-log₂ (P_{Η(·|X)}(a) / P_{U_μ}(a))`.

The probabilistic statements take an arbitrary probability space `(Ω, ℙ)` carrying an i.i.d.
sequence `X ν : Ω → α` whose law is `P j₀`.
-/

namespace HsiLean.Rate

open MeasureTheory ProbabilityTheory Filter ENNReal Topology

variable {α : Type*}

/-- The first `n` items of the data sequence `x`, as an ordered dataset. -/
def dataPrefix (x : ℕ → α) (n : ℕ) : List α := List.ofFn fun i : Fin n => x i

variable (P : ℕ → α → ℝ≥0∞) (w : ℕ → ℝ≥0∞)

/-- The probability model `j` gives to the ordered dataset `xs`: `P_{U_j}(X) = ∏ᵢ P_{U_j}(xᵢ)`. -/
noncomputable def lik (j : ℕ) (xs : List α) : ℝ≥0∞ := (xs.map (P j)).prod

/-- The mixture's probability of the dataset: `P_Η(X) = ∑_j Η(U_j) P_{U_j}(X)`. -/
noncomputable def mixL (xs : List α) : ℝ≥0∞ := ∑' j, w j * lik P j xs

/-- The conditioned predictor: `P_{Η(·|X)}(a) = P_Η(X, a) / P_Η(X)`. -/
noncomputable def pred (xs : List α) (a : α) : ℝ≥0∞ := mixL P w (xs ++ [a]) / mixL P w xs

/-- Excess log-loss (bits) of the conditioned predictor on a new item `a`, relative to model `j₀`:
`-log₂ (P_{Η(·|X)}(a) / P_{U_μ}(a)) = log₂ P_{U_μ}(a) - log₂ P_{Η(·|X)}(a)`. -/
noncomputable def excess (j₀ : ℕ) (xs : List α) (a : α) : ℝ :=
  Real.logb 2 (P j₀ a).toReal - Real.logb 2 (pred P w xs a).toReal

/-- Excess log-loss (bits) of the mixture on the whole dataset, relative to model `j₀`:
`-log₂ (P_Η(X) / P_{U_μ}(X))`. -/
noncomputable def totalExcess (j₀ : ℕ) (xs : List α) : ℝ :=
  Real.logb 2 (lik P j₀ xs).toReal - Real.logb 2 (mixL P w xs).toReal

/-! ## Deterministic part: chain rule and the pointwise bound -/

lemma dataPrefix_succ (x : ℕ → α) (n : ℕ) :
    dataPrefix x (n + 1) = dataPrefix x n ++ [x n] := by
  unfold dataPrefix
  rw [List.ofFn_succ', List.concat_eq_append]
  congr

lemma dataPrefix_zero (x : ℕ → α) : dataPrefix x 0 = [] := by
  simp [dataPrefix]

lemma lik_nil (j : ℕ) : lik P j ([] : List α) = 1 := by simp [lik]

lemma lik_append (j : ℕ) (xs : List α) (a : α) :
    lik P j (xs ++ [a]) = lik P j xs * P j a := by
  simp [lik]

lemma P_le_one (hP : ∀ j, ∑' a, P j a ≤ 1) (j : ℕ) (a : α) : P j a ≤ 1 :=
  (ENNReal.le_tsum a).trans (hP j)

lemma lik_le_one (hP : ∀ j, ∑' a, P j a ≤ 1) (j : ℕ) (xs : List α) : lik P j xs ≤ 1 := by
  induction xs with
  | nil => simp [lik]
  | cons a xs ih =>
    have h : lik P j (a :: xs) = P j a * lik P j xs := by simp [lik]
    rw [h]
    calc P j a * lik P j xs ≤ 1 * 1 := mul_le_mul' (P_le_one P hP j a) ih
      _ = 1 := one_mul 1

lemma mixL_le_one (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (xs : List α) :
    mixL P w xs ≤ 1 := by
  refine le_trans (ENNReal.tsum_le_tsum fun j => ?_) hw
  calc w j * lik P j xs ≤ w j * 1 := mul_le_mul' le_rfl (lik_le_one P hP j xs)
    _ = w j := mul_one _

lemma le_mixL (j : ℕ) (xs : List α) : w j * lik P j xs ≤ mixL P w xs :=
  ENNReal.le_tsum j

lemma mixL_ne_zero {j₀ : ℕ} (hw0 : w j₀ ≠ 0) {xs : List α} (hl : lik P j₀ xs ≠ 0) :
    mixL P w xs ≠ 0 := by
  intro h
  have := le_mixL P w j₀ xs
  rw [h, le_zero_iff, mul_eq_zero] at this
  exact this.elim hw0 hl

lemma mixL_ne_top (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (xs : List α) :
    mixL P w xs ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (mixL_le_one P w hP hw xs)

lemma lik_ne_top (hP : ∀ j, ∑' a, P j a ≤ 1) (j : ℕ) (xs : List α) : lik P j xs ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (lik_le_one P hP j xs)

/-- One step of the chain rule: the per-item excess is the increment of the dataset excess. -/
lemma excess_eq_sub (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {j₀ : ℕ} (hw0 : w j₀ ≠ 0)
    {xs : List α} {a : α} (hl : lik P j₀ (xs ++ [a]) ≠ 0) :
    excess P w j₀ xs a = totalExcess P w j₀ (xs ++ [a]) - totalExcess P w j₀ xs := by
  have hl' := hl
  rw [lik_append, mul_ne_zero_iff] at hl'
  obtain ⟨hlx, hpa⟩ := hl'
  have hm0 := mixL_ne_zero P w hw0 hlx
  have hm0' := mixL_ne_zero P w hw0 hl
  have hmt := mixL_ne_top P w hP hw xs
  have hmt' := mixL_ne_top P w hP hw (xs ++ [a])
  have hlt := lik_ne_top P hP j₀ xs
  have hpt : P j₀ a ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (P_le_one P hP j₀ a)
  have r1 : (mixL P w xs).toReal ≠ 0 := (ENNReal.toReal_ne_zero).mpr ⟨hm0, hmt⟩
  have r2 : (mixL P w (xs ++ [a])).toReal ≠ 0 := (ENNReal.toReal_ne_zero).mpr ⟨hm0', hmt'⟩
  have r3 : (lik P j₀ xs).toReal ≠ 0 := (ENNReal.toReal_ne_zero).mpr ⟨hlx, hlt⟩
  have r4 : (P j₀ a).toReal ≠ 0 := (ENNReal.toReal_ne_zero).mpr ⟨hpa, hpt⟩
  unfold excess totalExcess pred
  rw [lik_append, ENNReal.toReal_div, ENNReal.toReal_mul, Real.logb_div r2 r1,
    Real.logb_mul r3 r4]
  ring

/-- **[UNAPPROVED STATEMENT]** The chain rule over *sequences* (step (1) of the sketch; the
identity the paper uses implicitly). For any data sequence `x` whose first `n` items all have
positive probability under the true model `j₀`, the per-item excess losses of the conditioned
predictor add up to the dataset excess loss, minus the constant `totalExcess P w j₀ []`
(which is `-log₂ ∑_j w_j`, and so is `0` when the hyperprior weights sum to exactly one). -/
theorem sum_excess_eq_totalExcess (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {j₀ : ℕ}
    (hw0 : w j₀ ≠ 0) (x : ℕ → α) (n : ℕ) (hl : lik P j₀ (dataPrefix x n) ≠ 0) :
    ∑ ν ∈ Finset.range n, excess P w j₀ (dataPrefix x ν) (x ν)
      = totalExcess P w j₀ (dataPrefix x n) - totalExcess P w j₀ [] := by
  induction n with
  | zero => simp [dataPrefix_zero]
  | succ n ih =>
    rw [dataPrefix_succ] at hl
    have hl' := hl
    rw [lik_append, mul_ne_zero_iff] at hl'
    rw [Finset.sum_range_succ, ih hl'.1, excess_eq_sub P w hP hw hw0 hl, dataPrefix_succ]
    ring

/-- The empty dataset has excess `-log₂ ∑_j w_j ≥ 0`. -/
lemma totalExcess_nil_nonneg (hw : ∑' j, w j ≤ 1) (j₀ : ℕ) :
    0 ≤ totalExcess P w j₀ ([] : List α) := by
  have h1 : mixL P w ([] : List α) = ∑' j, w j := by simp [mixL, lik]
  unfold totalExcess
  rw [h1, lik_nil]
  have : Real.logb 2 (∑' j, w j).toReal ≤ 0 := by
    apply Real.logb_nonpos (by norm_num) ENNReal.toReal_nonneg
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hw)
  simp only [ENNReal.toReal_one, Real.logb_one]
  linarith

/-- **[UNAPPROVED STATEMENT]** The pointwise bound `eq:hsi-error-bound`, with `≤` in place of the
paper's `<`: for every ordered dataset `xs` to which the true model `j₀` gives positive
probability, the mixture's excess log-loss on `xs` is at most `-log₂ w_{j₀}`, whatever the size
of `xs`. -/
theorem totalExcess_le (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {j₀ : ℕ}
    (hw0 : w j₀ ≠ 0) (xs : List α) (hl : lik P j₀ xs ≠ 0) :
    totalExcess P w j₀ xs ≤ -Real.logb 2 (w j₀).toReal := by
  have hwt : w j₀ ≠ ⊤ := ne_top_of_le_ne_top one_ne_top ((ENNReal.le_tsum j₀).trans hw)
  have hlt := lik_ne_top P hP j₀ xs
  have r1 : 0 < (w j₀).toReal := ENNReal.toReal_pos hw0 hwt
  have r2 : 0 < (lik P j₀ xs).toReal := ENNReal.toReal_pos hl hlt
  have h := ENNReal.toReal_mono (mixL_ne_top P w hP hw xs) (le_mixL P w j₀ xs)
  rw [ENNReal.toReal_mul] at h
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos r1 r2) h
  rw [Real.logb_mul r1.ne' r2.ne'] at h2
  unfold totalExcess
  linarith

/-- **[UNAPPROVED STATEMENT]** Chain rule + pointwise bound: along any data sequence whose first
`n` items have positive probability under the true model, the *sum* of the first `n` per-item
excess losses is at most `-log₂ w_{j₀}` — a constant that does not depend on `n`. -/
theorem sum_excess_le (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {j₀ : ℕ}
    (hw0 : w j₀ ≠ 0) (x : ℕ → α) (n : ℕ) (hl : lik P j₀ (dataPrefix x n) ≠ 0) :
    ∑ ν ∈ Finset.range n, excess P w j₀ (dataPrefix x ν) (x ν)
      ≤ -Real.logb 2 (w j₀).toReal := by
  rw [sum_excess_eq_totalExcess P w hP hw hw0 x n hl]
  have := totalExcess_le P w hP hw hw0 _ hl
  have := totalExcess_nil_nonneg P w hw j₀
  linarith

end HsiLean.Rate

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

/-! ## Deterministic helpers for the expectation step -/

lemma lik_dataPrefix_ne_zero {j₀ : ℕ} (x : ℕ → α) (hx : ∀ ν, P j₀ (x ν) ≠ 0) (n : ℕ) :
    lik P j₀ (dataPrefix x n) ≠ 0 := by
  induction n with
  | zero => simp [dataPrefix_zero, lik_nil]
  | succ n ih =>
    rw [dataPrefix_succ, lik_append]
    exact mul_ne_zero ih (hx n)

/-- The conditioned predictor is a sub-probability mass function on items. This is where the
hypothesis `∑' a, P j a ≤ 1` is used. -/
lemma tsum_pred_le_one (hP : ∀ j, ∑' a, P j a ≤ 1) (xs : List α) :
    ∑' a, pred P w xs a ≤ 1 := by
  have h : ∑' a, mixL P w (xs ++ [a]) ≤ mixL P w xs := by
    unfold mixL
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum fun j => ?_
    simp only [lik_append]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    calc w j * (lik P j xs * ∑' a, P j a)
        ≤ w j * (lik P j xs * 1) := mul_le_mul' le_rfl (mul_le_mul' le_rfl (hP j))
      _ = w j * lik P j xs := by rw [mul_one]
  unfold pred
  simp only [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right]
  calc (∑' a, mixL P w (xs ++ [a])) * (mixL P w xs)⁻¹
      ≤ mixL P w xs * (mixL P w xs)⁻¹ := mul_le_mul' h le_rfl
    _ ≤ 1 := ENNReal.mul_inv_le_one _

lemma div_mul_le' (a b : ℝ≥0∞) : a / b * b ≤ a := by
  by_cases h0 : b = 0
  · simp [h0]
  by_cases ht : b = ⊤
  · simp [ht]
  · exact (ENNReal.div_mul_cancel h0 ht).le

/-- `-log₂ y ≥ (1 - y) / ln 2`, applied to `y = P_{Η(·|X)}(a) / P_{U_μ}(a)`. -/
lemma excess_ge (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {j₀ : ℕ} (hw0 : w j₀ ≠ 0)
    {xs : List α} {a : α} (hl : lik P j₀ (xs ++ [a]) ≠ 0) :
    (1 - (pred P w xs a / P j₀ a).toReal) / Real.log 2 ≤ excess P w j₀ xs a := by
  have hl' := hl
  rw [lik_append, mul_ne_zero_iff] at hl'
  obtain ⟨hlx, hpa⟩ := hl'
  have hm0 := mixL_ne_zero P w hw0 hlx
  have hm0' := mixL_ne_zero P w hw0 hl
  have hmt := mixL_ne_top P w hP hw xs
  have hmt' := mixL_ne_top P w hP hw (xs ++ [a])
  have hpt : P j₀ a ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (P_le_one P hP j₀ a)
  have hq0 : pred P w xs a ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hm0', hmt⟩
  have hqt : pred P w xs a ≠ ⊤ := ENNReal.div_ne_top hmt' hm0
  have hq : 0 < (pred P w xs a).toReal := ENNReal.toReal_pos hq0 hqt
  have hp : 0 < (P j₀ a).toReal := ENNReal.toReal_pos hpa hpt
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have e1 : excess P w j₀ xs a
      = -Real.log ((pred P w xs a).toReal / (P j₀ a).toReal) / Real.log 2 := by
    unfold excess
    rw [Real.log_div hq.ne' hp.ne']
    simp only [Real.logb]
    ring
  rw [e1, ENNReal.toReal_div]
  exact div_le_div_of_nonneg_right (by linarith) hlog2.le

/-- A sequence of non-negative reals whose partial sums are all `≤ C` exceeds `ε` at most
`C / ε` times. -/
lemma count_le_of_sum_le {d : ℕ → ℝ} {C ε : ℝ} (hd : ∀ ν, 0 ≤ d ν)
    (hsum : ∀ n, ∑ ν ∈ Finset.range n, d ν ≤ C) (hε : 0 < ε) :
    {ν | ε < d ν}.Finite ∧ ({ν | ε < d ν}.ncard : ℝ) ≤ C / ε := by
  have key : ∀ t : Finset ℕ, (↑t : Set ℕ) ⊆ {ν | ε < d ν} → (t.card : ℝ) * ε ≤ C := by
    intro t ht
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range t
    calc (t.card : ℝ) * ε = ∑ _ν ∈ t, ε := by simp
      _ ≤ ∑ ν ∈ t, d ν := Finset.sum_le_sum fun ν hν => (ht hν).le
      _ ≤ ∑ ν ∈ Finset.range n, d ν :=
        Finset.sum_le_sum_of_subset_of_nonneg hn fun ν _ _ => hd ν
      _ ≤ C := hsum n
  have hfin : {ν | ε < d ν}.Finite := by
    by_contra hinf
    obtain ⟨m, hm⟩ := exists_nat_gt (C / ε)
    obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf m
    have h1 := key t ht
    rw [hcard] at h1
    rw [div_lt_iff₀ hε] at hm
    linarith
  refine ⟨hfin, ?_⟩
  rw [le_div_iff₀ hε]
  have h2 := key hfin.toFinset (by simp)
  rwa [← Set.ncard_eq_toFinset_card _ hfin] at h2

/-! ## Probabilistic part: i.i.d. items from the true model -/

section Prob

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Tonelli + independence. If `Y` is independent of `H`, has mass function `p`, and `q h` is a
sub-probability mass function for each `h`, then multiplying by the likelihood ratio
`q (H) (Y) / p (Y)` does not increase a lower integral. -/
lemma lintegral_mul_ratio_le {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    [Countable β] (Pr : Measure Ω) [IsProbabilityMeasure Pr] {H : Ω → β} {Y : Ω → α}
    (hH : Measurable H) (hY : Measurable Y) (hind : IndepFun H Y Pr)
    (p : α → ℝ≥0∞) (hp : ∀ a, Pr (Y ⁻¹' {a}) = p a)
    (q : β → α → ℝ≥0∞) (hq : ∀ h, ∑' a, q h a ≤ 1) (g : β → ℝ≥0∞) :
    ∫⁻ ω, g (H ω) * (q (H ω) (Y ω) / p (Y ω)) ∂Pr ≤ ∫⁻ ω, g (H ω) ∂Pr := by
  let f : β × α → ℝ≥0∞ := fun z => g z.1 * (q z.1 z.2 / p z.2)
  have hfm : Measurable f := measurable_of_countable f
  have hpair : Measurable fun ω => (H ω, Y ω) := hH.prodMk hY
  have h1 : ∫⁻ ω, g (H ω) * (q (H ω) (Y ω) / p (Y ω)) ∂Pr
      = ∫⁻ z, f z ∂(Pr.map fun ω => (H ω, Y ω)) := (lintegral_map hfm hpair).symm
  haveI : IsProbabilityMeasure (Pr.map H) := Measure.isProbabilityMeasure_map hH.aemeasurable
  haveI : IsProbabilityMeasure (Pr.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hH.aemeasurable hY.aemeasurable).mp hind,
    lintegral_prod _ hfm.aemeasurable]
  have h2 : ∫⁻ h, g h ∂(Pr.map H) = ∫⁻ ω, g (H ω) ∂Pr :=
    lintegral_map (measurable_of_countable g) hH
  rw [← h2]
  refine lintegral_mono fun h => ?_
  have h3 : ∫⁻ a, q h a / p a ∂(Pr.map Y) ≤ 1 := by
    rw [lintegral_countable']
    refine le_trans (ENNReal.tsum_le_tsum fun a => ?_) (hq h)
    rw [Measure.map_apply hY (measurableSet_singleton a), hp a]
    exact div_mul_le' _ _
  calc ∫⁻ a, f (h, a) ∂(Pr.map Y)
      = g h * ∫⁻ a, q h a / p a ∂(Pr.map Y) := by
        change ∫⁻ a, g h * (q h a / p a) ∂(Pr.map Y) = _
        exact lintegral_const_mul _ (measurable_of_countable _)
    _ ≤ g h * 1 := mul_le_mul' le_rfl h3
    _ = g h := mul_one _

/-- The first `ν` items, as a random tuple. -/
def hist (X : ℕ → Ω → α) (ν : ℕ) (ω : Ω) : Fin ν → α := fun i => X i ω

lemma measurable_hist {X : ℕ → Ω → α} (hX : ∀ ν, Measurable (X ν)) (ν : ℕ) :
    Measurable (hist X ν) :=
  measurable_pi_lambda _ fun i => hX i

lemma indep_hist (Pr : Measure Ω) {X : ℕ → Ω → α} (hX : ∀ ν, Measurable (X ν))
    (hind : iIndepFun X Pr) (ν : ℕ) : IndepFun (hist X ν) (X ν) Pr := by
  have h := hind.indepFun_finset (Finset.range ν) {ν} (by simp) hX
  have hφ : Measurable (fun (g : (Finset.range ν) → α) (i : Fin ν) =>
      g ⟨i, Finset.mem_range.mpr i.isLt⟩) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hψ : Measurable (fun (g : ({ν} : Finset ℕ) → α) =>
      g ⟨ν, Finset.mem_singleton_self ν⟩) :=
    measurable_pi_apply _
  exact h.comp hφ hψ

/-- The hypotheses of the rate theorem, stated once.

* `model_sub`: every model is a sub-probability mass function on items.
* `weight_sub`: the hyperprior weights sum to at most one.
* `weight_pos`: the true model `j₀` has positive hyperprior weight.
* `meas`, `indep`, `law`: the items `X 0, X 1, …` are independent random variables, each
  distributed according to the true model `P j₀` (so `P j₀` is a genuine probability
  distribution: its values sum to exactly one). -/
structure IIDFromModel (P : ℕ → α → ℝ≥0∞) (w : ℕ → ℝ≥0∞) (j₀ : ℕ) (Pr : Measure Ω)
    (X : ℕ → Ω → α) : Prop where
  model_sub : ∀ j, ∑' a, P j a ≤ 1
  weight_sub : ∑' j, w j ≤ 1
  weight_pos : w j₀ ≠ 0
  meas : ∀ ν, Measurable (X ν)
  indep : iIndepFun X Pr
  law : ∀ ν a, Pr (X ν ⁻¹' {a}) = P j₀ a

/-- The excess log-loss (bits) of the conditioned predictor on the `ν`-th item, having seen
items `0, …, ν-1`: the random variable inside `eq:hsi-convergence`. -/
noncomputable def excessAt (j₀ : ℕ) (X : ℕ → Ω → α) (ν : ℕ) (ω : Ω) : ℝ :=
  excess P w j₀ (dataPrefix (fun i => X i ω) ν) (X ν ω)

/-- The likelihood ratio `P_{Η(·|x_{<ν})}(x_ν) / P_{U_μ}(x_ν)`. -/
noncomputable def ratioAt (j₀ : ℕ) (X : ℕ → Ω → α) (ν : ℕ) (ω : Ω) : ℝ≥0∞ :=
  pred P w (dataPrefix (fun i => X i ω) ν) (X ν ω) / P j₀ (X ν ω)

/-- The integrable lower bound `(1 - ratio) / ln 2` for `excessAt`. -/
noncomputable def lowerAt (j₀ : ℕ) (X : ℕ → Ω → α) (ν : ℕ) (ω : Ω) : ℝ :=
  (1 - (ratioAt P w j₀ X ν ω).toReal) / Real.log 2

variable {P w} {j₀ : ℕ} {Pr : Measure Ω} {X : ℕ → Ω → α}

lemma measurable_excessAt (hX : ∀ ν, Measurable (X ν)) (ν : ℕ) :
    Measurable (excessAt P w j₀ X ν) := by
  have hF : Measurable (fun z : (Fin ν → α) × α => excess P w j₀ (List.ofFn z.1) z.2) :=
    measurable_of_countable _
  exact hF.comp ((measurable_hist hX ν).prodMk (hX ν))

lemma measurable_ratioAt (hX : ∀ ν, Measurable (X ν)) (ν : ℕ) :
    Measurable (ratioAt P w j₀ X ν) := by
  have hF : Measurable
      (fun z : (Fin ν → α) × α => pred P w (List.ofFn z.1) z.2 / P j₀ z.2) :=
    measurable_of_countable _
  have e : ratioAt P w j₀ X ν
      = (fun z : (Fin ν → α) × α => pred P w (List.ofFn z.1) z.2 / P j₀ z.2)
        ∘ (fun ω => (hist X ν ω, X ν ω)) := by
    funext ω
    simp only [ratioAt, dataPrefix, Function.comp_apply]
    rfl
  rw [e]
  exact hF.comp ((measurable_hist hX ν).prodMk (hX ν))

lemma ae_P_ne_zero (hlaw : ∀ ν a, Pr (X ν ⁻¹' {a}) = P j₀ a) :
    ∀ᵐ ω ∂Pr, ∀ ν, P j₀ (X ν ω) ≠ 0 := by
  rw [ae_all_iff]
  intro ν
  rw [ae_iff]
  have hset : {ω | ¬ P j₀ (X ν ω) ≠ 0} = ⋃ a ∈ {a | P j₀ a = 0}, X ν ⁻¹' {a} := by
    ext ω
    simp
  rw [hset]
  refine (measure_biUnion_null_iff (Set.to_countable _)).mpr fun a ha => ?_
  rw [hlaw]
  exact ha

variable [IsProbabilityMeasure Pr]

lemma ae_lik_ne_zero (h : IIDFromModel P w j₀ Pr X) :
    ∀ᵐ ω ∂Pr, ∀ n, lik P j₀ (dataPrefix (fun i => X i ω) n) ≠ 0 := by
  filter_upwards [ae_P_ne_zero h.law] with ω hω n
  exact lik_dataPrefix_ne_zero P (fun i => X i ω) hω n

/-- The expected likelihood ratio is at most one. -/
lemma lintegral_ratioAt_le_one (h : IIDFromModel P w j₀ Pr X) (ν : ℕ) :
    ∫⁻ ω, ratioAt P w j₀ X ν ω ∂Pr ≤ 1 := by
  have key := lintegral_mul_ratio_le Pr (measurable_hist h.meas ν) (h.meas ν)
    (indep_hist Pr h.meas h.indep ν) (P j₀) (h.law ν)
    (fun hh a => pred P w (List.ofFn hh) a) (fun hh => tsum_pred_le_one P w h.model_sub _)
    (fun _ => 1)
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) (key.trans (by simp))
  exact (one_mul _).symm

lemma integrable_lowerAt (h : IIDFromModel P w j₀ Pr X) (ν : ℕ) :
    Integrable (lowerAt P w j₀ X ν) Pr := by
  have hne : ∫⁻ ω, ratioAt P w j₀ X ν ω ∂Pr ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (lintegral_ratioAt_le_one h ν)
  have hi := integrable_toReal_of_lintegral_ne_top (measurable_ratioAt h.meas ν).aemeasurable hne
  exact ((integrable_const (1 : ℝ)).sub hi).div_const _

lemma integral_lowerAt_nonneg (h : IIDFromModel P w j₀ Pr X) (ν : ℕ) :
    0 ≤ ∫ ω, lowerAt P w j₀ X ν ω ∂Pr := by
  have hle := lintegral_ratioAt_le_one h ν
  have hne : ∫⁻ ω, ratioAt P w j₀ X ν ω ∂Pr ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hle
  have hm := measurable_ratioAt (P := P) (w := w) (j₀ := j₀) h.meas ν
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hne
  have e : ∫ ω, lowerAt P w j₀ X ν ω ∂Pr
      = (1 - (∫⁻ ω, ratioAt P w j₀ X ν ω ∂Pr).toReal) / Real.log 2 := by
    unfold lowerAt
    rw [integral_div, integral_sub (integrable_const _) hi,
      integral_toReal hm.aemeasurable (ae_lt_top hm hne)]
    simp
  rw [e]
  have h1 : (∫⁻ ω, ratioAt P w j₀ X ν ω ∂Pr).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono one_ne_top hle
  exact div_nonneg (by linarith) (Real.log_nonneg (by norm_num))

lemma ae_lowerAt_le (h : IIDFromModel P w j₀ Pr X) :
    ∀ᵐ ω ∂Pr, ∀ ν, lowerAt P w j₀ X ν ω ≤ excessAt P w j₀ X ν ω := by
  filter_upwards [ae_lik_ne_zero h] with ω hω ν
  have hl := hω (ν + 1)
  rw [dataPrefix_succ] at hl
  exact excess_ge P w h.model_sub h.weight_sub h.weight_pos hl

lemma ae_sum_excessAt_le (h : IIDFromModel P w j₀ Pr X) :
    ∀ᵐ ω ∂Pr, ∀ n, ∑ ν ∈ Finset.range n, excessAt P w j₀ X ν ω
      ≤ -Real.logb 2 (w j₀).toReal := by
  filter_upwards [ae_lik_ne_zero h] with ω hω n
  exact sum_excess_le P w h.model_sub h.weight_sub h.weight_pos (fun i => X i ω) n (hω n)

/-- **[UNAPPROVED STATEMENT]** The excess log-loss on the `ν`-th item has a finite expectation.
(Needed for the expectations below to mean anything: Lean's integral of a non-integrable
function is `0` by convention.) -/
theorem integrable_excessAt (h : IIDFromModel P w j₀ Pr X) (ν : ℕ) :
    Integrable (excessAt P w j₀ X ν) Pr := by
  set C : ℝ := -Real.logb 2 (w j₀).toReal
  have hg : Integrable (fun ω => |lowerAt P w j₀ X ν ω|
      + |C - ∑ k ∈ Finset.range ν, lowerAt P w j₀ X k ω|) Pr :=
    (integrable_lowerAt h ν).abs.add
      ((integrable_const C).sub (integrable_finsetSum _ fun k _ => integrable_lowerAt h k)).abs
  refine hg.mono' (measurable_excessAt h.meas ν).aestronglyMeasurable ?_
  filter_upwards [ae_lowerAt_le h, ae_sum_excessAt_le h] with ω hlow hsum
  have h1 := hsum (ν + 1)
  rw [Finset.sum_range_succ] at h1
  have h2 : ∑ k ∈ Finset.range ν, lowerAt P w j₀ X k ω
      ≤ ∑ k ∈ Finset.range ν, excessAt P w j₀ X k ω :=
    Finset.sum_le_sum fun k _ => hlow k
  have h3 := hlow ν
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [neg_abs_le (lowerAt P w j₀ X ν ω),
      abs_nonneg (C - ∑ k ∈ Finset.range ν, lowerAt P w j₀ X k ω)]
  · linarith [le_abs_self (C - ∑ k ∈ Finset.range ν, lowerAt P w j₀ X k ω),
      abs_nonneg (lowerAt P w j₀ X ν ω)]

/-- **[UNAPPROVED STATEMENT]** Step (2) of the sketch: the expected excess log-loss on each new
item is non-negative (it is an expected KL divergence from the true model to the conditioned
predictor, which is a sub-probability mass function). -/
theorem expected_excess_nonneg (h : IIDFromModel P w j₀ Pr X) (ν : ℕ) :
    0 ≤ ∫ ω, excessAt P w j₀ X ν ω ∂Pr := by
  refine (integral_lowerAt_nonneg h ν).trans ?_
  refine integral_mono_ae (integrable_lowerAt h ν) (integrable_excessAt h ν) ?_
  filter_upwards [ae_lowerAt_le h] with ω hω
  exact hω ν

/-- **[UNAPPROVED STATEMENT]** The expected *total* excess log-loss over the first `n` items is
at most `-log₂ w_{j₀}`, for every `n` (`eq:hsi-error-bound` in expectation, split by the chain
rule into its `n` per-item terms). -/
theorem sum_expected_excess_le (h : IIDFromModel P w j₀ Pr X) (n : ℕ) :
    ∑ ν ∈ Finset.range n, ∫ ω, excessAt P w j₀ X ν ω ∂Pr ≤ -Real.logb 2 (w j₀).toReal := by
  rw [← integral_finsetSum _ fun ν _ => integrable_excessAt h ν]
  have hle : ∫ ω, ∑ ν ∈ Finset.range n, excessAt P w j₀ X ν ω ∂Pr
      ≤ ∫ _ω, -Real.logb 2 (w j₀).toReal ∂Pr := by
    refine integral_mono_ae (integrable_finsetSum _ fun ν _ => integrable_excessAt h ν)
      (integrable_const _) ?_
    filter_upwards [ae_sum_excessAt_le h] with ω hω
    exact hω n
  simpa using hle

/-- **[UNAPPROVED STATEMENT]** The rate (step (3) of the sketch; the upgrade of the arrow in
`eq:hsi-convergence`). For every `ε > 0`, the set of positions `ν` at which the expected excess
log-loss of the conditioned predictor exceeds `ε` is finite, and has at most
`-log₂ w_{j₀} / ε` elements. The bound does not depend on the size of the dataset. -/
theorem expected_excess_rate (h : IIDFromModel P w j₀ Pr X) {ε : ℝ} (hε : 0 < ε) :
    {ν | ε < ∫ ω, excessAt P w j₀ X ν ω ∂Pr}.Finite ∧
      ({ν | ε < ∫ ω, excessAt P w j₀ X ν ω ∂Pr}.ncard : ℝ)
        ≤ -Real.logb 2 (w j₀).toReal / ε :=
  count_le_of_sum_le (expected_excess_nonneg h) (sum_expected_excess_le h) hε

/-- **[UNAPPROVED STATEMENT]** The expected excess losses are summable over all positions, with
total at most `-log₂ w_{j₀}`. -/
theorem tsum_expected_excess_le (h : IIDFromModel P w j₀ Pr X) :
    Summable (fun ν => ∫ ω, excessAt P w j₀ X ν ω ∂Pr) ∧
      ∑' ν, ∫ ω, excessAt P w j₀ X ν ω ∂Pr ≤ -Real.logb 2 (w j₀).toReal :=
  ⟨summable_of_sum_range_le (expected_excess_nonneg h) (sum_expected_excess_le h),
    Real.tsum_le_of_sum_range_le (expected_excess_nonneg h) (sum_expected_excess_le h)⟩

/-- **[UNAPPROVED STATEMENT]** The paper's `eq:hsi-convergence`, as a corollary of the rate: the
expected excess log-loss on the `ν`-th item tends to `0` as `ν → ∞`. -/
theorem tendsto_expected_excess (h : IIDFromModel P w j₀ Pr X) :
    Tendsto (fun ν => ∫ ω, excessAt P w j₀ X ν ω ∂Pr) atTop (𝓝 0) :=
  (tsum_expected_excess_le h).1.tendsto_atTop_zero

end Prob

end HsiLean.Rate

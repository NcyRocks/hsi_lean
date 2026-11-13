-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-13 and has NOT been reviewed by Nathan.
import HsiLean.Rate
import HsiLean.HsiMachines

/-!
# HSI out of distribution: the cost of a test item unlike the training data

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-13. Not reviewed by Nathan.

Source: `PIBBSS/notes/queue/aram-hsi-optimality-2026-11-13.md` (AI-derived research note),
§3.6 Proposition E and its proof in §7, and §6 candidates 1 and 2.

Vocabulary of `Rate.lean`: item models `P j`, hyperprior weights `w j`, `lik` (a model's
probability of a dataset), `mixL` (HSI's probability of a dataset), `pred` (trained HSI's
predictive probability of the next item), `excess P w j xs y` (trained HSI's log loss on `y`
minus model `j`'s log loss on `y`, in bits).

The comparison predictor ("fresh SolInd") is a NAMED MEMBER `j` of the class, as in the note's
proof (`U_{j_M}`). It cannot be replaced by the untrained mixture `mixL P w [·]` in the abstract
setting: a mixture of products does not dominate the product of mixtures. At the machine level
the two coincide (`hsi_ood_machines`): the untrained HSI prior IS `λ_U` for a UTM `U`, and `U` is
a member.

Throughout, the hypothesis on the models is only `∀ j a, P j a ≤ 1` (weaker than `Rate.lean`'s
`∑' a, P j a ≤ 1`), so that the results apply to `contentModel` (length-conditioned items).

## Results

* `ood_upper` — Proposition E: `excess j X y ≤ -log₂ w j + trainGain j X`.
* `ood_upper_attained` — equality when `j` is the only member giving `y` positive probability.
* `pred_offDistribution_le`, `ood_lower` — train on `n` copies of `a`, test on `b`: the penalty
  is at least `log₂(n+1) - C`.
* `ood_linear`, `example_ood_linear` — in a class where the upper bound is attained the penalty
  grows LINEARLY in `n`.
* `ood_upper_hedged`, `ood_upper_hedged_log`, `ood_offDistribution_upper` — if the class contains a model hedging
  between a model `k` and the comparison `j`, the penalty is at most
  `log₂(n+1) + 1/ln 2 + (cost of the hedge) + trainGain k X`: logarithmic when one model `k`
  explains the training data about as well as HSI does.
* `example_ood_log` — an explicit class with all hedges: the penalty there is `Θ(log n)`.
* `hsi_ood` — the main facts in one statement.
* `hsi_ood_machines` — Proposition E about machines, with "fresh SolInd" = the untrained HSI prior.
* `mixL_perm`, `card_mul_mixL_le_one` — HSI is exchangeable, hence cannot learn item order.
-/

open ENNReal
open HsiLean.Rate

namespace HsiLean.HsiOOD

variable {α : Type*} (P : ℕ → α → ℝ≥0∞) (w : ℕ → ℝ≥0∞)

/-- [UNAPPROVED STATEMENT] What HSI gained over model `j` on the training data `xs`, in bits:
`L(P j ^⊗, X) - L(P_Η, X) = log₂ P_Η(X) - log₂ P_j(X)`. It is `-totalExcess P w j xs`. -/
noncomputable def trainGain (j : ℕ) (xs : List α) : ℝ :=
  Real.logb 2 (mixL P w xs).toReal - Real.logb 2 (lik P j xs).toReal

lemma trainGain_eq_neg_totalExcess (j : ℕ) (xs : List α) :
    trainGain P w j xs = -totalExcess P w j xs := by
  unfold trainGain totalExcess; ring

/-! ## Basic bounds under `P j a ≤ 1` -/

lemma lik_le_one' (hP1 : ∀ j a, P j a ≤ 1) (j : ℕ) (xs : List α) : lik P j xs ≤ 1 := by
  induction xs with
  | nil => simp [lik]
  | cons a xs ih =>
    have h : lik P j (a :: xs) = P j a * lik P j xs := by simp [lik]
    rw [h]
    calc P j a * lik P j xs ≤ 1 * 1 := mul_le_mul' (hP1 j a) ih
      _ = 1 := one_mul 1

lemma mixL_le_one' (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (xs : List α) :
    mixL P w xs ≤ 1 := by
  refine le_trans (ENNReal.tsum_le_tsum fun j => ?_) hw
  calc w j * lik P j xs ≤ w j * 1 := mul_le_mul' le_rfl (lik_le_one' P hP1 j xs)
    _ = w j := mul_one _

lemma mixL_ne_top' (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (xs : List α) :
    mixL P w xs ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (mixL_le_one' P w hP1 hw xs)

lemma w_ne_top (hw : ∑' j, w j ≤ 1) (j : ℕ) : w j ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top ((ENNReal.le_tsum j).trans hw)

lemma mixL_append_le (hP1 : ∀ j a, P j a ≤ 1) (xs : List α) (y : α) :
    mixL P w (xs ++ [y]) ≤ mixL P w xs := by
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [lik_append]
  calc w j * (lik P j xs * P j y) ≤ w j * (lik P j xs * 1) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hP1 j y))
    _ = w j * lik P j xs := by rw [mul_one]

/-- The excess on a test item, as three logarithms. -/
lemma excess_eq_logs (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (j : ℕ) {xs : List α} {y : α}
    (hm : mixL P w (xs ++ [y]) ≠ 0) :
    excess P w j xs y = Real.logb 2 (P j y).toReal - Real.logb 2 (mixL P w (xs ++ [y])).toReal
      + Real.logb 2 (mixL P w xs).toReal := by
  have hmx : mixL P w xs ≠ 0 := fun h => hm (le_zero_iff.mp (h ▸ mixL_append_le P w hP1 xs y))
  have r1 : (mixL P w xs).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hmx, mixL_ne_top' P w hP1 hw xs⟩
  have r2 : (mixL P w (xs ++ [y])).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hm, mixL_ne_top' P w hP1 hw _⟩
  unfold excess pred
  rw [ENNReal.toReal_div, Real.logb_div r2 r1]
  ring

/-- Any lower bound `q` on HSI's probability of (training data, test item) bounds the excess. -/
lemma excess_le_of_le (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (j : ℕ) {xs : List α} {y : α}
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≤ mixL P w (xs ++ [y])) :
    excess P w j xs y ≤ Real.logb 2 (P j y).toReal - Real.logb 2 q.toReal
      + Real.logb 2 (mixL P w xs).toReal := by
  have hm : mixL P w (xs ++ [y]) ≠ 0 := fun h => hq0 (le_zero_iff.mp (h ▸ hq))
  have hmt := mixL_ne_top' P w hP1 hw (xs ++ [y])
  rw [excess_eq_logs P w hP1 hw j hm]
  have hqt : q ≠ ⊤ := ne_top_of_le_ne_top hmt hq
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (ENNReal.toReal_pos hq0 hqt)
    (ENNReal.toReal_mono hmt hq)
  linarith

/-! ## Step 1: Proposition E, the upper bound -/

/-- [UNAPPROVED STATEMENT] Proposition E before taking logarithms: for every member `j`, dataset
`xs` and test item `y`,
`w j · P_j(X) · P_j(y) ≤ P_Η(y | X) · P_Η(X)`. -/
theorem ood_upper_ennreal (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (j : ℕ) (xs : List α)
    (y : α) : w j * lik P j xs * P j y ≤ pred P w xs y * mixL P w xs := by
  by_cases h0 : mixL P w xs = 0
  · have h1 : w j * lik P j xs = 0 := le_zero_iff.mp (h0 ▸ le_mixL P w j xs)
    simp [h1]
  · unfold pred
    rw [ENNReal.div_mul_cancel h0 (mixL_ne_top' P w hP1 hw xs), mul_assoc, ← lik_append]
    exact le_mixL P w j (xs ++ [y])

/-- [UNAPPROVED STATEMENT] **Proposition E (upper bound on the out-of-distribution penalty).**

Models with `P j a ≤ 1`, weights with `Σ w ≤ 1`, a comparison member `j` with `w j > 0`
("fresh SolInd"), ANY training data `xs` and ANY test item `y`, such that `j` gives `xs` and `y`
positive probability. Then

`(trained HSI's log loss on y) - (j's log loss on y) ≤ -log₂ w j + trainGain j xs`,

where `trainGain j xs = (j's log loss on xs, item by item) - (HSI's log loss on xs)`. In words:
the extra cost of a surprising test item is at most what HSI gained over `j` in training, plus the
constant `-log₂ w j`. No assumption on where `xs` or `y` come from.

(Under `Rate.lean`'s stronger hypothesis `∑' a, P j a ≤ 1` this is `excess_eq_sub` followed by
`totalExcess_le` at the dataset `xs ++ [y]`: Proposition E is the pointwise bound for the
dataset (X, y), rearranged.) -/
theorem ood_upper (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {j : ℕ} (hw0 : w j ≠ 0)
    (xs : List α) (y : α) (hl : lik P j (xs ++ [y]) ≠ 0) :
    excess P w j xs y ≤ -Real.logb 2 (w j).toReal + trainGain P w j xs := by
  have hl' := hl
  rw [lik_append, mul_ne_zero_iff] at hl'
  obtain ⟨hlx, hpy⟩ := hl'
  have r1 : 0 < (w j).toReal := ENNReal.toReal_pos hw0 (w_ne_top w hw j)
  have r2 : 0 < (lik P j xs).toReal :=
    ENNReal.toReal_pos hlx (ne_top_of_le_ne_top one_ne_top (lik_le_one' P hP1 j xs))
  have r3 : 0 < (P j y).toReal :=
    ENNReal.toReal_pos hpy (ne_top_of_le_ne_top one_ne_top (hP1 j y))
  have h := excess_le_of_le P w hP1 hw j (q := w j * (lik P j xs * P j y))
    (mul_ne_zero hw0 (mul_ne_zero hlx hpy)) (by rw [← lik_append]; exact le_mixL P w j _)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, Real.logb_mul r1.ne' (mul_pos r2 r3).ne',
    Real.logb_mul r2.ne' r3.ne'] at h
  unfold trainGain
  linarith

/-- [UNAPPROVED STATEMENT] The right-hand side of `ood_upper` is never negative:
`trainGain j xs ≥ log₂ w j` (Theorem A of the note, `le_mixL`, in the vocabulary of this file). -/
theorem logb_le_trainGain (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {j : ℕ} (hw0 : w j ≠ 0)
    (xs : List α) (hl : lik P j xs ≠ 0) :
    Real.logb 2 (w j).toReal ≤ trainGain P w j xs := by
  have r1 : 0 < (w j).toReal := ENNReal.toReal_pos hw0 (w_ne_top w hw j)
  have r2 : 0 < (lik P j xs).toReal :=
    ENNReal.toReal_pos hl (ne_top_of_le_ne_top one_ne_top (lik_le_one' P hP1 j xs))
  have h := ENNReal.toReal_mono (mixL_ne_top' P w hP1 hw xs) (le_mixL P w j xs)
  rw [ENNReal.toReal_mul] at h
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos r1 r2) h
  rw [Real.logb_mul r1.ne' r2.ne'] at h2
  unfold trainGain
  linarith

/-- [UNAPPROVED STATEMENT] **The upper bound is attained.** If the comparison member `j` is the
only member of positive weight that gives the test item `y` positive probability, then
`ood_upper` holds with EQUALITY: the out-of-distribution penalty is exactly HSI's training gain
plus `-log₂ w j`. -/
theorem ood_upper_attained (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {j : ℕ} (hw0 : w j ≠ 0)
    (xs : List α) (y : α) (hl : lik P j (xs ++ [y]) ≠ 0)
    (honly : ∀ i, i ≠ j → w i * P i y = 0) :
    excess P w j xs y = -Real.logb 2 (w j).toReal + trainGain P w j xs := by
  have hl' := hl
  rw [lik_append, mul_ne_zero_iff] at hl'
  obtain ⟨hlx, hpy⟩ := hl'
  have r1 : 0 < (w j).toReal := ENNReal.toReal_pos hw0 (w_ne_top w hw j)
  have r2 : 0 < (lik P j xs).toReal :=
    ENNReal.toReal_pos hlx (ne_top_of_le_ne_top one_ne_top (lik_le_one' P hP1 j xs))
  have r3 : 0 < (P j y).toReal :=
    ENNReal.toReal_pos hpy (ne_top_of_le_ne_top one_ne_top (hP1 j y))
  have hmix : mixL P w (xs ++ [y]) = w j * (lik P j xs * P j y) := by
    unfold mixL
    rw [tsum_eq_single j, lik_append]
    intro i hi
    rw [lik_append]
    calc w i * (lik P i xs * P i y) = lik P i xs * (w i * P i y) := by ring
      _ = 0 := by rw [honly i hi, mul_zero]
  rw [excess_eq_logs P w hP1 hw j (mixL_ne_zero P w hw0 hl), hmix, ENNReal.toReal_mul,
    ENNReal.toReal_mul, Real.logb_mul r1.ne' (mul_pos r2 r3).ne', Real.logb_mul r2.ne' r3.ne']
  unfold trainGain
  ring

/-! ## Step 2: the lower bound — the penalty can be large -/

lemma geom_aux (t s : ℝ≥0∞) (h : t + s ≤ 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), t ^ k) * s + t ^ (n + 1) ≤ 1 := by
  induction n with
  | zero => simpa [add_comm] using h
  | succ n ih =>
    calc (∑ k ∈ Finset.range (n + 1 + 1), t ^ k) * s + t ^ (n + 1 + 1)
        = (∑ k ∈ Finset.range (n + 1), t ^ k) * s + t ^ (n + 1) * (t + s) := by
          rw [Finset.sum_range_succ]; ring
      _ ≤ (∑ k ∈ Finset.range (n + 1), t ^ k) * s + t ^ (n + 1) * 1 := by gcongr
      _ ≤ 1 := by rw [mul_one]; exact ih

/-- `(n+1) tⁿ s ≤ 1` whenever `t + s ≤ 1` (the note's `max_t tⁿ(1-t) ≤ 1/(n+1)`), without
subtraction: `(n+1) tⁿ ≤ 1 + t + … + tⁿ` and `(1 + t + … + tⁿ) s + tⁿ⁺¹ ≤ 1`. -/
lemma succ_mul_pow_mul_le_one (t s : ℝ≥0∞) (h : t + s ≤ 1) (n : ℕ) :
    ((n : ℝ≥0∞) + 1) * (t ^ n * s) ≤ 1 := by
  have ht : t ≤ 1 := le_trans le_self_add h
  have h1 : ((n : ℝ≥0∞) + 1) * t ^ n ≤ ∑ k ∈ Finset.range (n + 1), t ^ k := by
    have h2 : ∑ _k ∈ Finset.range (n + 1), t ^ n ≤ ∑ k ∈ Finset.range (n + 1), t ^ k :=
      Finset.sum_le_sum fun k hk =>
        pow_le_pow_right_of_le_one' ht (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    simpa [Finset.sum_const, nsmul_eq_mul] using h2
  calc ((n : ℝ≥0∞) + 1) * (t ^ n * s) = (((n : ℝ≥0∞) + 1) * t ^ n) * s := by ring
    _ ≤ (∑ k ∈ Finset.range (n + 1), t ^ k) * s := by gcongr
    _ ≤ (∑ k ∈ Finset.range (n + 1), t ^ k) * s + t ^ (n + 1) := le_self_add
    _ ≤ 1 := geom_aux t s h n

lemma lik_replicate (j : ℕ) (n : ℕ) (a : α) : lik P j (List.replicate n a) = P j a ^ n := by
  simp [lik]

lemma lik_replicate_append (j : ℕ) (n : ℕ) (a b : α) :
    lik P j (List.replicate n a ++ [b]) = P j a ^ n * P j b := by
  rw [lik_append, lik_replicate]

/-- Two different items share at most probability one, under `Rate.lean`'s hypothesis. -/
lemma add_le_one_of_ne (hP : ∀ j, ∑' a, P j a ≤ 1) {a b : α} (hab : a ≠ b) (j : ℕ) :
    P j a + P j b ≤ 1 := by
  classical
  refine le_trans ?_ (hP j)
  have h := ENNReal.sum_le_tsum (f := P j) {a, b}
  rwa [Finset.sum_pair hab] at h

/-- [UNAPPROVED STATEMENT] HSI's probability of "`n` copies of `a`, then `b`" is at most
`1/(n+1)`, whenever no model gives `a` and `b` together more than probability one. -/
theorem mixL_replicate_append_le (hw : ∑' j, w j ≤ 1) (a b : α)
    (hab : ∀ j, P j a + P j b ≤ 1) (n : ℕ) :
    mixL P w (List.replicate n a ++ [b]) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
  have hk : ∀ j, w j * lik P j (List.replicate n a ++ [b]) ≤ w j * ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro j
    rw [lik_replicate_append]
    gcongr
    rw [ENNReal.le_inv_iff_mul_le, mul_comm]
    exact succ_mul_pow_mul_le_one _ _ (hab j) n
  calc mixL P w (List.replicate n a ++ [b])
      ≤ ∑' j, w j * ((n : ℝ≥0∞) + 1)⁻¹ := ENNReal.tsum_le_tsum hk
    _ = (∑' j, w j) * ((n : ℝ≥0∞) + 1)⁻¹ := ENNReal.tsum_mul_right
    _ ≤ 1 * ((n : ℝ≥0∞) + 1)⁻¹ := by gcongr
    _ = ((n : ℝ≥0∞) + 1)⁻¹ := one_mul _

/-- [UNAPPROVED STATEMENT] The general form of `pred_offDistribution_le`: the hypothesis on the
models is only that none gives `a` and `b` together more than probability one. -/
theorem pred_offDistribution_le' (hw : ∑' j, w j ≤ 1) (a b : α)
    (hab : ∀ j, P j a + P j b ≤ 1) (j₀ : ℕ) (hj₀ : P j₀ a = 1) (n : ℕ) :
    pred P w (List.replicate n a) b ≤ 1 / (((n : ℝ≥0∞) + 1) * w j₀) := by
  have hD : w j₀ ≤ mixL P w (List.replicate n a) := by
    have h := le_mixL P w j₀ (List.replicate n a)
    rwa [lik_replicate, hj₀, one_pow, mul_one] at h
  unfold pred
  calc mixL P w (List.replicate n a ++ [b]) / mixL P w (List.replicate n a)
      ≤ ((n : ℝ≥0∞) + 1)⁻¹ / w j₀ :=
        ENNReal.div_le_div (mixL_replicate_append_le P w hw a b hab n) hD
    _ = 1 / (((n : ℝ≥0∞) + 1) * w j₀) := by
        rw [one_div, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), div_eq_mul_inv]

/-- [UNAPPROVED STATEMENT] **Off-distribution test item** (the note's §6 candidate 1, as
sketched there, minus an unused `DecidableEq`). Train on `n` copies of `a`; some member `j₀` of
positive weight puts probability one on `a`; test on `b ≠ a`. Then trained HSI gives `b`
probability at most `1 / ((n+1) · w j₀)`.

Not vacuous: `example_ood_linear` exhibits such a class in which the left-hand side is positive.
(`hw₀` is not used by the proof — with `w j₀ = 0` the right-hand side is `⊤` — and is kept only
because the sketch has it.) -/
theorem pred_offDistribution_le (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1)
    (a b : α) (hab : a ≠ b) (j₀ : ℕ) (hj₀ : P j₀ a = 1) (_hw₀ : w j₀ ≠ 0) (n : ℕ) :
    pred P w (List.replicate n a) b ≤ 1 / (((n : ℝ≥0∞) + 1) * w j₀) :=
  pred_offDistribution_le' P w hw a b (add_le_one_of_ne P hP hab) j₀ hj₀ n

/-- [UNAPPROVED STATEMENT] **The out-of-distribution penalty can be large** (Proposition E's
example, log form). Train on `n` copies of `a`, test on `b`; no model gives `a` and `b` together
more than probability one; a member `j₀` of positive weight puts probability one on `a`; the
comparison member `j` ("fresh SolInd") has positive weight and gives `a` and `b` positive
probability. Then

`(trained HSI's log loss on b) - (j's log loss on b) ≥ log₂(n+1) - C`,
`C = -log₂ w j₀ - log₂ P_j(b)`, which does not depend on `n`. -/
theorem ood_lower (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (a b : α)
    (hab : ∀ j, P j a + P j b ≤ 1) {j₀ : ℕ} (hj₀ : P j₀ a = 1) (hw₀ : w j₀ ≠ 0)
    {j : ℕ} (hw0 : w j ≠ 0) (ha : P j a ≠ 0) (hb : P j b ≠ 0) (n : ℕ) :
    Real.logb 2 ((n : ℝ) + 1) - (-Real.logb 2 (w j₀).toReal - Real.logb 2 (P j b).toReal)
      ≤ excess P w j (List.replicate n a) b := by
  have hlx : lik P j (List.replicate n a) ≠ 0 := by
    rw [lik_replicate]; exact pow_ne_zero n ha
  have hl : lik P j (List.replicate n a ++ [b]) ≠ 0 := by
    rw [lik_append]; exact mul_ne_zero hlx hb
  have hq0 : pred P w (List.replicate n a) b ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨mixL_ne_zero P w hw0 hl, mixL_ne_top' P w hP1 hw _⟩
  have hqt : pred P w (List.replicate n a) b ≠ ⊤ :=
    ENNReal.div_ne_top (mixL_ne_top' P w hP1 hw _) (mixL_ne_zero P w hw0 hlx)
  have hq : 0 < (pred P w (List.replicate n a) b).toReal := ENNReal.toReal_pos hq0 hqt
  have r0 : 0 < (w j₀).toReal := ENNReal.toReal_pos hw₀ (w_ne_top w hw j₀)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbd : (pred P w (List.replicate n a) b).toReal ≤ 1 / (((n : ℝ) + 1) * (w j₀).toReal) := by
    have hfin : 1 / (((n : ℝ≥0∞) + 1) * w j₀) ≠ ⊤ := by
      rw [one_div]
      exact ENNReal.inv_ne_top.mpr (mul_ne_zero (by simp) hw₀)
    have h := ENNReal.toReal_mono hfin (pred_offDistribution_le' P w hw a b hab j₀ hj₀ n)
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_add (by simp) (by simp)] at h
    simpa using h
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hq hbd
  rw [one_div, Real.logb_inv, Real.logb_mul hn.ne' r0.ne'] at h2
  unfold excess
  linarith

/-- [UNAPPROVED STATEMENT] **In a class where the upper bound is attained, the penalty is
LINEAR in the amount of training data.** As in `ood_lower`, and in addition the comparison
member `j` is the only member of positive weight that gives `b` positive probability. Then

`(trained HSI's log loss on b) - (j's log loss on b) ≥ n · (-log₂ P_j(a)) - (-log₂ w j₀)`:

`n` times what `j` pays per training item, minus a constant. -/
theorem ood_linear (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (a b : α)
    {j₀ : ℕ} (hj₀ : P j₀ a = 1) (hw₀ : w j₀ ≠ 0)
    {j : ℕ} (hw0 : w j ≠ 0) (ha : P j a ≠ 0) (hb : P j b ≠ 0)
    (honly : ∀ i, i ≠ j → w i * P i b = 0) (n : ℕ) :
    (n : ℝ) * (-Real.logb 2 (P j a).toReal) - (-Real.logb 2 (w j₀).toReal)
      ≤ excess P w j (List.replicate n a) b := by
  have hlx : lik P j (List.replicate n a) ≠ 0 := by
    rw [lik_replicate]; exact pow_ne_zero n ha
  have hl : lik P j (List.replicate n a ++ [b]) ≠ 0 := by
    rw [lik_append]; exact mul_ne_zero hlx hb
  rw [ood_upper_attained P w hP1 hw hw0 _ b hl honly]
  have r0 : 0 < (w j₀).toReal := ENNReal.toReal_pos hw₀ (w_ne_top w hw j₀)
  have hD : w j₀ ≤ mixL P w (List.replicate n a) := by
    have h := le_mixL P w j₀ (List.replicate n a)
    rwa [lik_replicate, hj₀, one_pow, mul_one] at h
  have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) r0
    (ENNReal.toReal_mono (mixL_ne_top' P w hP1 hw _) hD)
  have h2 : Real.logb 2 (w j).toReal ≤ 0 := by
    apply Real.logb_nonpos (by norm_num) ENNReal.toReal_nonneg
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using (ENNReal.le_tsum j).trans hw)
  unfold trainGain
  rw [lik_replicate, ENNReal.toReal_pow, Real.logb_pow]
  linarith

/-! ### A class in which the penalty is linear (vacuity guard) -/

/-- Example class on `Bool`: model `0` is the point mass on `true`, model `1` is the fair coin,
every other model is zero. -/
noncomputable def exP : ℕ → Bool → ℝ≥0∞ := fun j x =>
  if j = 0 then (if x then 1 else 0) else if j = 1 then 2⁻¹ else 0

/-- Example weights: `1/2` on models `0` and `1`. -/
noncomputable def exW : ℕ → ℝ≥0∞ := fun j => if j = 0 then 2⁻¹ else if j = 1 then 2⁻¹ else 0

lemma exP_sub (j : ℕ) : ∑' a, exP j a ≤ 1 := by
  rw [tsum_bool]
  by_cases h0 : j = 0
  · simp [exP, h0]
  · by_cases h1 : j = 1
    · simp [exP, h1, ENNReal.inv_two_add_inv_two]
    · simp [exP, h0, h1]

lemma exW_sub : ∑' j, exW j ≤ 1 := by
  have h : ∑' j, exW j = ∑ j ∈ ({0, 1} : Finset ℕ), exW j := by
    apply tsum_eq_sum
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [exW, hj.1, hj.2]
  rw [h, Finset.sum_pair (by norm_num)]
  simp [exW, ENNReal.inv_two_add_inv_two]

/-- [UNAPPROVED STATEMENT] **The linear penalty occurs.** There is a class (on `Bool`: the point
mass on `true`, and the fair coin, weight `1/2` each) satisfying all of `Rate.lean`'s hypotheses
in which, after training on `n` copies of `true`, trained HSI's log loss on `false` exceeds the
fair coin's by at least `n - 1` bits. So the hypotheses of `ood_lower`, `ood_linear` and
`pred_offDistribution_le` are satisfiable and the penalty is not always logarithmic. -/
theorem example_ood_linear :
    ∃ (P : ℕ → Bool → ℝ≥0∞) (w : ℕ → ℝ≥0∞), (∀ j, ∑' a, P j a ≤ 1) ∧ ∑' j, w j ≤ 1 ∧
      ∀ n : ℕ, (n : ℝ) - 1 ≤ excess P w 1 (List.replicate n true) false := by
  refine ⟨exP, exW, exP_sub, exW_sub, fun n => ?_⟩
  have hP1 : ∀ j a, exP j a ≤ 1 := fun j a => (ENNReal.le_tsum a).trans (exP_sub j)
  have h := ood_linear exP exW hP1 exW_sub true false (j₀ := 0) (by simp [exP])
    (by simp [exW]) (j := 1) (by simp [exW]) (by simp [exP]) (by simp [exP])
    (by
      intro i hi
      by_cases h0 : i = 0
      · simp [exP, h0]
      · simp [exW, h0, hi]) n
  have e1 : Real.logb 2 (exP 1 true).toReal = -1 := by
    simp [exP, Real.logb_inv]
  have e2 : Real.logb 2 (exW 0).toReal = -1 := by
    simp [exW, Real.logb_inv]
  rw [e1, e2] at h
  linarith

/-! ## A logarithmic upper bound when the class contains a hedged model -/

lemma pow_mul_lik_le {i k : ℕ} {c : ℝ≥0∞} (hik : ∀ a, c * P k a ≤ P i a) (xs : List α) :
    c ^ xs.length * lik P k xs ≤ lik P i xs := by
  induction xs with
  | nil => simp [lik]
  | cons a xs ih =>
    have e1 : lik P k (a :: xs) = P k a * lik P k xs := by simp [lik]
    have e2 : lik P i (a :: xs) = P i a * lik P i xs := by simp [lik]
    rw [e1, e2, List.length_cons, pow_succ]
    calc c ^ xs.length * c * (P k a * lik P k xs)
        = (c * P k a) * (c ^ xs.length * lik P k xs) := by ring
      _ ≤ P i a * lik P i xs := mul_le_mul' (hik a) ih

/-- [UNAPPROVED STATEMENT] **Upper bound through a hedged member.** Let member `i` (positive
weight) dominate `c ·` (model `k`) and `d ·` (the comparison model `j`), `0 < c, d < ∞` — e.g.
`i` is the mixture `c · P_k + d · P_j`. For any training data `xs` to which `k` gives positive
probability and any test item `y` with `P_j(y) > 0`:

`(trained HSI's log loss on y) - (j's log loss on y)
   ≤ -log₂ w i + |xs| · (-log₂ c) + (-log₂ d) + trainGain k xs`.

This is Proposition E's argument with the lower bound `w i · P_i(X, y)` on HSI's probability of
(X, y) instead of `w j · P_j(X, y)`: the comparison model only has to be present inside SOME
member that also explains the training data. -/
theorem ood_upper_hedged (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {i j k : ℕ}
    (hwi : w i ≠ 0) {c d : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (hik : ∀ a, c * P k a ≤ P i a) (hij : ∀ a, d * P j a ≤ P i a)
    (xs : List α) (y : α) (hk : lik P k xs ≠ 0) (hy : P j y ≠ 0) :
    excess P w j xs y ≤ -Real.logb 2 (w i).toReal + (xs.length : ℝ) * (-Real.logb 2 c.toReal)
      + (-Real.logb 2 d.toReal) + trainGain P w k xs := by
  have hq : w i * ((c ^ xs.length * lik P k xs) * (d * P j y)) ≤ mixL P w (xs ++ [y]) := by
    refine le_trans ?_ (le_mixL P w i (xs ++ [y]))
    rw [lik_append]
    exact mul_le_mul' le_rfl (mul_le_mul' (pow_mul_lik_le P hik xs) (hij y))
  have h := excess_le_of_le P w hP1 hw j
    (mul_ne_zero hwi (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc0) hk) (mul_ne_zero hd0 hy))) hq
  have r1 : 0 < (w i).toReal := ENNReal.toReal_pos hwi (w_ne_top w hw i)
  have rc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  have rd : 0 < d.toReal := ENNReal.toReal_pos hd0 hdt
  have rl : 0 < (lik P k xs).toReal :=
    ENNReal.toReal_pos hk (ne_top_of_le_ne_top one_ne_top (lik_le_one' P hP1 k xs))
  have rp : 0 < (P j y).toReal :=
    ENNReal.toReal_pos hy (ne_top_of_le_ne_top one_ne_top (hP1 j y))
  have rcn : 0 < c.toReal ^ xs.length := pow_pos rc _
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow] at h
  rw [Real.logb_mul r1.ne' (mul_pos (mul_pos rcn rl) (mul_pos rd rp)).ne',
    Real.logb_mul (mul_pos rcn rl).ne' (mul_pos rd rp).ne', Real.logb_mul rcn.ne' rl.ne',
    Real.logb_mul rd.ne' rp.ne', Real.logb_pow] at h
  unfold trainGain
  linarith

/-- [UNAPPROVED STATEMENT] **A logarithmic upper bound on the out-of-distribution penalty.**
Training data `xs` of size `n ≥ 1`. Suppose some member `i` of positive weight hedges between a
model `k` and the comparison model `j` at rate `1/(n+1)`: `P_i ≥ (n/(n+1)) · P_k` and
`P_i ≥ (1/(n+1)) · P_j` (e.g. `P_i = (n/(n+1)) P_k + (1/(n+1)) P_j`). Then for every test item
`y` with `P_j(y) > 0` (and `P_k(xs) > 0`):

`(trained HSI's log loss on y) - (j's log loss on y)
   ≤ log₂(n+1) + 1/ln 2 - log₂ w i + trainGain k xs`.

`trainGain k xs` is how much HSI beat the single model `k` on the training data; it is `≤ 0`
when `k` fits the training data perfectly. So when one model explains the training data about as
well as HSI does, a surprising test item costs only `log₂(n+1)` plus the price `-log₂ w i` of
naming the hedge (which depends on `n` through `i`). -/
theorem ood_upper_hedged_log (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {i j k : ℕ}
    (hwi : w i ≠ 0) (xs : List α) (y : α) (hn : xs ≠ [])
    (hik : ∀ a, ((xs.length : ℝ≥0∞) / ((xs.length : ℝ≥0∞) + 1)) * P k a ≤ P i a)
    (hij : ∀ a, ((xs.length : ℝ≥0∞) + 1)⁻¹ * P j a ≤ P i a)
    (hk : lik P k xs ≠ 0) (hy : P j y ≠ 0) :
    excess P w j xs y ≤ Real.logb 2 ((xs.length : ℝ) + 1) + 1 / Real.log 2
      - Real.logb 2 (w i).toReal + trainGain P w k xs := by
  have hlen : 0 < xs.length := List.length_pos_iff.mpr hn
  have hN : (0 : ℝ) < (xs.length : ℝ) := by exact_mod_cast hlen
  have hN1 : (0 : ℝ) < (xs.length : ℝ) + 1 := by positivity
  have hc0 : ((xs.length : ℝ≥0∞) / ((xs.length : ℝ≥0∞) + 1)) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast hlen.ne', by simp⟩
  have hct : ((xs.length : ℝ≥0∞) / ((xs.length : ℝ≥0∞) + 1)) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by simp)
  have hd0 : ((xs.length : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
  have hdt : ((xs.length : ℝ≥0∞) + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by simp)
  have h := ood_upper_hedged P w hP1 hw hwi hc0 hct hd0 hdt hik hij xs y hk hy
  have ec : ((xs.length : ℝ≥0∞) / ((xs.length : ℝ≥0∞) + 1)).toReal
      = (xs.length : ℝ) / ((xs.length : ℝ) + 1) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)]; simp
  have ed : (((xs.length : ℝ≥0∞) + 1)⁻¹).toReal = ((xs.length : ℝ) + 1)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp)]; simp
  rw [ec, ed, Real.logb_inv] at h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : (xs.length : ℝ) * (-Real.logb 2 ((xs.length : ℝ) / ((xs.length : ℝ) + 1)))
      ≤ 1 / Real.log 2 := by
    have h1 := Real.log_le_sub_one_of_pos (x := ((xs.length : ℝ) + 1) / (xs.length : ℝ))
      (div_pos hN1 hN)
    have h2 : Real.log (((xs.length : ℝ) + 1) / (xs.length : ℝ))
        = -Real.log ((xs.length : ℝ) / ((xs.length : ℝ) + 1)) := by
      rw [← Real.log_inv, inv_div]
    have h3 : ((xs.length : ℝ) + 1) / (xs.length : ℝ) - 1 = 1 / (xs.length : ℝ) := by
      field_simp; ring
    rw [h2, h3] at h1
    unfold Real.logb
    rw [← neg_div, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hlog2.le
    calc (xs.length : ℝ) * (-Real.log ((xs.length : ℝ) / ((xs.length : ℝ) + 1)))
        ≤ (xs.length : ℝ) * (1 / (xs.length : ℝ)) := mul_le_mul_of_nonneg_left h1 hN.le
      _ = 1 := by field_simp
  linarith

/-- [UNAPPROVED STATEMENT] **The `n` copies of `a`, then `b` example from above: the penalty is
at most `log₂(n+1) + 1/ln 2 - log₂ w i`** when the class contains a member `i` hedging between
the point mass `j₀` on `a` and the comparison model `j` at rate `1/(n+1)`. Together with
`ood_lower` (`≥ log₂(n+1) - C`), the penalty in such a class is `log₂(n+1)` up to the price of
naming the hedge. -/
theorem ood_offDistribution_upper (hP1 : ∀ j a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) (a b : α)
    {j₀ : ℕ} (hj₀ : P j₀ a = 1) {i j : ℕ} (hwi : w i ≠ 0) (n : ℕ) (hn : 0 < n)
    (hik : ∀ x, ((n : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) * P j₀ x ≤ P i x)
    (hij : ∀ x, ((n : ℝ≥0∞) + 1)⁻¹ * P j x ≤ P i x) (hb : P j b ≠ 0) :
    excess P w j (List.replicate n a) b
      ≤ Real.logb 2 ((n : ℝ) + 1) + 1 / Real.log 2 - Real.logb 2 (w i).toReal := by
  have hne : List.replicate n a ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  have hlk : lik P j₀ (List.replicate n a) = 1 := by rw [lik_replicate, hj₀, one_pow]
  have h := ood_upper_hedged_log P w hP1 hw (i := i) (j := j) (k := j₀) hwi
    (List.replicate n a) b hne (by simpa using hik) (by simpa using hij)
    (by rw [hlk]; exact one_ne_zero) hb
  have hg : trainGain P w j₀ (List.replicate n a) ≤ 0 := by
    unfold trainGain
    rw [hlk]
    have : Real.logb 2 (mixL P w (List.replicate n a)).toReal ≤ 0 := by
      apply Real.logb_nonpos (by norm_num) ENNReal.toReal_nonneg
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using mixL_le_one' P w hP1 hw (List.replicate n a))
    simpa using this
  rw [List.length_replicate] at h
  linarith

/-! ### A class in which the penalty is logarithmic (vacuity guard for the hedged bound) -/

/-- Example class on `Bool`: model `0` is the point mass on `true`, model `1` the fair coin, and
model `n + 2` the hedge `((n+1)/(n+2)) · (point mass) + (1/(n+2)) · (fair coin)`. -/
noncomputable def exQ : ℕ → Bool → ℝ≥0∞
  | 0, x => if x then 1 else 0
  | 1, _ => 2⁻¹
  | (n + 2), x => (((n + 1 : ℕ) : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) + 1)) * (if x then 1 else 0)
      + (((n + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹ * 2⁻¹

/-- Example weights `1 / ((m+1)(m+2))`, which sum to one. -/
noncomputable def exV : ℕ → ℝ≥0∞ := fun m =>
  ENNReal.ofReal (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))

lemma hedge_sum (N : ℝ≥0∞) (hN : N ≠ ⊤) :
    (N / (N + 1) * 0 + (N + 1)⁻¹ * 2⁻¹) + (N / (N + 1) * 1 + (N + 1)⁻¹ * 2⁻¹) = 1 := by
  have h2 : (N + 1)⁻¹ * 2⁻¹ + (N + 1)⁻¹ * 2⁻¹ = (N + 1)⁻¹ := by
    rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  calc (N / (N + 1) * 0 + (N + 1)⁻¹ * 2⁻¹) + (N / (N + 1) * 1 + (N + 1)⁻¹ * 2⁻¹)
      = N / (N + 1) + ((N + 1)⁻¹ * 2⁻¹ + (N + 1)⁻¹ * 2⁻¹) := by ring
    _ = N * (N + 1)⁻¹ + (N + 1)⁻¹ := by rw [h2, div_eq_mul_inv]
    _ = (N + 1) * (N + 1)⁻¹ := by ring
    _ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp [hN])

lemma exQ_sub (j : ℕ) : ∑' a, exQ j a ≤ 1 := by
  rw [tsum_bool]
  match j with
  | 0 => simp [exQ]
  | 1 => simp [exQ, ENNReal.inv_two_add_inv_two]
  | (n + 2) =>
    simp only [exQ, Bool.false_eq_true, if_false, if_true]
    exact (hedge_sum _ (by simp)).le

lemma exV_toReal (m : ℕ) : (exV m).toReal = 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
  ENNReal.toReal_ofReal (by positivity)

lemma exV_ne_zero (m : ℕ) : exV m ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (by positivity)).ne'

lemma exV_sub : ∑' m, exV m ≤ 1 := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  have key : ∀ N : ℕ, ∑ m ∈ Finset.range N, (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      = 1 - 1 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring
  unfold exV
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity), key]
  refine ENNReal.ofReal_le_one.mpr ?_
  have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  linarith

/-- [UNAPPROVED STATEMENT] **A class in which the out-of-distribution penalty is logarithmic.**
There is a class on `Bool` (the point mass on `true`, the fair coin, and for every `m ≥ 2` the
hedge `((m-1)/m) · (point mass) + (1/m) · (fair coin)`; weights `1/((m+1)(m+2))`) satisfying all
of `Rate.lean`'s hypotheses in which, after training on `N = n + 1` copies of `true`, trained
HSI's log loss on `false` exceeds the fair coin's by

at least `log₂(N+1) - 2` and at most `log₂(N+1) + 1/ln 2 + log₂((n+3)(n+4))` bits.

So the hypotheses of `ood_offDistribution_upper` are satisfiable for every `N` at once, and in
this class the penalty is between `log₂ N` and about `3 log₂ N`. -/
theorem example_ood_log :
    ∃ (P : ℕ → Bool → ℝ≥0∞) (w : ℕ → ℝ≥0∞), (∀ j, ∑' a, P j a ≤ 1) ∧ ∑' j, w j ≤ 1 ∧
      ∀ n : ℕ,
        Real.logb 2 (((n + 1 : ℕ) : ℝ) + 1) - 2
          ≤ excess P w 1 (List.replicate (n + 1) true) false ∧
        excess P w 1 (List.replicate (n + 1) true) false
          ≤ Real.logb 2 (((n + 1 : ℕ) : ℝ) + 1) + 1 / Real.log 2
            + Real.logb 2 (((n : ℝ) + 3) * ((n : ℝ) + 4)) := by
  refine ⟨exQ, exV, exQ_sub, exV_sub, fun n => ⟨?_, ?_⟩⟩
  · have hP1 : ∀ j a, exQ j a ≤ 1 := fun j a => (ENNReal.le_tsum a).trans (exQ_sub j)
    have h := ood_lower exQ exV hP1 exV_sub true false
      (add_le_one_of_ne exQ exQ_sub (by decide)) (j₀ := 0) (by simp [exQ]) (exV_ne_zero 0)
      (j := 1) (exV_ne_zero 1) (by simp [exQ]) (by simp [exQ]) (n + 1)
    have e1 : Real.logb 2 (exV 0).toReal = -1 := by
      rw [exV_toReal]
      have : (1 : ℝ) / ((((0 : ℕ) : ℝ) + 1) * (((0 : ℕ) : ℝ) + 2)) = 2⁻¹ := by norm_num
      rw [this, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    have e2 : Real.logb 2 (exQ 1 false).toReal = -1 := by
      simp [exQ, Real.logb_inv]
    rw [e1, e2] at h
    push_cast at h ⊢
    linarith
  · have hP1 : ∀ j a, exQ j a ≤ 1 := fun j a => (ENNReal.le_tsum a).trans (exQ_sub j)
    have h := ood_offDistribution_upper exQ exV hP1 exV_sub true false (j₀ := 0)
      (by simp [exQ]) (i := n + 2) (j := 1) (exV_ne_zero _) (n + 1) (Nat.succ_pos n)
      (by intro x; simp only [exQ]; exact le_self_add)
      (by intro x; simp only [exQ]; exact le_add_self)
      (by simp [exQ])
    have e : (exV (n + 2)).toReal = (((n : ℝ) + 3) * ((n : ℝ) + 4))⁻¹ := by
      rw [exV_toReal, one_div]
      push_cast
      congr 1
      ring
    rw [e, Real.logb_inv] at h
    linarith

/-! ## Step 3: the headline -/

/-- [UNAPPROVED STATEMENT] **HSI out of distribution.** Item models `P j` (each a
sub-probability mass function on items), hyperprior weights `w` with `Σ w ≤ 1`, and a comparison
member `j` of positive weight ("fresh SolInd": at the machine level, the untrained HSI prior
itself — `hsi_ood_machines`). Write `excess j X y` for trained HSI's log loss on the test item
`y` minus `j`'s (bits), and `trainGain j X` for `j`'s log loss on the training data `X` (item by
item) minus HSI's.

1. (Upper bound, Proposition E.) For ALL training data `X` and test items `y` to which `j` gives
   positive probability: `excess j X y ≤ -log₂ w j + trainGain j X`.
2. (It is attained.) With equality whenever `j` is the only member of positive weight that gives
   `y` positive probability.
3. (The penalty grows at least logarithmically off-distribution.) If a member `j₀` of positive
   weight puts probability one on an item `a`, `b ≠ a`, and `j` gives `a`, `b` positive
   probability, then after training on `n` copies of `a`:
   `excess j aⁿ b ≥ log₂(n+1) - (-log₂ w j₀ - log₂ P_j(b))`.
4. (And no faster, if the class can hedge.) If moreover a member `i` of positive weight
   dominates `(n/(n+1)) · P_{j₀}` and `(1/(n+1)) · P_j`, `n ≥ 1`, then
   `excess j aⁿ b ≤ log₂(n+1) + 1/ln 2 - log₂ w i`.

`example_ood_linear` shows that without a hedging member the penalty in 3 can be `n - 1` bits.
The joint statement "training + test together lose at most `-log₂ w j` to `j`" is
`Rate.totalExcess_le` at the dataset `X ++ [y]` and is not restated. -/
theorem hsi_ood (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1) {j : ℕ} (hw0 : w j ≠ 0) :
    (∀ (xs : List α) (y : α), lik P j (xs ++ [y]) ≠ 0 →
      excess P w j xs y ≤ -Real.logb 2 (w j).toReal + trainGain P w j xs) ∧
    (∀ (xs : List α) (y : α), lik P j (xs ++ [y]) ≠ 0 → (∀ i, i ≠ j → w i * P i y = 0) →
      excess P w j xs y = -Real.logb 2 (w j).toReal + trainGain P w j xs) ∧
    (∀ (a b : α) (j₀ n : ℕ), a ≠ b → P j₀ a = 1 → w j₀ ≠ 0 → P j a ≠ 0 → P j b ≠ 0 →
      Real.logb 2 ((n : ℝ) + 1) - (-Real.logb 2 (w j₀).toReal - Real.logb 2 (P j b).toReal)
        ≤ excess P w j (List.replicate n a) b) ∧
    (∀ (a b : α) (j₀ i n : ℕ), P j₀ a = 1 → w i ≠ 0 → 0 < n →
      (∀ x, ((n : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) * P j₀ x ≤ P i x) →
      (∀ x, ((n : ℝ≥0∞) + 1)⁻¹ * P j x ≤ P i x) → P j b ≠ 0 →
      excess P w j (List.replicate n a) b
        ≤ Real.logb 2 ((n : ℝ) + 1) + 1 / Real.log 2 - Real.logb 2 (w i).toReal) := by
  have hP1 : ∀ j a, P j a ≤ 1 := fun j a => P_le_one P hP j a
  refine ⟨fun xs y hl => ood_upper P w hP1 hw hw0 xs y hl,
    fun xs y hl honly => ood_upper_attained P w hP1 hw hw0 xs y hl honly,
    fun a b j₀ n hab hj₀ hw₀ ha hb =>
      ood_lower P w hP1 hw a b (add_le_one_of_ne P hP hab) hj₀ hw₀ hw0 ha hb n,
    fun a b j₀ i n hj₀ hwi hn hik hij hb =>
      ood_offDistribution_upper P w hP1 hw a b hj₀ hwi n hn hik hij hb⟩

/-! ## Step 4: HSI is exchangeable, so it cannot learn the ORDER of the items -/

/-- [UNAPPROVED STATEMENT] **HSI is exchangeable** (the note's §6 candidate 2): reordering the
dataset does not change the probability HSI gives it. No hypotheses. -/
theorem mixL_perm {xs ys : List α} (h : xs.Perm ys) : mixL P w xs = mixL P w ys := by
  unfold mixL lik
  exact tsum_congr fun j => by rw [(h.map (P j)).prod_eq]

/-- [UNAPPROVED STATEMENT] Hence the trained predictor does not depend on the order of the
training data either. -/
theorem pred_perm {xs ys : List α} (h : xs.Perm ys) (a : α) : pred P w xs a = pred P w ys a := by
  unfold pred
  rw [mixL_perm P w h, mixL_perm P w (h.append_right [a])]

/-- The total probability of all `n`-tuples under an i.i.d. model is `(∑ f)ⁿ`. -/
lemma tsum_pi_prod (f : α → ℝ≥0∞) (n : ℕ) :
    ∑' v : Fin n → α, ∏ i, f (v i) = (∑' a, f a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).tsum_eq, ENNReal.tsum_prod']
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih, pow_succ, mul_comm]

/-- `n! · e_n(f) ≤ e_1(f)ⁿ`, for any family `S` of `n`-element sets: every set has `n!`
orderings, and different sets have different orderings. -/
lemma sum_factorial_mul_prod_le (f : α → ℝ≥0∞) (S : Finset (Finset α)) (n : ℕ)
    (hS : ∀ s ∈ S, s.card = n) :
    ∑ s ∈ S, (n.factorial : ℝ≥0∞) * ∏ a ∈ s, f a ≤ (∑' a, f a) ^ n := by
  classical
  rw [← tsum_pi_prod f n]
  let e : ∀ s : S, Fin n ≃ ↥s.1 := fun s => (Finset.equivFinOfCardEq (hS s.1 s.2)).symm
  let φ : S × Equiv.Perm (Fin n) → (Fin n → α) := fun p i => ((e p.1 (p.2 i) : ↥p.1.1) : α)
  have hmem : ∀ (t : S) (τ : Equiv.Perm (Fin n)) (a : α), a ∈ t.1 ↔ ∃ i, φ (t, τ) i = a := by
    intro t τ a
    constructor
    · intro ha
      refine ⟨τ.symm ((e t).symm ⟨a, ha⟩), ?_⟩
      simp [φ]
    · rintro ⟨i, rfl⟩
      exact (e t (τ i)).2
  have hφ : Function.Injective φ := by
    rintro ⟨s, σ⟩ ⟨s', σ'⟩ h
    have hs : s = s' := by
      apply Subtype.ext
      ext a
      rw [hmem s σ a, hmem s' σ' a, h]
    subst hs
    refine Prod.ext rfl (Equiv.ext fun i => ?_)
    exact (e s).injective (Subtype.ext (congrFun h i))
  have hval : ∀ p : S × Equiv.Perm (Fin n), ∏ i, f (φ p i) = ∏ a ∈ p.1.1, f a := by
    intro p
    calc ∏ i, f (φ p i) = ∏ i, (fun x : ↥p.1.1 => f x) ((p.2.trans (e p.1)) i) := rfl
      _ = ∏ x : ↥p.1.1, f x :=
        Fintype.prod_equiv (p.2.trans (e p.1)) _ (fun x : ↥p.1.1 => f x) (fun _ => rfl)
      _ = ∏ a ∈ p.1.1, f a := Finset.prod_coe_sort p.1.1 f
  calc ∑ s ∈ S, (n.factorial : ℝ≥0∞) * ∏ a ∈ s, f a
      = ∑ s : S, (n.factorial : ℝ≥0∞) * ∏ a ∈ s.1, f a :=
        (Finset.sum_coe_sort S fun s => (n.factorial : ℝ≥0∞) * ∏ a ∈ s, f a).symm
    _ = ∑ s : S, ∑ σ : Equiv.Perm (Fin n), ∏ i, f (φ (s, σ) i) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [hval]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
    _ = ∑ p : S × Equiv.Perm (Fin n), ∏ i, f (φ p i) :=
        (Fintype.sum_prod_type fun p : S × Equiv.Perm (Fin n) => ∏ i, f (φ p i)).symm
    _ = ∑' p : S × Equiv.Perm (Fin n), ∏ i, f (φ p i) := (tsum_fintype _).symm
    _ ≤ ∑' v : Fin n → α, ∏ i, f (v i) :=
        ENNReal.tsum_comp_le_tsum_of_injective hφ fun v => ∏ i, f (v i)

/-- [UNAPPROVED STATEMENT] **The counting bound** (the note's §6 candidate 2, the core of its
Theorem B.3; `DecidableEq` dropped). For any finite family `S` of `n`-element sets of items,

`Σ_{s ∈ S} n! · P_Η(s, in any one order) ≤ 1`.

HSI must spread its probability over all `n!` orderings of every set, because it gives them all
the same probability (`mixL_perm`). A predictor that reads the items in order need not. -/
theorem card_mul_mixL_le_one (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1)
    (S : Finset (Finset α)) (n : ℕ) (hS : ∀ s ∈ S, s.card = n) :
    ∑ s ∈ S, (n.factorial : ℝ≥0∞) * mixL P w s.toList ≤ 1 := by
  have hlik : ∀ j (s : Finset α), lik P j s.toList = ∏ a ∈ s, P j a := fun j s => by
    unfold lik; exact Finset.prod_map_toList s (P j)
  calc ∑ s ∈ S, (n.factorial : ℝ≥0∞) * mixL P w s.toList
      = ∑ s ∈ S, ∑' j, w j * ((n.factorial : ℝ≥0∞) * ∏ a ∈ s, P j a) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        unfold mixL
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun j => by rw [hlik]; ring
    _ = ∑' j, ∑ s ∈ S, w j * ((n.factorial : ℝ≥0∞) * ∏ a ∈ s, P j a) :=
        (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
    _ = ∑' j, w j * ∑ s ∈ S, (n.factorial : ℝ≥0∞) * ∏ a ∈ s, P j a :=
        tsum_congr fun j => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑' j, w j * 1 := ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl
        ((sum_factorial_mul_prod_le (P j) S n hS).trans (pow_le_one' (hP j) n))
    _ ≤ 1 := by simpa using hw

/-- [UNAPPROVED STATEMENT] **HSI cannot be paid for order.** In any non-empty family of `N`
sets of `n` distinct items there is a set `s` every ordering `xs` of which gets HSI-probability
at most `1 / (n! · N)`. (A predictor that knows the order rule can give one ordering of each set
probability `1/N`: it then beats HSI on that dataset by `log₂ n!` bits.) -/
theorem exists_mixL_perm_le (hP : ∀ j, ∑' a, P j a ≤ 1) (hw : ∑' j, w j ≤ 1)
    (S : Finset (Finset α)) (hne : S.Nonempty) (n : ℕ) (hS : ∀ s ∈ S, s.card = n) :
    ∃ s ∈ S, ∀ xs : List α, xs.Perm s.toList →
      (n.factorial : ℝ≥0∞) * mixL P w xs ≤ (S.card : ℝ≥0∞)⁻¹ := by
  have hc0 : (S.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hsum : ∑ s ∈ S, (n.factorial : ℝ≥0∞) * mixL P w s.toList
      ≤ ∑ _s ∈ S, (S.card : ℝ≥0∞)⁻¹ := by
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel hc0 (by simp)]
    exact card_mul_mixL_le_one P w hP hw S n hS
  obtain ⟨s, hs, hle⟩ := ENNReal.exists_le_of_sum_le hne hsum
  exact ⟨s, hs, fun xs hxs => by rw [mixL_perm P w hxs]; exact hle⟩

end HsiLean.HsiOOD

/-! ## The machine level -/

namespace HsiLean.Monotone

open HsiLean.HsiRateLength HsiLean.HsiOOD

/-- [UNAPPROVED STATEMENT] **Proposition E about machines, with "fresh SolInd" = untrained HSI.**

Let `V` be an effective enumeration of monotone machines containing every UTM and `w` any
lower-semicomputable, everywhere-positive weights with `Σ w ≤ 1`. Then there are a UTM `U` and an
index `k` of `U` in the enumeration such that

(a) the untrained HSI prior `Σ_k' w_k' λ_{V k'}` equals `λ_U` on every non-empty string; and
(b) for every dataset `X` of finite strings and every test string `y` to which `U` gives positive
    probability (items read as content-given-length, `contentModel`):

    `(trained HSI's log loss on y) - (-log₂ λ_U(y)) ≤ -log₂ w k + trainGain k X`,

    where `trainGain k X = (λ_U's log loss on X, item by item) - (HSI's log loss on X)`.

So the extra cost of a surprising test item, relative to the SAME prior used fresh, is at most
what training gained on the training data, plus the constant `-log₂ w k`. -/
theorem hsi_ood_machines (V : ℕ → Machine) (hV : UniformlyCE V)
    (hU : ∀ U : Machine, IsUTM U → ∃ k, V k = U) (w : Weights) :
    ∃ (U : Machine) (k : ℕ), IsUTM U ∧ V k = U ∧
      (∀ x : List Bool, x ≠ [] → ∑' k', w k' * (V k').lam x = U.lam x) ∧
      ∀ (X : List (List Bool)) (y : List Bool),
        lik (contentModel fun k' => (V k').lamSm) k (X ++ [y]) ≠ 0 →
        excess (contentModel fun k' => (V k').lamSm) w.toFun k X y
          ≤ -Real.logb 2 (w.toFun k).toReal
            + trainGain (contentModel fun k' => (V k').lamSm) w.toFun k X := by
  obtain ⟨U, hUtm, hprior⟩ := hsi_prior_eq_utm V hV hU w
  obtain ⟨k, hk⟩ := hU U hUtm
  refine ⟨U, k, hUtm, hk, hprior, fun X y hl => ?_⟩
  exact ood_upper _ _ (fun j a => apply_le_one ((V j).lamSm) a) w.tsum_le_one
    (w.pos k).ne' X y hl

end HsiLean.Monotone

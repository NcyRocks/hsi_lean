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
* `ood_upper_hedged`, `ood_upper_hedged_replicate` — if the class contains a model hedging
  between a model `k` and the comparison `j`, the penalty is at most
  `log₂(n+1) + 1/ln 2 + (cost of the hedge) + trainGain k X`: logarithmic when one model `k`
  explains the training data about as well as HSI does.
* `hsi_ood` — the three main facts in one statement.
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

end HsiLean.HsiOOD

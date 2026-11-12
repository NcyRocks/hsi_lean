-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-12 and has NOT been reviewed by Nathan.
import HsiLean.Posterior
import HsiLean.Monotone
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Hutter's unit loss bound

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-12. Not reviewed by Nathan.

Source: M. Hutter, *General Loss Bounds for Universal Sequence Prediction* (arXiv cs/0101019),
Theorem `thULoss` (unit loss bound) and Theorem `thGLoss` (general loss bound).

## Setting

Binary sequences. `μ` is the true measure and `ξ` a mixture with `ξ ≥ w · μ`; both are given as
functions on finite strings (`IsStrMeasure`: nonnegative, `1` at the empty string, additive over
the next bit). At history `x` a predictor picks an action `a : 𝒴` (ANY type; the paper has
`𝒴 = {0,1}`) and suffers loss `l x b a ∈ [0,1]` when the next bit is `b`. The loss may depend on
the history, as the paper remarks after the theorem. A predictor is `ρ`-Bayes-optimal
(`IsBayesOpt ρ l p`, the paper's `Λ_ρ`) if at every history its action minimises the
`ρ`-expected loss.

* `cumLoss μ l p n` — the paper's `L_{nΛ}`: total `μ`-expected loss in the first `n` steps.
* `relEnt μ ξ n` — the paper's `H_n`: the summed expected relative entropy (in NATS) of the
  next-bit predictions.

## Results

* `unit_loss_bound_fn` — `0 ≤ L_ξ - L_μ ≤ H_n + √(4 L_μ H_n + H_n²)` and `0 ≤ H_n ≤ ln(1/w)`.
* `unit_loss_bound` — the same for a countable class of probability measures on `ℕ → Bool` with
  `Posterior.lean`'s mixture, plus the weaker forms with `D = ln(1/w)`:
  `≤ D + √(4 L_μ D + D²) ≤ 2D + 2√(L_μ D)`.
* `general_loss_bound_fn` — `thGLoss`: losses in `[lmin, lmin + lΔ]`.
* `exists_bayesOpt` — Bayes-optimal predictors exist when `𝒴` is finite and non-empty.

## Proof — where it departs from the paper

The paper's proof is a sketch. Its structure is kept: a per-step linear inequality
`l_ξ ≤ (1+A) l_μ + (1 + A/4 + 1/A) h` for every `A > 0` (the paper's (eineq3) with
`B = A/4 + 1/A`), summed over histories, then minimised over `A`.

The per-step inequality is where the paper stops: it reduces it by a case analysis to two
two-variable inequalities and says they "are proved in [Hutter:01op]; the cautious reader may
check the inequalities numerically". So there is no written proof of that step to formalise.
The proof here (`step_ineq`) is:

1. For any tilts `θ₀, θ₁`: `Σ yᵢ θᵢ ≤ Σ yᵢ ln(yᵢ/zᵢ) + Σ zᵢ e^{θᵢ} - 1` (from `ln t ≤ t - 1`).
2. With `β = 1/(1 + A/4 + 1/A)` and `θᵢ = β (l_{i,ξ} - (1+A) l_{i,μ})`:
   `e^{θᵢ} ≤ 1 + (e^β - 1)(l_{i,ξ} - l_{i,μ})`, by convexity of `exp` in each loss separately,
   provided `e^β + e^{-(1+A)β} ≤ 2`.
3. So `Σ zᵢ e^{θᵢ} ≤ 1 + (e^β - 1) Σ zᵢ (l_{i,ξ} - l_{i,μ}) ≤ 1` since `Λ_ξ` is `ξ`-optimal.
4. `e^β + e^{-(1+A)β} ≤ 2`: with `x = 2A/(A+2)`, `β = x - x²/2` and `(1+A)β = x + x²/2`, so the
   sum is `2 e^{-x²/2} cosh x ≤ 2` (`Real.cosh_le_exp_half_sq`). This is exactly where
   `B = A/4 + 1/A` comes from.

No case analysis on the losses is needed, and nothing uses that the alphabet is binary beyond
the bookkeeping.
-/

open Real Finset MeasureTheory

namespace HsiLean.LossBound

open HsiLean.Monotone (strs mem_strs concat_injective)
open HsiLean.Posterior

/-! ### Scalar inequalities -/

/-- `e^{x - x²/2} + e^{-x - x²/2} ≤ 2`, i.e. `cosh x ≤ e^{x²/2}`. -/
lemma exp_pair_le (x : ℝ) : exp (x - x ^ 2 / 2) + exp (-x - x ^ 2 / 2) ≤ 2 := by
  have h := Real.cosh_le_exp_half_sq x
  rw [Real.cosh_eq] at h
  have e1 : exp (x - x ^ 2 / 2) = exp x * exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1
  have e2 : exp (-x - x ^ 2 / 2) = exp (-x) * exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1
  have e3 : exp (x ^ 2 / 2) * exp (-(x ^ 2 / 2)) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < exp (-(x ^ 2 / 2)) := exp_pos _
  have h4 : (exp x + exp (-x)) * exp (-(x ^ 2 / 2)) ≤
      2 * exp (x ^ 2 / 2) * exp (-(x ^ 2 / 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  rw [e1, e2]
  nlinarith

/-- Convexity of `exp` on a segment from `0`. -/
lemma exp_mul_le (s r : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : exp (s * r) ≤ 1 + s * (exp r - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ r) (sub_nonneg.2 hs1) hs0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  linarith

/-- The exponential of the tilted loss difference is below a linear function of the plain
loss difference. -/
lemma exp_tilt_le (β c : ℝ) (hβ : 0 ≤ β) (hE : exp β + exp (-c) ≤ 2) (s m : ℝ)
    (hs : 0 ≤ s ∧ s ≤ 1) (hm : 0 ≤ m ∧ m ≤ 1) :
    exp (β * s - c * m) ≤ 1 + (exp β - 1) * (s - m) := by
  have h1 := exp_mul_le s β hs.1 hs.2
  have h2 := exp_mul_le m (-c) hm.1 hm.2
  have hκ : 0 ≤ exp β - 1 := by linarith [Real.one_le_exp hβ]
  have hκ' : exp β - 1 ≤ 1 - exp (-c) := by linarith
  have e : exp (β * s - c * m) = exp (s * β) * exp (m * (-c)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have h3 : exp (s * β) * exp (m * (-c)) ≤
      (1 + s * (exp β - 1)) * (1 + m * (exp (-c) - 1)) :=
    mul_le_mul h1 h2 (exp_pos _).le (by nlinarith [mul_nonneg hs.1 hκ])
  nlinarith [mul_nonneg hm.1 (sub_nonneg.2 hκ'),
    mul_nonneg (mul_nonneg hs.1 hm.1) (mul_nonneg hκ (hκ.trans hκ')), h3]

/-- One symbol of the variational (Gibbs / Donsker–Varadhan) inequality. -/
lemma sym_ineq (y z θ : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) (hyz : 0 < y → 0 < z) :
    y * θ ≤ y * log (y / z) + z * exp θ - y := by
  rcases hy.eq_or_lt with rfl | hy'
  · have := mul_nonneg hz (exp_pos θ).le
    simpa using this
  · have hz' := hyz hy'
    have h := Real.log_le_sub_one_of_pos (show 0 < z * exp θ / y by positivity)
    rw [Real.log_div (by positivity) hy'.ne', Real.log_mul hz'.ne' (exp_pos θ).ne',
      Real.log_exp] at h
    rw [Real.log_div hy'.ne' hz'.ne']
    have h2 := mul_le_mul_of_nonneg_left h hy'.le
    have h3 : y * (z * exp θ / y - 1) = z * exp θ - y := by field_simp
    rw [h3] at h2
    linarith

/-- [UNAPPROVED STATEMENT] **The per-step inequality** (the paper's (eineq3), with
`A' = 1 + A`, `B' = 1 + A/4 + 1/A`). `y` are the true next-bit probabilities, `z` the mixture's;
`l·s` are the losses of the `ξ`-optimal action, `l·m` those of the `μ`-optimal action; the only
property of the actions used is that the first is at least as good as the second under `z`. -/
theorem step_ineq (A : ℝ) (hA : 0 < A) (y0 y1 z0 z1 : ℝ)
    (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1) (hy : y0 + y1 = 1)
    (hz0 : 0 ≤ z0) (hz1 : 0 ≤ z1) (hz : z0 + z1 = 1)
    (h0 : 0 < y0 → 0 < z0) (h1 : 0 < y1 → 0 < z1) (l0s l1s l0m l1m : ℝ)
    (hl0s : 0 ≤ l0s ∧ l0s ≤ 1) (hl1s : 0 ≤ l1s ∧ l1s ≤ 1)
    (hl0m : 0 ≤ l0m ∧ l0m ≤ 1) (hl1m : 0 ≤ l1m ∧ l1m ≤ 1)
    (hopt : z0 * l0s + z1 * l1s ≤ z0 * l0m + z1 * l1m) :
    y0 * l0s + y1 * l1s ≤ (1 + A) * (y0 * l0m + y1 * l1m) +
      (1 + A / 4 + 1 / A) * (y0 * log (y0 / z0) + y1 * log (y1 / z1)) := by
  have hA2 : (0 : ℝ) < A + 2 := by linarith
  have key1 : (2 * A / (A + 2) - (2 * A / (A + 2)) ^ 2 / 2) * (1 + A / 4 + 1 / A) = 1 := by
    field_simp; ring
  have key2 : 2 * A / (A + 2) + (2 * A / (A + 2)) ^ 2 / 2 =
      (1 + A) * (2 * A / (A + 2) - (2 * A / (A + 2)) ^ 2 / 2) := by
    field_simp; ring
  obtain ⟨β, hβdef⟩ : ∃ β, β = 2 * A / (A + 2) - (2 * A / (A + 2)) ^ 2 / 2 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = 1 + A / 4 + 1 / A := ⟨_, rfl⟩
  have hE : exp β + exp (-((1 + A) * β)) ≤ 2 := by
    have h := exp_pair_le (2 * A / (A + 2))
    have e : -((1 + A) * β) = -(2 * A / (A + 2)) - (2 * A / (A + 2)) ^ 2 / 2 := by
      rw [hβdef, ← key2]; ring
    rw [e, hβdef]; exact h
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hβB : β * B = 1 := by rw [hβdef, hBdef]; exact key1
  have hβ0 : 0 ≤ β := by
    have : β = 1 / B := eq_div_of_mul_eq hBpos.ne' hβB
    rw [this]; positivity
  rw [← hBdef]
  have t0 := exp_tilt_le β ((1 + A) * β) hβ0 hE l0s l0m hl0s hl0m
  have t1 := exp_tilt_le β ((1 + A) * β) hβ0 hE l1s l1m hl1s hl1m
  have s0 := sym_ineq y0 z0 (β * l0s - (1 + A) * β * l0m) hy0 hz0 h0
  have s1 := sym_ineq y1 z1 (β * l1s - (1 + A) * β * l1m) hy1 hz1 h1
  have hκ : 0 ≤ exp β - 1 := by linarith [Real.one_le_exp hβ0]
  have hZ : z0 * exp (β * l0s - (1 + A) * β * l0m) +
      z1 * exp (β * l1s - (1 + A) * β * l1m) ≤ 1 := by
    have a0 := mul_le_mul_of_nonneg_left t0 hz0
    have a1 := mul_le_mul_of_nonneg_left t1 hz1
    have a2 := mul_le_mul_of_nonneg_left hopt hκ
    nlinarith
  have hsum : y0 * (β * l0s - (1 + A) * β * l0m) + y1 * (β * l1s - (1 + A) * β * l1m) ≤
      y0 * log (y0 / z0) + y1 * log (y1 / z1) := by linarith
  have h5 := mul_le_mul_of_nonneg_left hsum hBpos.le
  have hid : B * (y0 * (β * l0s - (1 + A) * β * l0m) + y1 * (β * l1s - (1 + A) * β * l1m)) =
      (β * B) * (y0 * l0s + y1 * l1s - (1 + A) * (y0 * l0m + y1 * l1m)) := by ring
  rw [hid, hβB, one_mul] at h5
  linarith

/-- Minimising the linear bound over `A` (the paper's last step, `A² = H/(L_μ + H/4)`). -/
lemma opt_bound (Lξ Lμ H : ℝ) (hL : 0 ≤ Lμ) (hH : 0 ≤ H)
    (h : ∀ A : ℝ, 0 < A → Lξ ≤ (1 + A) * Lμ + (1 + A / 4 + 1 / A) * H) :
    Lξ - Lμ ≤ H + Real.sqrt (4 * Lμ * H + H ^ 2) := by
  rcases hH.eq_or_lt with rfl | hHpos
  · have hs : Real.sqrt (4 * Lμ * 0 + 0 ^ 2) = 0 := by simp
    rw [hs, add_zero]
    by_contra hc
    push_neg at hc
    have hA : 0 < (Lξ - Lμ) / (2 * (Lμ + 1)) := div_pos hc (by positivity)
    have h1 := h _ hA
    have e : (Lξ - Lμ) / (2 * (Lμ + 1)) * Lμ = (Lξ - Lμ) / 2 * (Lμ / (Lμ + 1)) := by
      field_simp
    have h2 : Lμ / (Lμ + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have h3 : (Lξ - Lμ) / 2 * (Lμ / (Lμ + 1)) ≤ (Lξ - Lμ) / 2 :=
      mul_le_of_le_one_right (by linarith) h2
    nlinarith
  · have hnn : 0 < 4 * Lμ * H + H ^ 2 := by
      nlinarith [mul_nonneg hL hHpos.le, sq_pos_of_pos hHpos]
    obtain ⟨S, hSdef⟩ : ∃ S, S = Real.sqrt (4 * Lμ * H + H ^ 2) := ⟨_, rfl⟩
    have hS2 : S ^ 2 = 4 * Lμ * H + H ^ 2 := by rw [hSdef]; exact Real.sq_sqrt hnn.le
    have hSpos : 0 < S := by rw [hSdef]; exact Real.sqrt_pos.2 hnn
    rw [← hSdef]
    have hA : 0 < 2 * H / S := by positivity
    have h1 := h _ hA
    have hLμ : Lμ = (S ^ 2 - H ^ 2) / (4 * H) := by field_simp; linarith
    have e : (1 + 2 * H / S) * Lμ + (1 + 2 * H / S / 4 + 1 / (2 * H / S)) * H = Lμ + H + S := by
      rw [hLμ]; field_simp; ring
    linarith

/-! ### Measures as functions on strings; losses; relative entropy -/

variable {𝒴 : Type*}

/-- [UNAPPROVED STATEMENT] A probability measure on infinite binary sequences, given by its
values on cylinders: nonnegative, `1` on the empty string, additive over the next bit. -/
structure IsStrMeasure (ρ : List Bool → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ρ x
  nil : ρ [] = 1
  split : ∀ x, ρ x = ρ (x ++ [false]) + ρ (x ++ [true])

/-- The conditional probability `ρ(b | x)` (`0` when `ρ x = 0`). -/
noncomputable def cond (ρ : List Bool → ℝ) (x : List Bool) (b : Bool) : ℝ := ρ (x ++ [b]) / ρ x

/-- The `ρ`-expected loss of action `a` at history `x`. -/
noncomputable def expLoss (ρ : List Bool → ℝ) (l : List Bool → Bool → 𝒴 → ℝ) (x : List Bool)
    (a : 𝒴) : ℝ :=
  cond ρ x false * l x false a + cond ρ x true * l x true a

/-- [UNAPPROVED STATEMENT] `p` is the paper's `Λ_ρ`: at every history its action minimises the
`ρ`-expected loss. -/
def IsBayesOpt (ρ : List Bool → ℝ) (l : List Bool → Bool → 𝒴 → ℝ) (p : List Bool → 𝒴) : Prop :=
  ∀ x a, expLoss ρ l x (p x) ≤ expLoss ρ l x a

/-- [UNAPPROVED STATEMENT] The paper's `L_{nΛ}`: the total `μ`-expected loss of predictor `p`
over the first `n` steps. -/
noncomputable def cumLoss (μ : List Bool → ℝ) (l : List Bool → Bool → 𝒴 → ℝ)
    (p : List Bool → 𝒴) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, ∑ x ∈ strs t, μ x * expLoss μ l x (p x)

/-- The paper's `h_t(x)`: relative entropy (nats) of `μ`'s next-bit prediction from `ξ`'s. -/
noncomputable def klStep (μ ξ : List Bool → ℝ) (x : List Bool) : ℝ :=
  cond μ x false * log (cond μ x false / cond ξ x false) +
    cond μ x true * log (cond μ x true / cond ξ x true)

/-- [UNAPPROVED STATEMENT] The paper's `H_n = Σ_{t<n} Σ_{|x|=t} μ(x) h_t(x)`. -/
noncomputable def relEnt (μ ξ : List Bool → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, ∑ x ∈ strs t, μ x * klStep μ ξ x

/-- `Σ_{|x|=n} μ(x) ln(μ(x)/ξ(x))`. -/
noncomputable def klTotal (μ ξ : List Bool → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ strs n, μ x * log (μ x / ξ x)

lemma sum_strs_succ (f : List Bool → ℝ) (n : ℕ) :
    ∑ x ∈ strs (n + 1), f x = ∑ x ∈ strs n, (f (x ++ [false]) + f (x ++ [true])) := by
  have hd : Disjoint ((strs n).image (· ++ [false])) ((strs n).image (· ++ [true])) := by
    rw [Finset.disjoint_left]
    intro q h0 h1
    simp only [Finset.mem_image] at h0 h1
    obtain ⟨a, _, rfl⟩ := h0
    obtain ⟨b, _, hb⟩ := h1
    have := List.append_inj' hb rfl
    simp at this
  rw [strs, Finset.sum_union hd, Finset.sum_image (fun a _ b _ h => concat_injective false h),
    Finset.sum_image (fun a _ b _ h => concat_injective true h), Finset.sum_add_distrib]

section Fn

variable {μ ξ : List Bool → ℝ} {w : ℝ}

lemma sum_strs_eq_one (hμ : IsStrMeasure μ) (n : ℕ) : ∑ x ∈ strs n, μ x = 1 := by
  induction n with
  | zero => simp [strs, hμ.nil]
  | succ n ih =>
    rw [sum_strs_succ]
    simp_rw [← hμ.split]
    exact ih

lemma cond_nonneg (hμ : IsStrMeasure μ) (x : List Bool) (b : Bool) : 0 ≤ cond μ x b :=
  div_nonneg (hμ.nonneg _) (hμ.nonneg _)

lemma cond_add (hμ : IsStrMeasure μ) {x : List Bool} (hx : μ x ≠ 0) :
    cond μ x false + cond μ x true = 1 := by
  unfold cond
  rw [← add_div, ← hμ.split x, div_self hx]

lemma pos_of_dom (hw : 0 < w) (hdom : ∀ x, w * μ x ≤ ξ x) {x : List Bool} (h : 0 < μ x) :
    0 < ξ x :=
  lt_of_lt_of_le (mul_pos hw h) (hdom x)

lemma cond_pos_of_dom (hμ : IsStrMeasure μ) (hw : 0 < w) (hdom : ∀ x, w * μ x ≤ ξ x)
    {x : List Bool} (hx : 0 < μ x) (b : Bool) (hc : 0 < cond μ x b) : 0 < cond ξ x b := by
  have hm : 0 < μ (x ++ [b]) := by
    by_contra h
    have h0 : μ (x ++ [b]) = 0 := le_antisymm (not_lt.1 h) (hμ.nonneg _)
    simp [cond, h0] at hc
  exact div_pos (pos_of_dom hw hdom hm) (pos_of_dom hw hdom hx)

lemma expLoss_nonneg (hμ : IsStrMeasure μ) {l : List Bool → Bool → 𝒴 → ℝ}
    (hl : ∀ x b a, 0 ≤ l x b a ∧ l x b a ≤ 1) (x : List Bool) (a : 𝒴) : 0 ≤ expLoss μ l x a :=
  add_nonneg (mul_nonneg (cond_nonneg hμ x false) (hl x false a).1)
    (mul_nonneg (cond_nonneg hμ x true) (hl x true a).1)

lemma cumLoss_nonneg (hμ : IsStrMeasure μ) {l : List Bool → Bool → 𝒴 → ℝ}
    (hl : ∀ x b a, 0 ≤ l x b a ∧ l x b a ≤ 1) (p : List Bool → 𝒴) (n : ℕ) :
    0 ≤ cumLoss μ l p n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun x _ =>
    mul_nonneg (hμ.nonneg x) (expLoss_nonneg hμ hl x _)

/-- Relative entropy of the next-bit predictions is nonnegative. -/
lemma klStep_nonneg (hμ : IsStrMeasure μ) (hξ : IsStrMeasure ξ) (hw : 0 < w)
    (hdom : ∀ x, w * μ x ≤ ξ x) {x : List Bool} (hx : 0 < μ x) : 0 ≤ klStep μ ξ x := by
  have s0 := sym_ineq (cond μ x false) (cond ξ x false) 0 (cond_nonneg hμ x false)
    (cond_nonneg hξ x false) (cond_pos_of_dom hμ hw hdom hx false)
  have s1 := sym_ineq (cond μ x true) (cond ξ x true) 0 (cond_nonneg hμ x true)
    (cond_nonneg hξ x true) (cond_pos_of_dom hμ hw hdom hx true)
  have hy := cond_add hμ hx.ne'
  have hz := cond_add hξ (pos_of_dom hw hdom hx).ne'
  simp only [mul_zero, Real.exp_zero, mul_one] at s0 s1
  unfold klStep
  linarith

lemma relEnt_nonneg (hμ : IsStrMeasure μ) (hξ : IsStrMeasure ξ) (hw : 0 < w)
    (hdom : ∀ x, w * μ x ≤ ξ x) (n : ℕ) : 0 ≤ relEnt μ ξ n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun x _ => by
    rcases (hμ.nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
    · exact mul_nonneg hpos.le (klStep_nonneg hμ hξ hw hdom hpos)

/-- The per-step inequality at a history `x`, weighted by `μ x`. -/
lemma step_loss_le (hμ : IsStrMeasure μ) (hξ : IsStrMeasure ξ) (hw : 0 < w)
    (hdom : ∀ x, w * μ x ≤ ξ x) {l : List Bool → Bool → 𝒴 → ℝ}
    (hl : ∀ x b a, 0 ≤ l x b a ∧ l x b a ≤ 1) {pξ : List Bool → 𝒴} (hoptξ : IsBayesOpt ξ l pξ)
    (pμ : List Bool → 𝒴) (A : ℝ) (hA : 0 < A) (x : List Bool) :
    μ x * expLoss μ l x (pξ x) ≤ (1 + A) * (μ x * expLoss μ l x (pμ x)) +
      (1 + A / 4 + 1 / A) * (μ x * klStep μ ξ x) := by
  rcases (hμ.nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hξpos := pos_of_dom hw hdom hpos
    have h := step_ineq A hA (cond μ x false) (cond μ x true) (cond ξ x false) (cond ξ x true)
      (cond_nonneg hμ x false) (cond_nonneg hμ x true) (cond_add hμ hpos.ne')
      (cond_nonneg hξ x false) (cond_nonneg hξ x true) (cond_add hξ hξpos.ne')
      (cond_pos_of_dom hμ hw hdom hpos false) (cond_pos_of_dom hμ hw hdom hpos true)
      (l x false (pξ x)) (l x true (pξ x)) (l x false (pμ x)) (l x true (pμ x))
      (hl _ _ _) (hl _ _ _) (hl _ _ _) (hl _ _ _) (hoptξ x (pμ x))
    refine (mul_le_mul_of_nonneg_left h hpos.le).trans (le_of_eq ?_)
    unfold expLoss klStep
    ring

/-- The paper's (Eineq3): `L_ξ ≤ (1+A) L_μ + (1 + A/4 + 1/A) H_n` for every `A > 0`. -/
lemma cumLoss_le_linear (hμ : IsStrMeasure μ) (hξ : IsStrMeasure ξ) (hw : 0 < w)
    (hdom : ∀ x, w * μ x ≤ ξ x) {l : List Bool → Bool → 𝒴 → ℝ}
    (hl : ∀ x b a, 0 ≤ l x b a ∧ l x b a ≤ 1) {pξ : List Bool → 𝒴} (hoptξ : IsBayesOpt ξ l pξ)
    (pμ : List Bool → 𝒴) (A : ℝ) (hA : 0 < A) (n : ℕ) :
    cumLoss μ l pξ n ≤ (1 + A) * cumLoss μ l pμ n + (1 + A / 4 + 1 / A) * relEnt μ ξ n := by
  unfold cumLoss relEnt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => step_loss_le hμ hξ hw hdom hl hoptξ pμ A hA x

/-- The informed predictor is at least as good as any other (the paper's (Lmuopt)). -/
lemma cumLoss_opt_le (hμ : IsStrMeasure μ) {l : List Bool → Bool → 𝒴 → ℝ}
    {pμ : List Bool → 𝒴} (hoptμ : IsBayesOpt μ l pμ) (p : List Bool → 𝒴) (n : ℕ) :
    cumLoss μ l pμ n ≤ cumLoss μ l p n :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (hoptμ x (p x)) (hμ.nonneg x)

/-! ### `H_n ≤ ln(1/w)`: chain rule and dominance -/

lemma term_eq (m M ξb X : ℝ) (hm : 0 ≤ m) (hM : 0 < M) (hX : 0 < X) (hpos : 0 < m → 0 < ξb) :
    M * (m / M * log (m / M / (ξb / X))) = m * log (m / ξb) - m * log (M / X) := by
  rcases hm.eq_or_lt with rfl | hm'
  · simp
  · have hb := hpos hm'
    have e : M * (m / M) = m := by field_simp
    rw [Real.log_div (by positivity) (by positivity), Real.log_div hm'.ne' hM.ne',
      Real.log_div hb.ne' hX.ne', Real.log_div hm'.ne' hb.ne', Real.log_div hM.ne' hX.ne',
      ← mul_assoc, e]
    ring

lemma step_kl_eq (hμ : IsStrMeasure μ) (hw : 0 < w) (hdom : ∀ x, w * μ x ≤ ξ x)
    (x : List Bool) :
    μ x * klStep μ ξ x =
      (μ (x ++ [false]) * log (μ (x ++ [false]) / ξ (x ++ [false])) +
        μ (x ++ [true]) * log (μ (x ++ [true]) / ξ (x ++ [true]))) - μ x * log (μ x / ξ x) := by
  rcases (hμ.nonneg x).eq_or_lt with h0 | hpos
  · have hs := hμ.split x
    have h1 : μ (x ++ [false]) = 0 := by
      linarith [hμ.nonneg (x ++ [false]), hμ.nonneg (x ++ [true])]
    have h2 : μ (x ++ [true]) = 0 := by
      linarith [hμ.nonneg (x ++ [false]), hμ.nonneg (x ++ [true])]
    rw [← h0, h1, h2]; simp
  · have hξpos := pos_of_dom hw hdom hpos
    have t0 := term_eq (μ (x ++ [false])) (μ x) (ξ (x ++ [false])) (ξ x) (hμ.nonneg _) hpos
      hξpos (pos_of_dom hw hdom)
    have t1 := term_eq (μ (x ++ [true])) (μ x) (ξ (x ++ [true])) (ξ x) (hμ.nonneg _) hpos
      hξpos (pos_of_dom hw hdom)
    have hs := hμ.split x
    unfold klStep cond
    rw [mul_add, t0, t1]
    have e : μ (x ++ [false]) * log (μ x / ξ x) + μ (x ++ [true]) * log (μ x / ξ x) =
        μ x * log (μ x / ξ x) := by rw [← add_mul, ← hs]
    linarith

/-- The chain rule: `H_n = Σ_{|x|=n} μ(x) ln(μ(x)/ξ(x))`. -/
lemma relEnt_eq_klTotal (hμ : IsStrMeasure μ) (hξ : IsStrMeasure ξ) (hw : 0 < w)
    (hdom : ∀ x, w * μ x ≤ ξ x) (n : ℕ) : relEnt μ ξ n = klTotal μ ξ n := by
  have hstep : ∀ t, ∑ x ∈ strs t, μ x * klStep μ ξ x = klTotal μ ξ (t + 1) - klTotal μ ξ t := by
    intro t
    unfold klTotal
    rw [sum_strs_succ, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => step_kl_eq hμ hw hdom x
  unfold relEnt
  rw [Finset.sum_congr rfl (fun t _ => hstep t), Finset.sum_range_sub]
  simp [klTotal, strs, hμ.nil, hξ.nil]

lemma klTotal_le (hμ : IsStrMeasure μ) (hw : 0 < w) (hdom : ∀ x, w * μ x ≤ ξ x) (n : ℕ) :
    klTotal μ ξ n ≤ log (1 / w) := by
  calc klTotal μ ξ n ≤ ∑ x ∈ strs n, μ x * log (1 / w) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rcases (hμ.nonneg x).eq_or_lt with h0 | hpos
        · rw [← h0, zero_mul, zero_mul]
        · have hξpos := pos_of_dom hw hdom hpos
          refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos hpos hξpos) ?_) hpos.le
          exact (div_le_div_iff₀ hξpos hw).2 (by linarith [hdom x])
    _ = log (1 / w) := by rw [← Finset.sum_mul, sum_strs_eq_one hμ, one_mul]

/-! ### The unit loss bound -/

/-- [UNAPPROVED STATEMENT] **Hutter's unit loss bound** (`thULoss`), for measures given as
functions on strings.

Let `μ` (the truth) and `ξ` be probability measures on binary sequences with `ξ ≥ w · μ` for
some `w > 0`. Let the loss `l x b a` (history `x`, next bit `b`, action `a`) lie in `[0,1]`, and
let `pμ`, `pξ` be Bayes-optimal for `μ` and `ξ`. Then for every `n`:

* `0 ≤ L_ξ - L_μ ≤ H_n + √(4 L_μ H_n + H_n²)`, and
* `0 ≤ H_n ≤ ln(1/w)`,

where `L_· = cumLoss μ l p· n` are the total `μ`-expected losses and `H_n = relEnt μ ξ n`. -/
theorem unit_loss_bound_fn {μ ξ : List Bool → ℝ} {w : ℝ} (hμ : IsStrMeasure μ)
    (hξ : IsStrMeasure ξ) (hw : 0 < w) (hdom : ∀ x, w * μ x ≤ ξ x)
    {l : List Bool → Bool → 𝒴 → ℝ} (hl : ∀ x b a, 0 ≤ l x b a ∧ l x b a ≤ 1)
    {pμ pξ : List Bool → 𝒴} (hoptμ : IsBayesOpt μ l pμ) (hoptξ : IsBayesOpt ξ l pξ) (n : ℕ) :
    0 ≤ cumLoss μ l pξ n - cumLoss μ l pμ n ∧
    cumLoss μ l pξ n - cumLoss μ l pμ n ≤
      relEnt μ ξ n + Real.sqrt (4 * cumLoss μ l pμ n * relEnt μ ξ n + relEnt μ ξ n ^ 2) ∧
    0 ≤ relEnt μ ξ n ∧ relEnt μ ξ n ≤ log (1 / w) :=
  ⟨sub_nonneg.2 (cumLoss_opt_le hμ hoptμ pξ n),
    opt_bound _ _ _ (cumLoss_nonneg hμ hl pμ n) (relEnt_nonneg hμ hξ hw hdom n)
      (fun A hA => cumLoss_le_linear hμ hξ hw hdom hl hoptξ pμ A hA n),
    relEnt_nonneg hμ hξ hw hdom n,
    (relEnt_eq_klTotal hμ hξ hw hdom n).le.trans (klTotal_le hμ hw hdom n)⟩

/-! ### The general loss bound -/

lemma expLoss_scale (ρ : List Bool → ℝ) (l : List Bool → Bool → 𝒴 → ℝ) (lmin lΔ : ℝ)
    (x : List Bool) (a : 𝒴) :
    expLoss ρ (fun x b a => (l x b a - lmin) / lΔ) x a =
      (expLoss ρ l x a - (cond ρ x false + cond ρ x true) * lmin) / lΔ := by
  unfold expLoss; ring

/-- Rescaling the loss rescales the total expected loss: `L' = (L - n·lmin)/lΔ`. -/
lemma cumLoss_scale (hμ : IsStrMeasure μ) (l : List Bool → Bool → 𝒴 → ℝ) (lmin lΔ : ℝ)
    (p : List Bool → 𝒴) (n : ℕ) :
    cumLoss μ (fun x b a => (l x b a - lmin) / lΔ) p n = (cumLoss μ l p n - n * lmin) / lΔ := by
  have hx : ∀ (x : List Bool) (a : 𝒴),
      μ x * expLoss μ (fun x b a => (l x b a - lmin) / lΔ) x a =
        (μ x * expLoss μ l x a - μ x * lmin) / lΔ := by
    intro x a
    rw [expLoss_scale]
    rcases (hμ.nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [cond_add hμ hpos.ne']; ring
  have inner : ∀ t, ∑ x ∈ strs t, μ x * expLoss μ (fun x b a => (l x b a - lmin) / lΔ) x (p x) =
      (∑ x ∈ strs t, μ x * expLoss μ l x (p x) - lmin) / lΔ := by
    intro t
    rw [Finset.sum_congr rfl (fun x _ => hx x (p x)), ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.sum_mul, sum_strs_eq_one hμ, one_mul]
  unfold cumLoss
  rw [Finset.sum_congr rfl (fun t _ => inner t), ← Finset.sum_div, Finset.sum_sub_distrib]
  simp

/-- [UNAPPROVED STATEMENT] **Hutter's general loss bound** (`thGLoss`): as
`unit_loss_bound_fn`, but with losses in `[lmin, lmin + lΔ]`, `lΔ > 0`:

`0 ≤ L_ξ - L_μ ≤ lΔ H_n + √(4 (L_μ - n·lmin) lΔ H_n + lΔ² H_n²)`.

(Proof as in the paper: rescale the loss to `[0,1]`; the Bayes-optimal predictors do not
change.) -/
theorem general_loss_bound_fn (hμ : IsStrMeasure μ) (hξ : IsStrMeasure ξ) (hw : 0 < w)
    (hdom : ∀ x, w * μ x ≤ ξ x) {l : List Bool → Bool → 𝒴 → ℝ} {lmin lΔ : ℝ} (hΔ : 0 < lΔ)
    (hl : ∀ x b a, lmin ≤ l x b a ∧ l x b a ≤ lmin + lΔ)
    {pμ pξ : List Bool → 𝒴} (hoptμ : IsBayesOpt μ l pμ) (hoptξ : IsBayesOpt ξ l pξ) (n : ℕ) :
    0 ≤ cumLoss μ l pξ n - cumLoss μ l pμ n ∧
    cumLoss μ l pξ n - cumLoss μ l pμ n ≤
      lΔ * relEnt μ ξ n +
        Real.sqrt (4 * (cumLoss μ l pμ n - n * lmin) * lΔ * relEnt μ ξ n +
          lΔ ^ 2 * relEnt μ ξ n ^ 2) := by
  have hl' : ∀ x b a, 0 ≤ (l x b a - lmin) / lΔ ∧ (l x b a - lmin) / lΔ ≤ 1 := fun x b a =>
    ⟨div_nonneg (sub_nonneg.2 (hl x b a).1) hΔ.le,
      (div_le_one hΔ).2 (by linarith [(hl x b a).2])⟩
  have hopt' : ∀ (ρ : List Bool → ℝ) (p : List Bool → 𝒴), IsBayesOpt ρ l p →
      IsBayesOpt ρ (fun x b a => (l x b a - lmin) / lΔ) p := by
    intro ρ p h x a
    rw [expLoss_scale, expLoss_scale]
    exact div_le_div_of_nonneg_right (sub_le_sub_right (h x a) _) hΔ.le
  obtain ⟨h1, h2, -, -⟩ := unit_loss_bound_fn hμ hξ hw hdom hl' (hopt' _ _ hoptμ)
    (hopt' _ _ hoptξ) n
  rw [cumLoss_scale hμ, cumLoss_scale hμ] at h1 h2
  obtain ⟨Lξ, hLξ⟩ : ∃ L, L = cumLoss μ l pξ n := ⟨_, rfl⟩
  obtain ⟨Lμ, hLμ⟩ : ∃ L, L = cumLoss μ l pμ n := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = relEnt μ ξ n := ⟨_, rfl⟩
  rw [← hLξ, ← hLμ] at h1
  rw [← hLξ, ← hLμ, ← hH] at h2
  rw [← hLξ, ← hLμ, ← hH]
  have e : (Lξ - n * lmin) / lΔ - (Lμ - n * lmin) / lΔ = (Lξ - Lμ) / lΔ := by ring
  rw [e] at h1 h2
  refine ⟨?_, ?_⟩
  · by_contra hc
    have : (Lξ - Lμ) / lΔ < 0 := div_neg_of_neg_of_pos (not_le.1 hc) hΔ
    linarith
  · have h5 := mul_le_mul_of_nonneg_left h2 hΔ.le
    have e3 : lΔ * ((Lξ - Lμ) / lΔ) = Lξ - Lμ := by field_simp
    have h6 : lΔ * Real.sqrt (4 * ((Lμ - n * lmin) / lΔ) * H + H ^ 2) =
        Real.sqrt (lΔ ^ 2 * (4 * ((Lμ - n * lmin) / lΔ) * H + H ^ 2)) := by
      rw [Real.sqrt_mul (sq_nonneg lΔ), Real.sqrt_sq hΔ.le]
    have h7 : lΔ ^ 2 * (4 * ((Lμ - n * lmin) / lΔ) * H + H ^ 2) =
        4 * (Lμ - n * lmin) * lΔ * H + lΔ ^ 2 * H ^ 2 := by
      field_simp
    rw [e3, mul_add, h6, h7] at h5
    exact h5

end Fn

/-- The bound is monotone in `H`, and implies the simpler `2D + 2√(L D)`. -/
lemma bound_mono {L H D : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) (hHD : H ≤ D) :
    H + Real.sqrt (4 * L * H + H ^ 2) ≤ D + Real.sqrt (4 * L * D + D ^ 2) ∧
    D + Real.sqrt (4 * L * D + D ^ 2) ≤ 2 * D + 2 * Real.sqrt (L * D) := by
  have hD : 0 ≤ D := hH.trans hHD
  refine ⟨add_le_add hHD (Real.sqrt_le_sqrt ?_), ?_⟩
  · nlinarith [mul_nonneg hL (sub_nonneg.2 hHD), mul_nonneg hH (sub_nonneg.2 hHD),
      mul_nonneg hD (sub_nonneg.2 hHD)]
  · have hs := Real.sqrt_nonneg (L * D)
    have hs2 : Real.sqrt (L * D) ^ 2 = L * D := Real.sq_sqrt (mul_nonneg hL hD)
    have h1 : Real.sqrt (4 * L * D + D ^ 2) ≤ D + 2 * Real.sqrt (L * D) := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      nlinarith [mul_nonneg hD hs]
    linarith

/-- [UNAPPROVED STATEMENT] Bayes-optimal predictors exist when there are finitely many actions
(so the hypotheses of the loss bounds are not vacuous). -/
theorem exists_bayesOpt [Finite 𝒴] [Nonempty 𝒴] (ρ : List Bool → ℝ)
    (l : List Bool → Bool → 𝒴 → ℝ) : ∃ p : List Bool → 𝒴, IsBayesOpt ρ l p := by
  choose p hp using fun x => Finite.exists_min (fun a => expLoss ρ l x a)
  exact ⟨p, hp⟩

/-! ### For a countable class of measures (`Posterior.lean`) -/

section Measure

variable (Q : ℕ → Measure (ℕ → Bool)) (w : ℕ → ENNReal)

/-- The truth `Q i₀` as a real function on strings. -/
noncomputable def truthFn (i₀ : ℕ) : List Bool → ℝ := fun x => (Q i₀ (cyl x)).toReal

/-- The Bayes mixture `ξ = Σ w_i Q_i` as a real function on strings. -/
noncomputable def mixFn : List Bool → ℝ := fun x => (mix Q w x).toReal

lemma isStrMeasure_measure (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P] :
    IsStrMeasure (fun x => (P (cyl x)).toReal) where
  nonneg _ := ENNReal.toReal_nonneg
  nil := by
    have : cyl [] = (Set.univ : Set (ℕ → Bool)) := by ext ω; simp [cyl, pre]
    simp [this]
  split x := by
    rw [measure_cyl_split P x, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

variable [∀ i, IsProbabilityMeasure (Q i)]

lemma isStrMeasure_truthFn (i₀ : ℕ) : IsStrMeasure (truthFn Q i₀) :=
  isStrMeasure_measure (Q i₀)

lemma isStrMeasure_mixFn (hw : ∑' i, w i = 1) : IsStrMeasure (mixFn Q w) := by
  haveI := isProbabilityMeasure_mixMeasure Q w hw
  have h := isStrMeasure_measure (mixMeasure Q w)
  simp_rw [mixMeasure_cyl] at h
  exact h

lemma dom_mixFn (hw : ∑' i, w i = 1) (i₀ : ℕ) (x : List Bool) :
    (w i₀).toReal * truthFn Q i₀ x ≤ mixFn Q w x := by
  unfold truthFn mixFn
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (mix_le_one Q w hw x))
    (ENNReal.le_tsum i₀)

/-- [UNAPPROVED STATEMENT] **Hutter's unit loss bound** for a countable class.

Let `Q i` be a countable class of probability measures on infinite binary sequences, with prior
weights `w` summing to one; let the truth `Q i₀` have `w i₀ ≠ 0`, and let `ξ` be the Bayes
mixture. Let the loss `l x b a` lie in `[0,1]`, and let `pμ`, `pξ` be Bayes-optimal predictors
for the truth and for `ξ`. Write `L_μ`, `L_ξ` for their total expected losses (under the truth)
over the first `n` steps, `H_n` for the relative entropy, `D = ln(1/w i₀)`. Then

`0 ≤ L_ξ - L_μ ≤ H_n + √(4 L_μ H_n + H_n²) ≤ D + √(4 L_μ D + D²) ≤ 2D + 2√(L_μ D)`. -/
theorem unit_loss_bound (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0)
    {l : List Bool → Bool → 𝒴 → ℝ} (hl : ∀ x b a, 0 ≤ l x b a ∧ l x b a ≤ 1)
    {pμ pξ : List Bool → 𝒴} (hoptμ : IsBayesOpt (truthFn Q i₀) l pμ)
    (hoptξ : IsBayesOpt (mixFn Q w) l pξ) (n : ℕ) :
    0 ≤ cumLoss (truthFn Q i₀) l pξ n - cumLoss (truthFn Q i₀) l pμ n ∧
    cumLoss (truthFn Q i₀) l pξ n - cumLoss (truthFn Q i₀) l pμ n ≤
      relEnt (truthFn Q i₀) (mixFn Q w) n +
        Real.sqrt (4 * cumLoss (truthFn Q i₀) l pμ n * relEnt (truthFn Q i₀) (mixFn Q w) n +
          relEnt (truthFn Q i₀) (mixFn Q w) n ^ 2) ∧
    relEnt (truthFn Q i₀) (mixFn Q w) n ≤ log (1 / (w i₀).toReal) ∧
    cumLoss (truthFn Q i₀) l pξ n - cumLoss (truthFn Q i₀) l pμ n ≤
      log (1 / (w i₀).toReal) +
        Real.sqrt (4 * cumLoss (truthFn Q i₀) l pμ n * log (1 / (w i₀).toReal) +
          log (1 / (w i₀).toReal) ^ 2) ∧
    cumLoss (truthFn Q i₀) l pξ n - cumLoss (truthFn Q i₀) l pμ n ≤
      2 * log (1 / (w i₀).toReal) +
        2 * Real.sqrt (cumLoss (truthFn Q i₀) l pμ n * log (1 / (w i₀).toReal)) := by
  have hwt : w i₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hw ▸ ENNReal.le_tsum i₀)
  have hwpos : 0 < (w i₀).toReal := ENNReal.toReal_pos hi₀ hwt
  have hμ := isStrMeasure_truthFn Q i₀
  obtain ⟨h1, h2, h3, h4⟩ := unit_loss_bound_fn hμ (isStrMeasure_mixFn Q w hw) hwpos
    (dom_mixFn Q w hw i₀) hl hoptμ hoptξ n
  obtain ⟨m1, m2⟩ := bound_mono (cumLoss_nonneg hμ hl pμ n) h3 h4
  exact ⟨h1, h2, h4, h2.trans m1, (h2.trans m1).trans m2⟩

end Measure

end HsiLean.LossBound

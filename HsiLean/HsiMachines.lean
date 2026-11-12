-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-12 and has NOT been reviewed by Nathan.
import HsiLean.WshEquiv
import HsiLean.HsiRateLength
import HsiLean.LossBound

/-!
# The paper's main line, about MACHINES

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-12. Not reviewed by Nathan.

Source: `paper/ALT format.tex` — `cor:um=umum=solind=hsi` (HSI = SolInd) and §"Optimality
properties" (`eq:hsi-error-bound`, `eq:hsi-convergence`), read with dataset items conditioned on
their length (Nathan's reading, 2026-11-11; `HsiRateLength.lean`).

This file only JOINS two results that are already proven:

* `hsi_eq_solomonoff` (`WshEquiv.lean`): for an effective enumeration `V` of machines containing
  every UTM, the HSI priors over `V` are exactly the Solomonoff priors of UTMs, off `ε`;
* `hsi_rate_length` (`HsiRateLength.lean`): the convergence rate of the dataset predictor.

The one bridge needed: the rate is stated for `Semimeasure`s, and the paper's `P_M = λ_M`
(`Machine.lam`, which is `1` at `ε`) was only a function. `Machine.lamSm` packages it as a
`Semimeasure`. (`Machine.sm`, used inside `WshEquiv.lean`, differs from it only at `ε`.)

## Results

* `Machine.lamSm` — `λ_M` as a `Semimeasure`.
* `hsi_machines` — the headline.
* `hsi_machines_enum` — the same for the enumeration of ALL machines and any machine as truth.
* `mixL_singleton_machines` — the predictor in the rate is the HSI prior of part (a): on a single
  item it is `Σ_k w_k λ_{V k}`.

## Decisions (added later in the same run)

`LossBound.lean` proves Hutter's unit loss bound with the mixture allowed to be a semimeasure.
Instantiated here:

* `hsi_loss_bound` — for any enumeration `ν` of semimeasures, weights `w`, and a truth `ν k` that
  is a measure: acting Bayes-optimally for the HSI mixture loses at most
  `D + √(4 L_μ D + D²)`, `D = ln(1/w k)`, more than acting Bayes-optimally for the truth.
* `hsi_machines_loss` — the same about machines, joined with "the HSI prior is a UTM's
  Solomonoff prior". Here the data is ONE binary sequence predicted bit by bit (Hutter's
  setting), not a dataset of items.
-/

open MeasureTheory ProbabilityTheory Filter ENNReal Topology
open HsiLean.Rate HsiLean.HsiRate HsiLean.HsiRateLength

namespace HsiLean.Monotone

/-- [UNAPPROVED STATEMENT] `λ_M` (the paper's `P_M`: `1` at the empty string, the machine's
output measure elsewhere) as a `Semimeasure`. -/
noncomputable def Machine.lamSm (M : Machine) : Semimeasure where
  toFun := M.lam
  empty_le_one := by simp [Machine.lam]
  extend_le x := by
    rw [M.lam_of_ne (by simp), M.lam_of_ne (by simp)]
    refine (M.sm.extend_le x).trans ?_
    by_cases hx : x = []
    · subst hx; simpa [Machine.lam] using M.sm.empty_le_one
    · rw [M.lam_of_ne hx]

@[simp] theorem Machine.lamSm_apply (M : Machine) (x : List Bool) : M.lamSm x = M.lam x := rfl

/-- [UNAPPROVED STATEMENT] The dataset predictor of the rate theorems, on a single item `a` and
with no data seen, is the HSI prior `Σ_k w_k λ_{V k}(a)` — the same function that part (a) of
`hsi_machines` identifies with a UTM's Solomonoff prior. -/
theorem mixL_singleton_machines (V : ℕ → Machine) (w : Weights) (a : List Bool) :
    mixL (contentModel fun k => (V k).lamSm) w.toFun [a] = ∑' k, w k * (V k).lam a := by
  simp [mixL, lik, contentModel]

/-- [UNAPPROVED STATEMENT] **The paper's main claims, about machines.**

Let `V` be an effective enumeration of monotone machines containing every UTM, and `w` any
lower-semicomputable, everywhere-positive weights with `Σ w ≤ 1`. Let `len` be a distribution
over lengths, `k₀` any index, and `X 0, X 1, …` independent random finite strings, each drawn by
picking a length `n` with probability `len n` and then content `x` of that length with
probability `λ_{V k₀}(x)`. Write `e n` for the excess log-loss (bits) on item `n` of the HSI
predictor (the mixture `Σ_k w_k λ_{V k}` conditioned on items `0..n-1`, each item's probability
read as content-given-length) relative to the true machine `V k₀`. Then

(a) the HSI prior `Σ_k w_k λ_{V k}` equals `λ_U` for some UTM `U`, on every non-empty string;
(b) each `e n` is integrable with expectation `≥ 0`; the expectations are summable with total
    `≤ -log₂ w k₀`; for every `ε > 0` at most `-log₂ w k₀ / ε` positions have expected excess
    above `ε`; and the expected excess tends to `0`. -/
theorem hsi_machines {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (List Bool)] [MeasurableSingletonClass (List Bool)]
    (V : ℕ → Machine) (hV : UniformlyCE V) (hU : ∀ U : Machine, IsUTM U → ∃ k, V k = U)
    (w : Weights) (len : ℕ → ℝ≥0∞) (hlen : ∑' n, len n ≤ 1)
    (k₀ : ℕ) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = len x.length * (V k₀).lam x) :
    (∃ U : Machine, IsUTM U ∧ ∀ x : List Bool, x ≠ [] → ∑' k, w k * (V k).lam x = U.lam x) ∧
    (∀ n, Integrable (excessAt (contentModel fun k => (V k).lamSm) w.toFun k₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (contentModel fun k => (V k).lamSm) w.toFun k₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (contentModel fun k => (V k).lamSm) w.toFun k₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (contentModel fun k => (V k).lamSm) w.toFun k₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun k₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (contentModel fun k => (V k).lamSm) w.toFun k₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω,
            excessAt (contentModel fun k => (V k).lamSm) w.toFun k₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun k₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (contentModel fun k => (V k).lamSm) w.toFun k₀ X n ω ∂Pr)
      atTop (𝓝 0) := by
  refine ⟨?_, hsi_rate_length len hlen (fun k => (V k).lamSm) w k₀ Pr X hX hind hlaw⟩
  have hmem : (fun x : {x : List Bool // x ≠ []} => ∑' k, w k * (V k).lam x.1) ∈
      {f : {x : List Bool // x ≠ []} → ℝ≥0∞ |
        ∃ w : Weights, f = fun x => ∑' k, w k * (V k).lam x.1} := ⟨w, rfl⟩
  rw [hsi_eq_solomonoff V hV hU] at hmem
  obtain ⟨U, hUtm, hf⟩ := hmem
  exact ⟨U, hUtm, fun x hx => congrFun hf ⟨x, hx⟩⟩

/-- [UNAPPROVED STATEMENT] `hsi_machines` for the standard enumeration of ALL monotone machines
and an arbitrary machine `M` as the truth: there is an index `k₀` of `M` (so `w k₀ > 0`) for
which (a) and (b) of `hsi_machines` hold. The hypotheses on `V` are discharged. -/
theorem hsi_machines_enum {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (List Bool)] [MeasurableSingletonClass (List Bool)]
    (w : Weights) (M : Machine) (len : ℕ → ℝ≥0∞) (hlen : ∑' n, len n ≤ 1)
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = len x.length * M.lam x) :
    (∃ U : Machine, IsUTM U ∧
      ∀ x : List Bool, x ≠ [] → ∑' k, w k * (enumMachine k).lam x = U.lam x) ∧
    ∃ k₀, enumMachine k₀ = M ∧ 0 < w k₀ ∧
    (∀ n, Integrable (excessAt (contentModel fun k => (enumMachine k).lamSm) w.toFun k₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (contentModel fun k => (enumMachine k).lamSm) w.toFun k₀ X n ω ∂Pr) ∧
    (Summable (fun n =>
        ∫ ω, excessAt (contentModel fun k => (enumMachine k).lamSm) w.toFun k₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (contentModel fun k => (enumMachine k).lamSm) w.toFun k₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun k₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω,
          excessAt (contentModel fun k => (enumMachine k).lamSm) w.toFun k₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω,
            excessAt (contentModel fun k => (enumMachine k).lamSm) w.toFun k₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun k₀).toReal / ε) ∧
    Tendsto (fun n =>
      ∫ ω, excessAt (contentModel fun k => (enumMachine k).lamSm) w.toFun k₀ X n ω ∂Pr)
      atTop (𝓝 0) := by
  obtain ⟨k₀, rfl⟩ := enumMachine_complete M
  have h := hsi_machines enumMachine enumMachine_uniformlyCE
    (fun U _ => enumMachine_complete U) w len hlen k₀ Pr X hX hind hlaw
  exact ⟨h.1, k₀, rfl, w.pos k₀, h.2⟩

/-! ## Decisions: Hutter's loss bound for HSI -/

open HsiLean.LossBound

/-- A semimeasure as a real-valued function on strings. -/
noncomputable def semFn (μ : Semimeasure) : List Bool → ℝ := fun x => (μ x).toReal

lemma sem_ne_top (μ : Semimeasure) (x : List Bool) : μ x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (apply_le_one μ x)

lemma isStrSemi_semFn (μ : Semimeasure) : IsStrSemi (semFn μ) where
  nonneg _ := ENNReal.toReal_nonneg
  nil_le := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top μ.empty_le_one
    simpa [semFn] using h
  split_le x := by
    unfold semFn
    rw [← ENNReal.toReal_add (sem_ne_top μ _) (sem_ne_top μ _)]
    exact ENNReal.toReal_mono (sem_ne_top μ x) (μ.extend_le x)

lemma isStrMeasure_semFn (μ : Semimeasure) (h1 : μ [] = 1)
    (hadd : ∀ x, μ x = μ (x ++ [false]) + μ (x ++ [true])) : IsStrMeasure (semFn μ) where
  nonneg _ := ENNReal.toReal_nonneg
  nil := by simp [semFn, h1]
  split x := by
    unfold semFn
    rw [← ENNReal.toReal_add (sem_ne_top μ _) (sem_ne_top μ _), ← hadd x]

lemma dom_semFn (ν : ℕ → Semimeasure) (w : Weights) (k : ℕ) (x : List Bool) :
    (w k).toReal * semFn (ν k) x ≤ semFn (mixture ν w) x := by
  unfold semFn
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (sem_ne_top (mixture ν w) x) (le_mixture ν w k x)

/-- [UNAPPROVED STATEMENT] **Hutter's unit loss bound for an HSI mixture.**

Let `ν` be any family of semimeasures and `w` weights (positive, `Σ w ≤ 1`). Let the truth
`ν k` be a measure (`1` at the empty string, additive over the next bit). One binary sequence
is drawn from `ν k` and predicted bit by bit; at history `x` an action `a` costs `l x b a ∈ [0,1]`
if the next bit is `b`. Let `pμ` act Bayes-optimally for the truth and `pξ` Bayes-optimally for
the HSI mixture `Σ_j w_j ν_j` (a semimeasure). With `L_·` the total expected losses over the
first `n` steps, `H_n` the relative entropy and `D = ln(1 / w k)`:

`0 ≤ L_ξ - L_μ ≤ H_n + √(4 L_μ H_n + H_n²)`, `H_n ≤ D`, and so
`L_ξ - L_μ ≤ D + √(4 L_μ D + D²) ≤ 2D + 2√(L_μ D)`. -/
theorem hsi_loss_bound {𝒴 : Type*} (ν : ℕ → Semimeasure) (w : Weights) (k : ℕ)
    (hk1 : ν k [] = 1) (hkadd : ∀ x, ν k x = ν k (x ++ [false]) + ν k (x ++ [true]))
    {l : List Bool → Bool → 𝒴 → ℝ} (hl : ∀ x b a, 0 ≤ l x b a ∧ l x b a ≤ 1)
    {pμ pξ : List Bool → 𝒴} (hoptμ : IsBayesOpt (semFn (ν k)) l pμ)
    (hoptξ : IsBayesOpt (semFn (mixture ν w)) l pξ) (n : ℕ) :
    0 ≤ cumLoss (semFn (ν k)) l pξ n - cumLoss (semFn (ν k)) l pμ n ∧
    cumLoss (semFn (ν k)) l pξ n - cumLoss (semFn (ν k)) l pμ n ≤
      relEnt (semFn (ν k)) (semFn (mixture ν w)) n +
        Real.sqrt (4 * cumLoss (semFn (ν k)) l pμ n * relEnt (semFn (ν k)) (semFn (mixture ν w)) n
          + relEnt (semFn (ν k)) (semFn (mixture ν w)) n ^ 2) ∧
    relEnt (semFn (ν k)) (semFn (mixture ν w)) n ≤ Real.log (1 / (w k).toReal) ∧
    cumLoss (semFn (ν k)) l pξ n - cumLoss (semFn (ν k)) l pμ n ≤
      Real.log (1 / (w k).toReal) +
        Real.sqrt (4 * cumLoss (semFn (ν k)) l pμ n * Real.log (1 / (w k).toReal) +
          Real.log (1 / (w k).toReal) ^ 2) ∧
    cumLoss (semFn (ν k)) l pξ n - cumLoss (semFn (ν k)) l pμ n ≤
      2 * Real.log (1 / (w k).toReal) +
        2 * Real.sqrt (cumLoss (semFn (ν k)) l pμ n * Real.log (1 / (w k).toReal)) := by
  have hwt : w k ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum k).trans w.tsum_le_one)
  have hwpos : 0 < (w k).toReal := ENNReal.toReal_pos (w.pos k).ne' hwt
  have hμ := isStrMeasure_semFn (ν k) hk1 hkadd
  obtain ⟨h1, h2, h3, h4⟩ := unit_loss_bound_fn hμ (isStrSemi_semFn (mixture ν w)) hwpos
    (dom_semFn ν w k) hl hoptμ hoptξ n
  obtain ⟨m1, m2⟩ := bound_mono (cumLoss_nonneg hμ hl pμ n) h3 h4
  exact ⟨h1, h2, h4, h2.trans m1, (h2.trans m1).trans m2⟩

/-- [UNAPPROVED STATEMENT] The HSI prior over an effective enumeration of machines containing
every UTM is the Solomonoff prior of some UTM, off the empty string (part (a) of
`hsi_machines`, on its own). -/
theorem hsi_prior_eq_utm (V : ℕ → Machine) (hV : UniformlyCE V)
    (hU : ∀ U : Machine, IsUTM U → ∃ k, V k = U) (w : Weights) :
    ∃ U : Machine, IsUTM U ∧ ∀ x : List Bool, x ≠ [] → ∑' k, w k * (V k).lam x = U.lam x := by
  have hmem : (fun x : {x : List Bool // x ≠ []} => ∑' k, w k * (V k).lam x.1) ∈
      {f : {x : List Bool // x ≠ []} → ℝ≥0∞ |
        ∃ w : Weights, f = fun x => ∑' k, w k * (V k).lam x.1} := ⟨w, rfl⟩
  rw [hsi_eq_solomonoff V hV hU] at hmem
  obtain ⟨U, hUtm, hf⟩ := hmem
  exact ⟨U, hUtm, fun x hx => congrFun hf ⟨x, hx⟩⟩

/-- [UNAPPROVED STATEMENT] **HSI's decisions, about machines.**

Let `V` be an effective enumeration of monotone machines containing every UTM, `w` weights, and
let the true machine `V k₀` have a `λ` that is a measure (additive over the next bit). One
binary sequence is drawn from `λ_{V k₀}` and predicted bit by bit with losses in `[0,1]`. Then

(a) the HSI prior `Σ_k w_k λ_{V k}` is `λ_U` for some UTM `U`, on every non-empty string; and
(b) acting Bayes-optimally for the HSI prior (the mixture
    `mixture (fun k => (V k).lamSm) w`, whose value at `x` is `Σ_k w_k λ_{V k}(x)`) has total
    expected loss over `n` steps at most `D + √(4 L_μ D + D²) ≤ 2D + 2√(L_μ D)` above that of
    acting Bayes-optimally for the true machine, `D = ln(1 / w k₀)`, and never below it. -/
theorem hsi_machines_loss {𝒴 : Type*} (V : ℕ → Machine) (hV : UniformlyCE V)
    (hU : ∀ U : Machine, IsUTM U → ∃ k, V k = U) (w : Weights) (k₀ : ℕ)
    (hadd : ∀ x, (V k₀).lam x = (V k₀).lam (x ++ [false]) + (V k₀).lam (x ++ [true]))
    {l : List Bool → Bool → 𝒴 → ℝ} (hl : ∀ x b a, 0 ≤ l x b a ∧ l x b a ≤ 1)
    {pμ pξ : List Bool → 𝒴} (hoptμ : IsBayesOpt (semFn (V k₀).lamSm) l pμ)
    (hoptξ : IsBayesOpt (semFn (mixture (fun k => (V k).lamSm) w)) l pξ) (n : ℕ) :
    (∃ U : Machine, IsUTM U ∧ ∀ x : List Bool, x ≠ [] → ∑' k, w k * (V k).lam x = U.lam x) ∧
    0 ≤ cumLoss (semFn (V k₀).lamSm) l pξ n - cumLoss (semFn (V k₀).lamSm) l pμ n ∧
    cumLoss (semFn (V k₀).lamSm) l pξ n - cumLoss (semFn (V k₀).lamSm) l pμ n ≤
      Real.log (1 / (w k₀).toReal) +
        Real.sqrt (4 * cumLoss (semFn (V k₀).lamSm) l pμ n * Real.log (1 / (w k₀).toReal) +
          Real.log (1 / (w k₀).toReal) ^ 2) ∧
    cumLoss (semFn (V k₀).lamSm) l pξ n - cumLoss (semFn (V k₀).lamSm) l pμ n ≤
      2 * Real.log (1 / (w k₀).toReal) +
        2 * Real.sqrt (cumLoss (semFn (V k₀).lamSm) l pμ n * Real.log (1 / (w k₀).toReal)) := by
  have h := hsi_loss_bound (fun k => (V k).lamSm) w k₀ (by simp [Machine.lam]) hadd hl
    hoptμ hoptξ n
  exact ⟨hsi_prior_eq_utm V hV hU w, h.1, h.2.2.2.1, h.2.2.2.2⟩

end HsiLean.Monotone

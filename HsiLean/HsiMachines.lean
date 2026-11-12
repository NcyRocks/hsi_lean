-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-12 and has NOT been reviewed by Nathan.
import HsiLean.WshEquiv
import HsiLean.HsiRateLength

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

end HsiLean.Monotone

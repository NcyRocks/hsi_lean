-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.HsiRate

/-!
# HSI end to end, with the STOPPING-MODEL reading of a dataset item

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-11. Not reviewed by Nathan.

Source: `paper/ALT format.tex`, `lm:bijection` (`ν⁻({x}) = ν(x) - ν(x0) - ν(x1)`),
§"Optimality properties" (`eq:hsi-error-bound`, `eq:hsi-convergence`) and
`thm:enums-of-ums=ums`.

Of the three readings of "the probability a model `ν` gives to a dataset item `x`" —
(a) conditioned on length (`HsiRateLength.lean`), (b) the stopping model, (c) prefix-free items
(`HsiRate.lean`) — this file uses **(b)**: the probability that a machine's output is *exactly*
`x`, that is, the mass `ν x - ν (x0) - ν (x1)` that `ν` loses at `x`.

* `halt μ x` — the halting mass `μ x - (μ (x0) + μ (x1))`.
* `tsum_halt_le_one` — the bridge: halting mass sums to at most `μ [] ≤ 1` over ALL finite
  strings. So the hypothesis `model_sub` of `Rate.lean` holds with no restriction on the items.
* `hsi_rate_stop`, `hsi_end_to_end_stop`, `hsi_end_to_end_stop_enum` — the rate and the
  end-to-end theorem under this reading.
* `exists_iid_stop_items` — the hypotheses are not vacuous.

Under this reading the true model must halt with probability one (its halting masses sum to
one): a machine that outputs an infinite string gives every finite item probability zero.
-/

namespace HsiLean.HsiRateStop

open MeasureTheory ProbabilityTheory Filter ENNReal Topology HsiLean.Rate HsiLean.HsiRate

/-- The halting mass of `μ` at `x`: the probability that the output is exactly `x`,
`μ x - μ (x0) - μ (x1)` (the paper's `ν⁻({x})`, `lm:bijection`). -/
noncomputable def halt (μ : Semimeasure) (x : List Bool) : ℝ≥0∞ :=
  μ x - (μ (x ++ [false]) + μ (x ++ [true]))

/-- The enumerated semimeasures under the stopping-model reading: `stopModel ν j x` is the
probability that the `j`-th machine's output is exactly `x`. -/
noncomputable def stopModel (ν : ℕ → Semimeasure) : ℕ → List Bool → ℝ≥0∞ :=
  fun j x => halt (ν j) x

/-! ## The bridge: halting mass sums to at most one over all finite strings -/

/-- Induction on the depth `n` of the tree below `x`: the halting mass of any finite set of
strings extending `x` by at most `n` symbols is at most `μ x`. -/
lemma sum_halt_le_aux (μ : Semimeasure) : ∀ (n : ℕ) (x : List Bool) (s : Finset (List Bool)),
    (∀ a ∈ s, x <+: a) → (∀ a ∈ s, a.length ≤ x.length + n) →
    ∑ a ∈ s, halt μ a ≤ μ x := by
  classical
  intro n
  induction n with
  | zero =>
    intro x s hx hlen
    have hsub : s ⊆ {x} := by
      intro a ha
      rw [Finset.mem_singleton]
      exact ((hx a ha).eq_of_length_le (by simpa using hlen a ha)).symm
    calc ∑ a ∈ s, halt μ a ≤ ∑ a ∈ ({x} : Finset (List Bool)), halt μ a :=
          Finset.sum_le_sum_of_subset hsub
      _ = halt μ x := by simp
      _ ≤ μ x := tsub_le_self
  | succ n ih =>
    intro x s hx hlen
    -- Split off `x` itself; every other element extends `x0` or `x1`.
    have h1 : ∑ a ∈ s.filter (fun a => a = x), halt μ a ≤ halt μ x := by
      have hsub : s.filter (fun a => a = x) ⊆ {x} := by
        intro a ha
        rw [Finset.mem_singleton]
        exact (Finset.mem_filter.mp ha).2
      calc ∑ a ∈ s.filter (fun a => a = x), halt μ a
          ≤ ∑ a ∈ ({x} : Finset (List Bool)), halt μ a := Finset.sum_le_sum_of_subset hsub
        _ = halt μ x := by simp
    have h2 : ∑ a ∈ s.filter (fun a => ¬ a = x), halt μ a
        ≤ μ (x ++ [false]) + μ (x ++ [true]) := by
      have hcover : ∀ a ∈ s.filter (fun a => ¬ a = x),
          ¬ (x ++ [false] <+: a) → x ++ [true] <+: a := by
        intro a ha hna
        obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
        obtain ⟨t, rfl⟩ := hx a ha1
        cases t with
        | nil => exact absurd (by simp) ha2
        | cons b t =>
          cases b with
          | false => exact absurd ⟨t, by simp⟩ hna
          | true => exact ⟨t, by simp⟩
      rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun a => ¬ a = x))
        (fun a => x ++ [false] <+: a)]
      refine add_le_add ?_ ?_
      · refine ih (x ++ [false]) _ (fun a ha => (Finset.mem_filter.mp ha).2) (fun a ha => ?_)
        have := hlen a (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
        simp only [List.length_append, List.length_singleton]
        omega
      · refine ih (x ++ [true]) _
          (fun a ha => hcover a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2)
          (fun a ha => ?_)
        have := hlen a (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
        simp only [List.length_append, List.length_singleton]
        omega
    rw [← Finset.sum_filter_add_sum_filter_not s (fun a => a = x)]
    calc ∑ a ∈ s.filter (fun a => a = x), halt μ a
          + ∑ a ∈ s.filter (fun a => ¬ a = x), halt μ a
        ≤ halt μ x + (μ (x ++ [false]) + μ (x ++ [true])) := add_le_add h1 h2
      _ = μ x := tsub_add_cancel_of_le (μ.extend_le x)

/-- **[UNAPPROVED STATEMENT]** The halting mass of any finite set of strings extending `x` is at
most `μ x`. -/
theorem sum_halt_le (μ : Semimeasure) (x : List Bool) (s : Finset (List Bool))
    (hx : ∀ a ∈ s, x <+: a) : ∑ a ∈ s, halt μ a ≤ μ x :=
  sum_halt_le_aux μ (s.sup List.length) x s hx fun _ ha =>
    (Finset.le_sup (f := List.length) ha).trans (Nat.le_add_left _ _)

/-- **[UNAPPROVED STATEMENT]** The bridge for the stopping model: a semimeasure's halting mass
sums to at most one over ALL finite strings. -/
theorem tsum_halt_le_one (μ : Semimeasure) : ∑' x : List Bool, halt μ x ≤ 1 := by
  refine le_trans ?_ μ.empty_le_one
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s => sum_halt_le μ [] s fun _ _ => List.nil_prefix

/-! ## The rate and the headline, stopping-model reading -/

section Prob

variable [MeasurableSpace (List Bool)] [MeasurableSingletonClass (List Bool)]
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSingletonClass (List Bool)] in
/-- **[UNAPPROVED STATEMENT]** The hypotheses of `Rate.lean` hold for HSI under the
stopping-model reading: items = all finite strings, models = the halting masses of the
enumerated semimeasures, weights = the hyperprior weights `w`, data = independent draws
`X 0, X 1, …`, each equal to `x` with probability `halt (ν j₀) x`. -/
theorem iidFromModel_stopModel (ν : ℕ → Semimeasure) (w : Weights)
    (j₀ : ℕ) (Pr : Measure Ω) (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = halt (ν j₀) x) :
    IIDFromModel (stopModel ν) w.toFun j₀ Pr X :=
  ⟨fun j => tsum_halt_le_one (ν j), w.tsum_le_one, (w.pos j₀).ne', hX, hind, hlaw⟩

/-- **[UNAPPROVED STATEMENT]** The rate of convergence for HSI over datasets, stopping-model
reading. No restriction on the items.

Let `ν` be any family of semimeasures, `w` hyperprior weights, and `X 0, X 1, …` independent
random finite strings, each equal to `x` with probability `halt (ν j₀) x` (the probability that
machine `j₀` outputs exactly `x`). Write `e n` for the excess log-loss (bits) of the conditioned
HSI predictor on item `n`, having seen items `0, …, n-1`, relative to the true model, with
every model's item probability read as its halting mass. Then:

1. each `e n` has a finite expectation, and that expectation is `≥ 0`;
2. the expectations are summable, with total at most `-log₂ w j₀`;
3. for every `ε > 0`, at most `-log₂ w j₀ / ε` positions `n` have expected excess above `ε`;
4. the expected excess tends to `0` (`eq:hsi-convergence`). -/
theorem hsi_rate_stop (ν : ℕ → Semimeasure) (w : Weights)
    (j₀ : ℕ) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = halt (ν j₀) x) :
    (∀ n, Integrable (excessAt (stopModel ν) w.toFun j₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun j₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun j₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr) atTop (𝓝 0) := by
  have h := iidFromModel_stopModel ν w j₀ Pr X hX hind hlaw
  exact ⟨fun n => ⟨integrable_excessAt h n, expected_excess_nonneg h n⟩,
    tsum_expected_excess_le h, fun ε hε => expected_excess_rate h hε, tendsto_expected_excess h⟩

/-- **[UNAPPROVED STATEMENT]** HSI end to end, stopping-model reading: no restriction on the
strings.

Let `ν` be an effective enumeration of semimeasures in which every universal mixture appears
(the hypotheses of the spine theorem `thm:enums-of-ums=ums`), and `w` any admissible hyperprior
weights. Let `X 0, X 1, …` be independent random finite strings, each equal to `x` with
probability `halt (ν j₀) x`. Then

* the HSI mixture `∑ⱼ w j • ν j` is a universal mixture (by the spine theorem), and
* its dataset predictor, with item probabilities read as halting masses, satisfies the rate of
  `hsi_rate_stop`, with constant `-log₂ w j₀`. -/
theorem hsi_end_to_end_stop (ν : ℕ → Semimeasure) (hν_enum : UniformlyEnumerable ν)
    (hν_univ : ContainsAllUniversalMixtures ν) (w : Weights)
    (j₀ : ℕ) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = halt (ν j₀) x) :
    IsUniversalMixture (mixture ν w) ∧
    (∀ n, Integrable (excessAt (stopModel ν) w.toFun j₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun j₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun j₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (stopModel ν) w.toFun j₀ X n ω ∂Pr) atTop (𝓝 0) := by
  refine ⟨?_, hsi_rate_stop ν w j₀ Pr X hX hind hlaw⟩
  have hmem : mixture ν w ∈ MixtureClass ν := ⟨w, rfl⟩
  rw [Wood.mixtureClass_eq_universalMixtures' ν hν_enum hν_univ] at hmem
  exact hmem

/-- **[UNAPPROVED STATEMENT]** HSI end to end, stopping-model reading, for the concrete
enumeration `Wood.enum` and an arbitrary enumerable truth `μ`: the HSI mixture is a universal
mixture, and there is an index `j₀` with `Wood.enum j₀ = μ` (so `w j₀ > 0`) for which the
dataset predictor satisfies the rate with constant `-log₂ w j₀`. -/
theorem hsi_end_to_end_stop_enum (w : Weights) (μ : Semimeasure) (hμ : μ.Enumerable)
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → List Bool)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (x : List Bool), Pr (X n ⁻¹' {x}) = halt μ x) :
    IsUniversalMixture (mixture Wood.enum w) ∧
    ∃ j₀, Wood.enum j₀ = μ ∧ 0 < w.toFun j₀ ∧
    (∀ n, Integrable (excessAt (stopModel Wood.enum) w.toFun j₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (stopModel Wood.enum) w.toFun j₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (stopModel Wood.enum) w.toFun j₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (stopModel Wood.enum) w.toFun j₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun j₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (stopModel Wood.enum) w.toFun j₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω, excessAt (stopModel Wood.enum) w.toFun j₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun j₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (stopModel Wood.enum) w.toFun j₀ X n ω ∂Pr)
      atTop (𝓝 0) := by
  obtain ⟨j₀, rfl⟩ := Wood.enum_complete μ hμ
  exact ⟨⟨Wood.enum, w, Wood.enum_uniformlyEnumerable, Wood.enum_complete, rfl⟩, j₀, rfl,
    w.pos j₀, hsi_rate_stop Wood.enum w j₀ Pr X hX hind hlaw⟩

/-- **[UNAPPROVED STATEMENT]** The hypotheses are not vacuous: whenever the semimeasure `μ`
halts with probability one (`∑ₓ halt μ x = 1`), there is a probability space carrying
independent random finite strings, each equal to `x` with probability `halt μ x`. -/
theorem exists_iid_stop_items (μ : Semimeasure) (hμ : ∑' x : List Bool, halt μ x = 1) :
    ∃ Pr : Measure (ℕ → List Bool), IsProbabilityMeasure Pr ∧
      (∀ n, Measurable (fun ω : ℕ → List Bool => ω n)) ∧
      iIndepFun (fun n (ω : ℕ → List Bool) => ω n) Pr ∧
      ∀ n (x : List Bool), Pr ((fun ω : ℕ → List Bool => ω n) ⁻¹' {x}) = halt μ x := by
  obtain ⟨Pr, hPr, h⟩ := exists_iidFromModel (α := List Bool)
    (fun _ x => halt μ x) (fun j => if j = 0 then 1 else 0) 0
    (fun _ => hμ.le) (by simp) (by simp) hμ
  exact ⟨Pr, hPr, h.meas, h.indep, h.law⟩

end Prob

end HsiLean.HsiRateStop

-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.Wood
import HsiLean.Rate

/-!
# HSI end to end: a universal mixture whose dataset predictor converges at the rate of `Rate.lean`

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-11. Not reviewed by Nathan.

Source: `paper/ALT format.tex`, `thm:enums-of-ums=ums` (the spine theorem, `Wood.lean`) and
§"Optimality properties" (`eq:hsi-error-bound`, `eq:hsi-convergence`; `Rate.lean`).

This file joins the two halves of the paper's main line.

* `PrefixFree A` — no string of `A` is a proper prefix of another.
* `tsum_le_one_of_prefixFree` — the bridge (a Kraft-style inequality): a `Semimeasure` sums to
  at most one over a prefix-free set of strings. This is exactly the hypothesis `model_sub` of
  `Rate.lean`, which `RateCounterexample.lean` shows cannot be dropped.
* `itemModel ν A` — the enumerated semimeasures `ν j`, restricted to the items of `A`
  (the paper: `P_{U_j}(x)` for `x ∈ A`).
* `hsi_rate` — the rate of `Rate.lean` for the dataset predictor built from `ν` and the
  hyperprior weights `w`, with constant `-log₂ w j₀`.
* `hsi_end_to_end` — the headline: for any enumeration as in the spine theorem, the HSI mixture
  is a universal mixture, *and* its dataset predictor satisfies the rate.
* `hsi_end_to_end_enum` — the same for the concrete enumeration `Wood.enum` and *any* enumerable
  semimeasure `μ` that is a probability distribution on `A`: the true model need not be given as
  an index.
* `exists_iid_items` — the hypotheses are not vacuous.

## Which reading of an item's probability this file uses (added 2026-11-11)

There are three readings of "the probability a model `ν` gives to the dataset item `x`":

(a) **conditioned on length** (Nathan's intended reading): given that an item has `n` symbols,
    its content `x` has probability `ν x`; items of any lengths (`HsiRateLength.lean`);
(b) **the stopping model** (the paper's `lm:bijection`): the probability that a machine's output
    is exactly `x`, i.e. `ν x - ν (x0) - ν (x1)` (`HsiRateStop.lean`);
(c) **prefix-free items**: the probability is `ν x`, with items restricted to a prefix-free set
    `A`.

This file uses (c). It is the special case of (a) when all items have one length, and it also
covers prefix-free sets with items of different lengths (e.g. self-delimiting encodings). For
items of arbitrary lengths with no restriction, use `HsiRateLength.lean`.
-/

namespace HsiLean.HsiRate

open MeasureTheory ProbabilityTheory Filter ENNReal Topology HsiLean.Rate

/-- `A` is *prefix-free*: no string of `A` is a proper prefix of another string of `A`. -/
def PrefixFree (A : Set (List Bool)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x <+: y → x = y

/-- The enumerated semimeasures restricted to the items of `A`: `itemModel ν A j a` is the mass
that the `j`-th semimeasure gives to the string `a ∈ A` (the paper: `P_{U_j}(a)`). -/
noncomputable def itemModel (ν : ℕ → Semimeasure) (A : Set (List Bool)) : ℕ → A → ℝ≥0∞ :=
  fun j a => ν j a.1

/-! ## The bridge: semimeasures sum to at most one over a prefix-free set -/

lemma PrefixFree.mono {A B : Set (List Bool)} (hB : PrefixFree B) (hAB : A ⊆ B) :
    PrefixFree A :=
  fun x hx y hy hxy => hB x (hAB hx) y (hAB hy) hxy

/-- Induction on the depth `n` of the tree below `x`: the bridge for finite prefix-free sets all
of whose strings extend `x` by at most `n` symbols. -/
lemma sum_le_aux (μ : Semimeasure) : ∀ (n : ℕ) (x : List Bool) (s : Finset (List Bool)),
    PrefixFree (↑s : Set (List Bool)) → (∀ a ∈ s, x <+: a) →
    (∀ a ∈ s, a.length ≤ x.length + n) → ∑ a ∈ s, μ a ≤ μ x := by
  classical
  intro n
  induction n with
  | zero =>
    intro x s _ hx hlen
    have hsub : s ⊆ {x} := by
      intro a ha
      rw [Finset.mem_singleton]
      exact ((hx a ha).eq_of_length_le (by simpa using hlen a ha)).symm
    calc ∑ a ∈ s, μ a ≤ ∑ a ∈ ({x} : Finset (List Bool)), μ a :=
          Finset.sum_le_sum_of_subset hsub
      _ = μ x := by simp
  | succ n ih =>
    intro x s hs hx hlen
    by_cases hxs : x ∈ s
    · -- `x` itself is in the set, so by prefix-freeness it is the only element.
      have hsub : s ⊆ {x} := by
        intro a ha
        rw [Finset.mem_singleton]
        exact (hs x (Finset.mem_coe.mpr hxs) a (Finset.mem_coe.mpr ha) (hx a ha)).symm
      calc ∑ a ∈ s, μ a ≤ ∑ a ∈ ({x} : Finset (List Bool)), μ a :=
            Finset.sum_le_sum_of_subset hsub
        _ = μ x := by simp
    · -- Otherwise every element extends `x0` or `x1`; split and use `μ x0 + μ x1 ≤ μ x`.
      have hcover : ∀ a ∈ s, ¬ (x ++ [false] <+: a) → x ++ [true] <+: a := by
        intro a ha hna
        obtain ⟨t, rfl⟩ := hx a ha
        cases t with
        | nil => exact absurd (by simpa using ha) hxs
        | cons b t =>
          cases b with
          | false => exact absurd ⟨t, by simp⟩ hna
          | true => exact ⟨t, by simp⟩
      rw [← Finset.sum_filter_add_sum_filter_not s (fun a => x ++ [false] <+: a)]
      refine le_trans (add_le_add ?_ ?_) (μ.extend_le x)
      · refine ih (x ++ [false]) _ (hs.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
          (fun a ha => (Finset.mem_filter.mp ha).2) (fun a ha => ?_)
        have := hlen a (Finset.mem_filter.mp ha).1
        simp only [List.length_append, List.length_singleton]
        omega
      · refine ih (x ++ [true]) _ (hs.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
          (fun a ha => hcover a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2)
          (fun a ha => ?_)
        have := hlen a (Finset.mem_filter.mp ha).1
        simp only [List.length_append, List.length_singleton]
        omega

/-- **[UNAPPROVED STATEMENT]** A semimeasure's total mass on a finite prefix-free set of strings,
all of which extend `x`, is at most its mass on `x`. -/
theorem sum_le_of_prefixFree (μ : Semimeasure) (x : List Bool) (s : Finset (List Bool))
    (hs : PrefixFree (↑s : Set (List Bool))) (hx : ∀ a ∈ s, x <+: a) :
    ∑ a ∈ s, μ a ≤ μ x :=
  sum_le_aux μ (s.sup List.length) x s hs hx fun _ ha =>
    (Finset.le_sup (f := List.length) ha).trans (Nat.le_add_left _ _)

/-- **[UNAPPROVED STATEMENT]** The bridge lemma (Kraft-style): a semimeasure sums to at most one
over any prefix-free set of strings. -/
theorem tsum_le_one_of_prefixFree (μ : Semimeasure) {A : Set (List Bool)} (hA : PrefixFree A) :
    ∑' a : A, μ a.1 ≤ 1 := by
  refine le_trans ?_ μ.empty_le_one
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have h := sum_le_of_prefixFree μ [] (s.map (Function.Embedding.subtype _)) ?_
    (fun a _ => List.nil_prefix)
  · rwa [Finset.sum_map] at h
  · intro a ha b hb hab
    obtain ⟨a', _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp ha)
    obtain ⟨b', _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hb)
    exact hA _ a'.2 _ b'.2 hab

/-! ## The rate for HSI's dataset predictor -/

section Prob

variable {A : Set (List Bool)} [MeasurableSpace A] [MeasurableSingletonClass A]
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSingletonClass A] in
/-- **[UNAPPROVED STATEMENT]** The hypotheses of `Rate.lean` hold for HSI over a prefix-free set
of items: models = the enumerated semimeasures restricted to `A`, weights = the hyperprior
weights `w`, data = independent draws `X 0, X 1, …` from `A`, each with law `ν j₀`. -/
theorem iidFromModel_of_prefixFree (ν : ℕ → Semimeasure) (w : Weights) (hA : PrefixFree A)
    (j₀ : ℕ) (Pr : Measure Ω) (X : ℕ → Ω → A)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (a : A), Pr (X n ⁻¹' {a}) = ν j₀ a.1) :
    IIDFromModel (itemModel ν A) w.toFun j₀ Pr X :=
  ⟨fun j => tsum_le_one_of_prefixFree (ν j) hA, w.tsum_le_one, (w.pos j₀).ne', hX, hind, hlaw⟩

/-- **[UNAPPROVED STATEMENT]** The rate of convergence for HSI over datasets.

Let `ν` be any family of semimeasures, `w` hyperprior weights, `A` a prefix-free set of strings,
and `X 0, X 1, …` independent random items of `A`, each distributed according to `ν j₀`.
Write `e n` for the excess log-loss (bits) of the conditioned HSI predictor on item `n`, having
seen items `0, …, n-1`, relative to the true model `ν j₀`. Then:

1. each `e n` has a finite expectation, and that expectation is `≥ 0`;
2. the expectations are summable, with total at most `-log₂ w j₀`;
3. for every `ε > 0`, at most `-log₂ w j₀ / ε` positions `n` have expected excess above `ε`;
4. the expected excess tends to `0` (`eq:hsi-convergence`). -/
theorem hsi_rate (ν : ℕ → Semimeasure) (w : Weights) (hA : PrefixFree A)
    (j₀ : ℕ) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → A)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (a : A), Pr (X n ⁻¹' {a}) = ν j₀ a.1) :
    (∀ n, Integrable (excessAt (itemModel ν A) w.toFun j₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun j₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun j₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr) atTop (𝓝 0) := by
  have h := iidFromModel_of_prefixFree ν w hA j₀ Pr X hX hind hlaw
  exact ⟨fun n => ⟨integrable_excessAt h n, expected_excess_nonneg h n⟩,
    tsum_expected_excess_le h, fun ε hε => expected_excess_rate h hε, tendsto_expected_excess h⟩

/-! ## The link between the dataset predictor and the HSI mixture -/

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- **[UNAPPROVED STATEMENT]** On a one-item dataset, the dataset probability `mixL` of
`Rate.lean` is the HSI mixture semimeasure `mixture ν w` of `Basic.lean`, evaluated at that
item. (So the predictor in `hsi_rate` is built from the same object the spine theorem is
about.) -/
theorem mixL_singleton (ν : ℕ → Semimeasure) (w : Weights) (a : A) :
    mixL (itemModel ν A) w.toFun [a] = mixture ν w a.1 := by
  simp [mixL, lik, itemModel]

/-! ## The headline -/

/-- **[UNAPPROVED STATEMENT]** HSI end to end.

Let `ν` be an effective enumeration of semimeasures in which every universal mixture appears
(the hypotheses of the spine theorem `thm:enums-of-ums=ums`), and `w` any admissible hyperprior
weights. Let `A` be a prefix-free set of strings and `X 0, X 1, …` independent random items of
`A`, each distributed according to the enumerated semimeasure `ν j₀`. Then

* the HSI mixture `∑ⱼ w j • ν j` is a universal mixture (by the spine theorem), and
* its dataset predictor satisfies the rate of `hsi_rate`, with constant `-log₂ w j₀`. -/
theorem hsi_end_to_end (ν : ℕ → Semimeasure) (hν_enum : UniformlyEnumerable ν)
    (hν_univ : ContainsAllUniversalMixtures ν) (w : Weights) (hA : PrefixFree A)
    (j₀ : ℕ) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → A)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (a : A), Pr (X n ⁻¹' {a}) = ν j₀ a.1) :
    IsUniversalMixture (mixture ν w) ∧
    (∀ n, Integrable (excessAt (itemModel ν A) w.toFun j₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun j₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun j₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (itemModel ν A) w.toFun j₀ X n ω ∂Pr) atTop (𝓝 0) := by
  refine ⟨?_, hsi_rate ν w hA j₀ Pr X hX hind hlaw⟩
  have hmem : mixture ν w ∈ MixtureClass ν := ⟨w, rfl⟩
  rw [Wood.mixtureClass_eq_universalMixtures' ν hν_enum hν_univ] at hmem
  exact hmem

/-- **[UNAPPROVED STATEMENT]** The enumeration `Wood.enum` of all enumerable semimeasures
satisfies the hypotheses of the spine theorem: it is effective and every universal mixture
appears in it. -/
theorem enum_containsAllUniversalMixtures : ContainsAllUniversalMixtures Wood.enum := by
  rintro ξ ⟨ν', w', hen, _, rfl⟩
  exact Wood.enum_complete _ (hen.mixture_enumerable w')

/-- **[UNAPPROVED STATEMENT]** HSI end to end, for the concrete enumeration `Wood.enum` and an
arbitrary enumerable truth.

Let `w` be any admissible hyperprior weights over `Wood.enum`, the enumeration of *all*
enumerable semimeasures. Let `μ` be any enumerable semimeasure, `A` a prefix-free set of
strings, and `X 0, X 1, …` independent random items of `A`, each distributed according to `μ`.
Then the HSI mixture is a universal mixture, and there is an index `j₀` with `Wood.enum j₀ = μ`
(so `w j₀ > 0`) for which the dataset predictor satisfies the rate with constant
`-log₂ w j₀`. -/
theorem hsi_end_to_end_enum (w : Weights) (μ : Semimeasure) (hμ : μ.Enumerable)
    (hA : PrefixFree A) (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → A)
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X Pr)
    (hlaw : ∀ n (a : A), Pr (X n ⁻¹' {a}) = μ a.1) :
    IsUniversalMixture (mixture Wood.enum w) ∧
    ∃ j₀, Wood.enum j₀ = μ ∧ 0 < w.toFun j₀ ∧
    (∀ n, Integrable (excessAt (itemModel Wood.enum A) w.toFun j₀ X n) Pr ∧
        0 ≤ ∫ ω, excessAt (itemModel Wood.enum A) w.toFun j₀ X n ω ∂Pr) ∧
    (Summable (fun n => ∫ ω, excessAt (itemModel Wood.enum A) w.toFun j₀ X n ω ∂Pr) ∧
        ∑' n, ∫ ω, excessAt (itemModel Wood.enum A) w.toFun j₀ X n ω ∂Pr
          ≤ -Real.logb 2 (w.toFun j₀).toReal) ∧
    (∀ ε : ℝ, 0 < ε →
        {n | ε < ∫ ω, excessAt (itemModel Wood.enum A) w.toFun j₀ X n ω ∂Pr}.Finite ∧
        ({n | ε < ∫ ω, excessAt (itemModel Wood.enum A) w.toFun j₀ X n ω ∂Pr}.ncard : ℝ)
          ≤ -Real.logb 2 (w.toFun j₀).toReal / ε) ∧
    Tendsto (fun n => ∫ ω, excessAt (itemModel Wood.enum A) w.toFun j₀ X n ω ∂Pr)
      atTop (𝓝 0) := by
  obtain ⟨j₀, rfl⟩ := Wood.enum_complete μ hμ
  exact ⟨⟨Wood.enum, w, Wood.enum_uniformlyEnumerable, Wood.enum_complete, rfl⟩, j₀, rfl,
    w.pos j₀, hsi_rate Wood.enum w hA j₀ Pr X hX hind hlaw⟩

/-- **[UNAPPROVED STATEMENT]** The hypotheses are not vacuous: whenever a semimeasure `μ` is a
probability distribution on the items of `A` (`∑_{a ∈ A} μ a = 1`), there is a probability
space carrying independent random items of `A`, each distributed according to `μ` — the
coordinate process on `ℕ → A` under the infinite product measure. -/
theorem exists_iid_items (μ : Semimeasure) (hμ : ∑' a : A, μ a.1 = 1) :
    ∃ Pr : Measure (ℕ → A), IsProbabilityMeasure Pr ∧
      (∀ n, Measurable (fun ω : ℕ → A => ω n)) ∧
      iIndepFun (fun n (ω : ℕ → A) => ω n) Pr ∧
      ∀ n (a : A), Pr ((fun ω : ℕ → A => ω n) ⁻¹' {a}) = μ a.1 := by
  obtain ⟨Pr, hPr, h⟩ := exists_iidFromModel (α := A) (fun _ a => μ a.1)
    (fun j => if j = 0 then 1 else 0) 0 (fun _ => hμ.le) (by simp) (by simp) hμ
  exact ⟨Pr, hPr, h.meas, h.indep, h.law⟩

end Prob

end HsiLean.HsiRate

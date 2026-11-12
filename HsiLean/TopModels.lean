-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-12 and has NOT been reviewed by Nathan.
import HsiLean.Posterior

/-!
# "Top models contain truth" (Cohen, Hutter & Nanda, Theorem 3)

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-12. Not reviewed by Nathan.

Source: Cohen, Hutter & Nanda, *Fully General Online Imitation Learning* (arXiv 2102.08686),
Theorem 3 (`thm:truthintop`): `P(∀t: π^d ∈ Π^α_{h<t}) ≥ 1 - α · w(π^d)⁻¹`.

## Setting here (what was dropped)

The paper's models are policies, updated only on the steps where the demonstrator acts. Its
proof uses only the posterior, so here the class is a countable class `Q i` of probability
measures on `ℕ → Bool` with prior weights `w` (`Σ w = 1`), posterior `post Q w i x`
(`Posterior.lean`), and the truth is `Q i₀`. Dropped: actions, observations, the query
indicator `q_t` (steps without an update leave the posterior unchanged, so they add nothing).

`topSet Q w α x` is the paper's `Π^α_x`: the models whose posterior weight is at least `α` times
the total posterior weight of the models ranked at least as high. The paper ranks with ties
broken arbitrarily; here "ranked at least as high as `i`" means "posterior weight `≥` that of
`i`", ALL ties included. That is the smallest set any tie-breaking can give, so the theorem here
implies the paper's for every tie-breaking.

## Proof route — where it departs from the paper

The paper: (1) `z_t = w(π^d | h_{<t})⁻¹` is a nonnegative supermartingale; (2) "by the
supermartingale convergence theorem" `P(∃t: z_t ≥ α⁻¹) ≤ α w(π^d)⁻¹`.

Step (2) is not the convergence theorem but the maximal inequality for nonnegative
supermartingales (Ville's inequality). Mathlib has that only for nonnegative SUBmartingales
(`MeasureTheory.maximal_ineq`). So step (2) is proved directly, by the standard proof of Ville's
inequality specialised to cylinders: let `S` be the set of strings `x` at which the posterior
first drops to `≤ α` (no proper prefix has done so). The cylinders of `S` are disjoint and cover
the bad event; on each, `P(x) ≤ (α / w) ξ(x)`; and the mixture `ξ` gives the disjoint cylinders
total mass at most one. Step (1) is `inv_post_step` below (the paper's display (a)–(c)), kept
for the record; the headline does not use it.

## Results

* `topSet` — `Π^α`.
* `mem_topSet_of_le` — posterior weight `≥ α` puts a model in `Π^α`.
* `inv_post_step` — the supermartingale step for `1 / posterior`.
* `prob_exists_post_le` — `P(∃t: w(truth | x_{<t}) ≤ α) ≤ α / w(truth)`.
* `truth_stays_above` — `P(∀t: w(truth | x_{<t}) > α) ≥ 1 - α / w(truth)`.
* `truth_in_top` — the headline: `P(∀t: truth ∈ Π^α_{x<t}) ≥ 1 - α / w(truth)`.
-/

open MeasureTheory Filter ENNReal Topology HsiLean.Posterior

namespace HsiLean.TopModels

variable (Q : ℕ → Measure (ℕ → Bool)) (w : ℕ → ℝ≥0∞)

open Classical in
/-- [UNAPPROVED STATEMENT] The paper's `Π^α_x`: the models whose posterior weight after `x` is
at least `α` times the total posterior weight of the models with posterior weight at least as
large (ties all included). -/
noncomputable def topSet (α : ℝ≥0∞) (x : List Bool) : Set ℕ :=
  {i | α * (∑' j, if post Q w i x ≤ post Q w j x then post Q w j x else 0) ≤ post Q w i x}

/-- The strings at which the posterior of `i₀` is at most `α`. -/
def bad (α : ℝ≥0∞) (i₀ : ℕ) : Set (List Bool) := {x | post Q w i₀ x ≤ α}

/-- The strings at which the posterior of `i₀` is at most `α` for the first time. -/
def firstBad (α : ℝ≥0∞) (i₀ : ℕ) : Set (List Bool) :=
  {x | x ∈ bad Q w α i₀ ∧ ∀ y, y <+: x → y ∈ bad Q w α i₀ → y = x}

/-! ### Prefixes of a sequence -/

lemma pre_length (ω : ℕ → Bool) (t : ℕ) : (pre ω t).length = t := by simp [pre]

lemma pre_prefix (ω : ℕ → Bool) {s t : ℕ} (h : s ≤ t) : pre ω s <+: pre ω t := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => rw [pre_succ]; exact ih.trans (List.prefix_append _ _)

lemma eq_pre_of_prefix {ω : ℕ → Bool} {t : ℕ} {y : List Bool} (h : y <+: pre ω t) :
    y = pre ω y.length := by
  have hlen : y.length ≤ t := by simpa [pre_length] using h.length_le
  have h2 : y <+: pre ω y.length :=
    List.prefix_of_prefix_length_le h (pre_prefix ω hlen) (by simp [pre_length])
  exact h2.eq_of_length (by simp [pre_length])

lemma exists_firstBad {α : ℝ≥0∞} {i₀ : ℕ} {ω : ℕ → Bool}
    (h : ∃ t, pre ω t ∈ bad Q w α i₀) : ∃ x ∈ firstBad Q w α i₀, ω ∈ cyl x := by
  classical
  refine ⟨pre ω (Nat.find h), ⟨Nat.find_spec h, fun y hy hyb => ?_⟩, mem_cyl_pre ω _⟩
  have hyeq := eq_pre_of_prefix hy
  have h1 : Nat.find h ≤ y.length := Nat.find_min' h (by rw [← hyeq]; exact hyb)
  have h2 : y.length ≤ Nat.find h := by simpa [pre_length] using hy.length_le
  rw [hyeq, le_antisymm h2 h1]

lemma firstBad_pairwiseDisjoint (α : ℝ≥0∞) (i₀ : ℕ) :
    (firstBad Q w α i₀).PairwiseDisjoint cyl := by
  intro x hx y hy hxy
  refine Set.disjoint_left.mpr fun ω hωx hωy => hxy ?_
  have ex : pre ω x.length = x := hωx
  have ey : pre ω y.length = y := hωy
  rcases le_total x.length y.length with h | h
  · have hp : x <+: y := by rw [← ex, ← ey]; exact pre_prefix ω h
    exact hy.2 x hp hx.1
  · have hp : y <+: x := by rw [← ex, ← ey]; exact pre_prefix ω h
    exact (hx.2 y hp hy.1).symm

variable [∀ i, IsProbabilityMeasure (Q i)]

/-! ### `Π^α` contains every model of posterior weight at least `α` -/

/-- [UNAPPROVED STATEMENT] A model with posterior weight at least `α` is in `Π^α` (the first
line of the paper's proof). -/
theorem mem_topSet_of_le (hw : ∑' i, w i = 1) {α : ℝ≥0∞} {i : ℕ} {x : List Bool}
    (h : α ≤ post Q w i x) : i ∈ topSet Q w α x := by
  classical
  have hs : (∑' j, if post Q w i x ≤ post Q w j x then post Q w j x else 0) ≤ 1 :=
    (ENNReal.tsum_le_tsum fun j => by split_ifs <;> simp).trans (tsum_post_le_one Q w hw x)
  change α * _ ≤ post Q w i x
  calc α * (∑' j, if post Q w i x ≤ post Q w j x then post Q w j x else 0)
      ≤ α * 1 := by gcongr
    _ = α := mul_one _
    _ ≤ post Q w i x := h

/-! ### The supermartingale step (the paper's step (1); not used by the headline) -/

lemma mul_inv_post (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0) (y : List Bool)
    (hP : Q i₀ (cyl y) ≠ 0) :
    Q i₀ (cyl y) * (post Q w i₀ y)⁻¹ = mix Q w y / w i₀ := by
  have hwt : w i₀ ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (hw ▸ ENNReal.le_tsum i₀)
  have hPt : Q i₀ (cyl y) ≠ ⊤ := measure_ne_top _ _
  unfold post
  rw [ENNReal.inv_div (Or.inr (ENNReal.mul_ne_top hwt hPt)) (Or.inr (mul_ne_zero hi₀ hP)),
    div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hi₀) (Or.inl hwt)]
  calc Q i₀ (cyl y) * (mix Q w y * ((w i₀)⁻¹ * (Q i₀ (cyl y))⁻¹))
      = mix Q w y * (w i₀)⁻¹ * (Q i₀ (cyl y) * (Q i₀ (cyl y))⁻¹) := by ring
    _ = mix Q w y * (w i₀)⁻¹ := by rw [ENNReal.mul_inv_cancel hP hPt, mul_one]

lemma mul_inv_post_le (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0) (y : List Bool) :
    Q i₀ (cyl y) * (post Q w i₀ y)⁻¹ ≤ mix Q w y / w i₀ := by
  by_cases hP : Q i₀ (cyl y) = 0
  · rw [hP, zero_mul]; simp
  · exact (mul_inv_post Q w hw i₀ hi₀ y hP).le

/-- [UNAPPROVED STATEMENT] The paper's supermartingale step for `z = 1 / posterior of the
truth`: on every cylinder `x` of positive true probability, the integral of `z` at the next step
(the sum over the next bit `b` of `P(xb) · z(xb)`) is at most its integral now (`P(x) · z(x)`). -/
theorem inv_post_step (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0) (x : List Bool)
    (hP : Q i₀ (cyl x) ≠ 0) :
    Q i₀ (cyl (x ++ [false])) * (post Q w i₀ (x ++ [false]))⁻¹ +
        Q i₀ (cyl (x ++ [true])) * (post Q w i₀ (x ++ [true]))⁻¹ ≤
      Q i₀ (cyl x) * (post Q w i₀ x)⁻¹ := by
  rw [mul_inv_post Q w hw i₀ hi₀ x hP, mix_split Q w x, ENNReal.add_div]
  exact add_le_add (mul_inv_post_le Q w hw i₀ hi₀ _) (mul_inv_post_le Q w hw i₀ hi₀ _)

/-! ### The maximal inequality, by first crossings -/

/-- At a string where the truth's posterior is at most `α`, its probability is at most
`α / w` times the mixture's. -/
lemma measure_cyl_le_of_bad (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0) (α : ℝ≥0∞)
    {x : List Bool} (hx : x ∈ bad Q w α i₀) :
    Q i₀ (cyl x) ≤ α * (w i₀)⁻¹ * mixMeasure Q w (cyl x) := by
  have hwt : w i₀ ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (hw ▸ ENNReal.le_tsum i₀)
  have hle : w i₀ * Q i₀ (cyl x) ≤ mix Q w x := ENNReal.le_tsum i₀
  rw [mixMeasure_cyl]
  by_cases hm : mix Q w x = 0
  · rw [hm, le_zero_iff, mul_eq_zero] at hle
    rcases hle with h | h
    · exact absurd h hi₀
    · rw [h]; simp
  · have hmt : mix Q w x ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (mix_le_one Q w hw x)
    have h1 : w i₀ * Q i₀ (cyl x) ≤ α * mix Q w x := (ENNReal.div_le_iff hm hmt).1 hx
    calc Q i₀ (cyl x) = (w i₀)⁻¹ * (w i₀ * Q i₀ (cyl x)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hi₀ hwt, one_mul]
      _ ≤ (w i₀)⁻¹ * (α * mix Q w x) := by gcongr
      _ = α * (w i₀)⁻¹ * mix Q w x := by ring

/-- [UNAPPROVED STATEMENT] The maximal inequality: under the truth `Q i₀`, the probability that
its posterior weight is EVER at most `α` is at most `α / w i₀`. Hypotheses: the prior weights
sum to one and the truth has positive prior weight. -/
theorem prob_exists_post_le (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0) (α : ℝ≥0∞) :
    Q i₀ {ω | ∃ t, post Q w i₀ (pre ω t) ≤ α} ≤ α * (w i₀)⁻¹ := by
  haveI := isProbabilityMeasure_mixMeasure Q w hw
  have hS : (firstBad Q w α i₀).Countable := Set.to_countable _
  have hsub : {ω | ∃ t, post Q w i₀ (pre ω t) ≤ α} ⊆ ⋃ x ∈ firstBad Q w α i₀, cyl x := by
    intro ω h
    obtain ⟨x, hx, hω⟩ := exists_firstBad Q w (α := α) (i₀ := i₀) (ω := ω) h
    exact Set.mem_biUnion hx hω
  calc Q i₀ {ω | ∃ t, post Q w i₀ (pre ω t) ≤ α}
      ≤ Q i₀ (⋃ x ∈ firstBad Q w α i₀, cyl x) := measure_mono hsub
    _ ≤ ∑' x : firstBad Q w α i₀, Q i₀ (cyl x) := measure_biUnion_le _ hS _
    _ ≤ ∑' x : firstBad Q w α i₀, α * (w i₀)⁻¹ * mixMeasure Q w (cyl x) :=
        ENNReal.tsum_le_tsum fun x => measure_cyl_le_of_bad Q w hw i₀ hi₀ α x.2.1
    _ = α * (w i₀)⁻¹ * ∑' x : firstBad Q w α i₀, mixMeasure Q w (cyl x) := ENNReal.tsum_mul_left
    _ = α * (w i₀)⁻¹ * mixMeasure Q w (⋃ x ∈ firstBad Q w α i₀, cyl x) := by
        rw [measure_biUnion hS (firstBad_pairwiseDisjoint Q w α i₀)
          (fun x _ => cyl_measurable x)]
    _ ≤ α * (w i₀)⁻¹ * 1 := by gcongr; exact prob_le_one
    _ = α * (w i₀)⁻¹ := mul_one _

/-- [UNAPPROVED STATEMENT] Under the truth `Q i₀`, with probability at least `1 - α / w i₀` the
posterior weight of the truth stays strictly above `α` at ALL times. -/
theorem truth_stays_above (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0) (α : ℝ≥0∞) :
    1 - α * (w i₀)⁻¹ ≤ Q i₀ {ω | ∀ t, α < post Q w i₀ (pre ω t)} := by
  have hB : MeasurableSet {ω : ℕ → Bool | ∃ t, post Q w i₀ (pre ω t) ≤ α} := by
    have : {ω : ℕ → Bool | ∃ t, post Q w i₀ (pre ω t) ≤ α} =
        ⋃ t, (fun ω => post Q w i₀ (pre ω t)) ⁻¹' Set.Iic α := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iUnion fun t =>
      (measurable_comp_pre (fun x => post Q w i₀ x) t) measurableSet_Iic
  have hG : {ω : ℕ → Bool | ∀ t, α < post Q w i₀ (pre ω t)} =
      {ω | ∃ t, post Q w i₀ (pre ω t) ≤ α}ᶜ := by
    ext ω; simp
  rw [hG, prob_compl_eq_one_sub hB]
  exact tsub_le_tsub_left (prob_exists_post_le Q w hw i₀ hi₀ α) 1

/-- [UNAPPROVED STATEMENT] **Top models contain truth** (Cohen, Hutter & Nanda, Theorem 3).

Let `Q i` be a countable class of probability measures on infinite binary sequences, with prior
weights `w` summing to one, and let the truth `Q i₀` have positive prior weight. Then for every
`α`, with `Q i₀`-probability at least `1 - α / w i₀`, the truth is in the top set `Π^α` after
every finite prefix of the data. -/
theorem truth_in_top (hw : ∑' i, w i = 1) (i₀ : ℕ) (hi₀ : w i₀ ≠ 0) (α : ℝ≥0∞) :
    1 - α * (w i₀)⁻¹ ≤ Q i₀ {ω | ∀ t, i₀ ∈ topSet Q w α (pre ω t)} :=
  (truth_stays_above Q w hw i₀ hi₀ α).trans
    (measure_mono fun _ h t => mem_topSet_of_le Q w hw (h t).le)

end HsiLean.TopModels

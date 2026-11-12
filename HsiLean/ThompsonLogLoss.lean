-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-12 and has NOT been reviewed by Nathan.
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Fintype.BigOperators

/-!
# A per-step on-policy log-loss bound for Thompson sampling

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-12. Not reviewed by Nathan.

Source: `PIBBSS/notes/queue/rl-logloss-vs-solind-2026-11-11.md`, §0 (setting) and §3,
**Theorem 5** — itself written by another Fable run and NOT checked by Nathan. This file is the
check: the argument goes through, with the bookkeeping below.

Theorem 5: for per-step posterior resampling (the Bayesian control rule, interventional
conditioning), for ANY behaviour policy `π` (in particular the Thompson policy itself), at
EVERY time `t`,

  `E^π_μ [ KL( π_μ(· | h_{<t}) ‖ π_T(· | h_{<t}) ) ] ≤ ln(1 / w_μ)`,

for any countable class, with no further assumptions.

## The model (every definition is a design decision — all UNAPPROVED)

* Actions `A` and percepts `E` are finite types. Rewards play no role in Theorem 5, so a percept
  is just an element of `E`.
* A history `Hist A E` is a list of (action, percept) pairs, **most recent step first**
  (`(a, e) :: h` is `h` followed by action `a` and percept `e`). Newest-first makes every
  definition a structural recursion.
* An environment `Env A E` gives `ν h a e`, the probability of percept `e` after history `h` and
  action `a`. `IsSemiEnv`: nonnegative, sums to `≤ 1` over percepts (class members may be
  semimeasures). The truth must sum to exactly `1`.
* A policy `Policy A E` gives `π h a`. `IsPolicy`: nonnegative, sums to `1` over actions.
* `lik ν h` is the interventional likelihood `ν(e_{1:t} ‖ a_{1:t})`: the product of the percept
  probabilities only.
* `Ex π μ t f` is the expectation of `f` over length-`t` histories when `π` acts in `μ`,
  defined by the tower rule: `Ex (t+1) f = Ex t (h ↦ Σ_a Σ_e π(a|h) μ(e|h,a) f(h a e))`.
  No measure theory: finite horizon suffices for a per-step statement. `Ex_one` checks it is a
  probability; `Ex_eq_S0` rewrites it as `Σ_h π-part(h) · lik μ h · f(h)`.
* The class is `ν : ℕ → Env A E` with real weights `w i ≥ 0`, `Σ w ≤ 1`, and a designated
  policy `πd i` for each member. `xi` is the interventional mixture `ξ(h) = Σ_i w_i lik(ν_i, h)`.
* `thompson ν w πd` is `π_T(a | h) = Σ_i w(i | h) πd_i(a | h)` with the interventional posterior
  `w(i | h) = w_i lik(ν_i, h) / ξ(h)` (actions are NOT evidence).
* `klAct p q = Σ_a p(a) ln(p(a)/q(a))`.

## The proof, and how it relates to the note's

The note: `π_T ≥ w(μ|h) π_μ`, so `KL ≤ ln Z_t` with `Z_t = 1/w(μ|h)`; `Z_t` is a nonnegative
supermartingale under `P^π_μ`; Jensen. All three steps are used here, in this form:

1. (`kl_le`) on histories with `lik μ h > 0`: `KL ≤ ln(ξ(h) / (w_μ lik μ h))`.
2. (`pointwise`) Jensen as a tangent line, `ln z ≤ ln(1/w) + w z - 1`, multiplied by `lik μ h`
   so that it holds at EVERY history, including those of probability zero:
   `lik μ h · KL(h) ≤ lik μ h · (ln(1/w) - 1) + ξ(h)`.
3. (`xi_super`, `S0_super`) the supermartingale step: `Σ_e ξ(h a e) ≤ ξ(h)` for every action,
   hence `Σ_h π-part(h) ξ(h) ≤ ξ([]) ≤ 1` for any policy; and the same with equality for `μ`.

One point the note leaves implicit: on histories of `P^π_μ`-probability zero the posterior and
the KL are undefined. Step 2 is stated so that those histories contribute zero.

## Results

* `thompson_per_step` — Theorem 5 (KL form); `thompson_per_step_det` — the `-ln π_T(a*)` form.
* `posterior_uniform`, `thompson_uniform` — the theorem's "with probability `1 - δ`, for all `t`
  at once" clause, at every finite horizon.
* `thompson_per_step_tight` — the bound is attained at every step in a degenerate class (same
  environment, different designated policies), so it cannot be summed.
* `Ex_one`, `Ex_step_one`, `Ex_eq_S0` — sanity checks on the definition of `Ex`.
-/

open Real Finset

namespace HsiLean.ThompsonLogLoss

variable {A E : Type*}

/-- A history: (action, percept) pairs, most recent first. -/
abbrev Hist (A E : Type*) := List (A × E)

/-- An environment: `ν h a e` is the probability of percept `e` after history `h` and action
`a`. -/
abbrev Env (A E : Type*) := Hist A E → A → E → ℝ

/-- A policy: `π h a` is the probability of action `a` after history `h`. -/
abbrev Policy (A E : Type*) := Hist A E → A → ℝ

/-- The interventional likelihood `ν(e_{1:t} ‖ a_{1:t})`: the product of the percept
probabilities along the history. -/
noncomputable def lik (ν : Env A E) : Hist A E → ℝ
  | [] => 1
  | (a, e) :: h => lik ν h * ν h a e

/-- `Σ_a p(a) ln(p(a)/q(a))`. -/
noncomputable def klAct [Fintype A] (p q : A → ℝ) : ℝ := ∑ a, p a * log (p a / q a)

variable [Fintype A] [Fintype E]

/-- [UNAPPROVED STATEMENT] A (semi)environment: nonnegative, percept probabilities sum to at
most one. -/
structure IsSemiEnv (ν : Env A E) : Prop where
  nonneg : ∀ h a e, 0 ≤ ν h a e
  sum_le : ∀ h a, ∑ e, ν h a e ≤ 1

/-- [UNAPPROVED STATEMENT] A policy: nonnegative, action probabilities sum to one. -/
structure IsPolicy (π : Policy A E) : Prop where
  nonneg : ∀ h a, 0 ≤ π h a
  sum_eq : ∀ h, ∑ a, π h a = 1

/-- [UNAPPROVED STATEMENT] The expectation of `f` over the length-`t` histories generated when
policy `π` acts in environment `μ` (the measure `P^π_μ`), by the tower rule. -/
noncomputable def Ex (π : Policy A E) (μ : Env A E) : ℕ → (Hist A E → ℝ) → ℝ
  | 0, f => f []
  | t + 1, f => Ex π μ t (fun h => ∑ a, ∑ e, π h a * μ h a e * f ((a, e) :: h))

/-- `Σ_{|h| = t} π-part(h) · F(h)`: the sum over length-`t` histories weighted by the policy's
action probabilities only. -/
noncomputable def S0 (π : Policy A E) : ℕ → (Hist A E → ℝ) → ℝ
  | 0, F => F []
  | t + 1, F => S0 π t (fun h => ∑ a, π h a * ∑ e, F ((a, e) :: h))

/-- The interventional mixture `ξ(h) = Σ_i w_i ν_i(e ‖ a)`. -/
noncomputable def xi (ν : ℕ → Env A E) (w : ℕ → ℝ) (h : Hist A E) : ℝ :=
  ∑' i, w i * lik (ν i) h

/-- [UNAPPROVED STATEMENT] The Thompson-sampling / Bayesian-control-rule policy with per-step
resampling: `π_T(a | h) = Σ_i w(i | h) πd_i(a | h)`, where `w(i | h) = w_i lik(ν_i, h) / ξ(h)` is
the interventional posterior. -/
noncomputable def thompson (ν : ℕ → Env A E) (w : ℕ → ℝ) (πd : ℕ → Policy A E) : Policy A E :=
  fun h a => (∑' i, w i * lik (ν i) h * πd i h a) / xi ν w h

/-! ### `S0`: monotone, linear, and bounded on superharmonic functions -/

lemma S0_mono {π : Policy A E} (hπ : IsPolicy π) (t : ℕ) {F G : Hist A E → ℝ}
    (h : ∀ x, F x ≤ G x) : S0 π t F ≤ S0 π t G := by
  induction t generalizing F G with
  | zero => simp only [S0]; exact h []
  | succ t ih =>
    simp only [S0]
    exact ih fun x => Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => h _) (hπ.nonneg x a)

lemma S0_lin (π : Policy A E) (c : ℝ) (t : ℕ) (F G : Hist A E → ℝ) :
    S0 π t (fun h => c * F h + G h) = c * S0 π t F + S0 π t G := by
  induction t generalizing F G with
  | zero => simp only [S0]
  | succ t ih =>
    simp only [S0]
    rw [← ih]
    congr 1
    funext x
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

/-- The supermartingale step: if `Σ_e F(h a e) ≤ F(h)` for every history and action, then the
policy-weighted sum of `F` over length-`t` histories is at most `F []`, for any policy. -/
lemma S0_super {π : Policy A E} (hπ : IsPolicy π) {F : Hist A E → ℝ}
    (hF : ∀ h a, ∑ e, F ((a, e) :: h) ≤ F h) (t : ℕ) : S0 π t F ≤ F [] := by
  induction t with
  | zero => simp only [S0]; exact le_rfl
  | succ t ih =>
    simp only [S0]
    refine (S0_mono hπ t fun x => ?_).trans ih
    calc ∑ a, π x a * ∑ e, F ((a, e) :: x) ≤ ∑ a, π x a * F x :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hF x a) (hπ.nonneg x a)
      _ = F x := by rw [← Finset.sum_mul, hπ.sum_eq, one_mul]

lemma S0_harm {π : Policy A E} (hπ : IsPolicy π) {F : Hist A E → ℝ}
    (hF : ∀ h a, ∑ e, F ((a, e) :: h) = F h) (t : ℕ) : S0 π t F = F [] := by
  induction t with
  | zero => simp only [S0]
  | succ t ih =>
    simp only [S0]
    rw [← ih]
    congr 1
    funext x
    simp_rw [hF]
    rw [← Finset.sum_mul, hπ.sum_eq, one_mul]

/-- [UNAPPROVED STATEMENT] The on-policy expectation as a weighted sum: the weight of a history
is its policy part times its interventional likelihood under `μ`. -/
theorem Ex_eq_S0 (π : Policy A E) (μ : Env A E) (t : ℕ) (f : Hist A E → ℝ) :
    Ex π μ t f = S0 π t (fun h => lik μ h * f h) := by
  induction t generalizing f with
  | zero => simp [Ex, S0, lik]
  | succ t ih =>
    simp only [Ex, S0]
    rw [ih]
    congr 1
    funext x
    simp only [lik]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring

/-! ### Likelihoods and the mixture -/

lemma lik_nonneg {ν : Env A E} (hν : IsSemiEnv ν) (h : Hist A E) : 0 ≤ lik ν h := by
  induction h with
  | nil => simp [lik]
  | cons p h ih =>
    obtain ⟨a, e⟩ := p
    simp only [lik]
    exact mul_nonneg ih (hν.nonneg h a e)

lemma env_le_one {ν : Env A E} (hν : IsSemiEnv ν) (h : Hist A E) (a : A) (e : E) :
    ν h a e ≤ 1 :=
  (Finset.single_le_sum (fun e _ => hν.nonneg h a e) (Finset.mem_univ e)).trans (hν.sum_le h a)

lemma lik_le_one {ν : Env A E} (hν : IsSemiEnv ν) (h : Hist A E) : lik ν h ≤ 1 := by
  induction h with
  | nil => simp [lik]
  | cons p h ih =>
    obtain ⟨a, e⟩ := p
    simp only [lik]
    calc lik ν h * ν h a e ≤ 1 * 1 :=
          mul_le_mul ih (env_le_one hν h a e) (hν.nonneg h a e) zero_le_one
      _ = 1 := one_mul 1

lemma policy_le_one {π : Policy A E} (hπ : IsPolicy π) (h : Hist A E) (a : A) : π h a ≤ 1 :=
  (Finset.single_le_sum (fun a _ => hπ.nonneg h a) (Finset.mem_univ a)).trans (hπ.sum_eq h).le

section Class

variable {ν : ℕ → Env A E} {w : ℕ → ℝ} {πd : ℕ → Policy A E}

lemma summable_lik (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (h : Hist A E) : Summable (fun i => w i * lik (ν i) h) :=
  Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 i) (lik_nonneg (hν i) h))
    (fun i => mul_le_of_le_one_right (hw0 i) (lik_le_one (hν i) h)) hws

lemma summable_num (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hπd : ∀ i, IsPolicy (πd i)) (h : Hist A E) (a : A) :
    Summable (fun i => w i * lik (ν i) h * πd i h a) :=
  Summable.of_nonneg_of_le
    (fun i => mul_nonneg (mul_nonneg (hw0 i) (lik_nonneg (hν i) h)) ((hπd i).nonneg h a))
    (fun i => mul_le_of_le_one_right (mul_nonneg (hw0 i) (lik_nonneg (hν i) h))
      (policy_le_one (hπd i) h a))
    (summable_lik hν hw0 hws h)

lemma xi_nonneg (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (h : Hist A E) :
    0 ≤ xi ν w h :=
  tsum_nonneg fun i => mul_nonneg (hw0 i) (lik_nonneg (hν i) h)

/-- Dominance: `ξ(h) ≥ w_i ν_i(h)`. -/
lemma le_xi (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w) (i₀ : ℕ)
    (h : Hist A E) : w i₀ * lik (ν i₀) h ≤ xi ν w h :=
  (summable_lik hν hw0 hws h).le_tsum i₀
    (fun j _ => mul_nonneg (hw0 j) (lik_nonneg (hν j) h))

lemma xi_nil : xi ν w ([] : Hist A E) = ∑' i, w i := by simp [xi, lik]

/-- The mixture is a semimeasure given the actions: `Σ_e ξ(h a e) ≤ ξ(h)`. -/
lemma xi_super (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (h : Hist A E) (a : A) : ∑ e, xi ν w ((a, e) :: h) ≤ xi ν w h := by
  have hsw : ∑' i, ∑ e, w i * lik (ν i) ((a, e) :: h) =
      ∑ e, ∑' i, w i * lik (ν i) ((a, e) :: h) :=
    Summable.tsum_finsetSum (fun e _ => summable_lik hν hw0 hws ((a, e) :: h))
  unfold xi
  rw [← hsw]
  refine Summable.tsum_le_tsum (fun i => ?_)
    (summable_sum fun e _ => summable_lik hν hw0 hws ((a, e) :: h))
    (summable_lik hν hw0 hws h)
  simp only [lik]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_right (lik_nonneg (hν i) h) ((hν i).sum_le h a)) (hw0 i)

/-- `π_T(a | h) ≥ w(i₀ | h) · πd_{i₀}(a | h)`. -/
lemma thompson_ge (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hπd : ∀ i, IsPolicy (πd i)) (i₀ : ℕ) (h : Hist A E) (a : A) :
    w i₀ * lik (ν i₀) h * πd i₀ h a / xi ν w h ≤ thompson ν w πd h a :=
  div_le_div_of_nonneg_right
    ((summable_num hν hw0 hws hπd h a).le_tsum i₀ (fun j _ =>
      mul_nonneg (mul_nonneg (hw0 j) (lik_nonneg (hν j) h)) ((hπd j).nonneg h a)))
    (xi_nonneg hν hw0 h)

/-- Step 1 of the note's proof: at a history the truth gives positive likelihood,
`KL(π_μ ‖ π_T) ≤ ln(1 / w(μ | h)) = ln(ξ(h) / (w_μ μ(h)))`. -/
lemma kl_le (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hπd : ∀ i, IsPolicy (πd i)) (i₀ : ℕ) (hi₀ : 0 < w i₀) (h : Hist A E)
    (hL : 0 < lik (ν i₀) h) :
    klAct (πd i₀ h) (thompson ν w πd h) ≤ log (xi ν w h / (w i₀ * lik (ν i₀) h)) := by
  have hξ := le_xi hν hw0 hws i₀ h
  have hwL : 0 < w i₀ * lik (ν i₀) h := mul_pos hi₀ hL
  have hξpos : 0 < xi ν w h := lt_of_lt_of_le hwL hξ
  have hZ : 0 < xi ν w h / (w i₀ * lik (ν i₀) h) := div_pos hξpos hwL
  unfold klAct
  calc ∑ a, πd i₀ h a * log (πd i₀ h a / thompson ν w πd h a)
      ≤ ∑ a, πd i₀ h a * log (xi ν w h / (w i₀ * lik (ν i₀) h)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rcases ((hπd i₀).nonneg h a).eq_or_lt with h0 | hp
        · rw [← h0, zero_mul, zero_mul]
        · have hT : πd i₀ h a / (xi ν w h / (w i₀ * lik (ν i₀) h)) ≤ thompson ν w πd h a := by
            refine le_trans (le_of_eq ?_) (thompson_ge hν hw0 hws hπd i₀ h a)
            rw [div_div_eq_mul_div]; ring
          have hTpos : 0 < thompson ν w πd h a := lt_of_lt_of_le (div_pos hp hZ) hT
          refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos hp hTpos) ?_) hp.le
          rw [div_le_iff₀ hTpos]
          exact ((div_le_iff₀ hZ).1 hT).trans_eq (mul_comm _ _)
    _ = log (xi ν w h / (w i₀ * lik (ν i₀) h)) := by
        rw [← Finset.sum_mul, (hπd i₀).sum_eq h, one_mul]

/-- Steps 1–2 at EVERY history (also those of probability zero), weighted by the truth's
likelihood: `μ(h) · KL(h) ≤ (ln(1/w_μ) - 1) · μ(h) + ξ(h)`. -/
lemma pointwise (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hπd : ∀ i, IsPolicy (πd i)) (i₀ : ℕ) (hi₀ : 0 < w i₀) (h : Hist A E) :
    lik (ν i₀) h * klAct (πd i₀ h) (thompson ν w πd h) ≤
      (log (1 / w i₀) - 1) * lik (ν i₀) h + xi ν w h := by
  rcases (lik_nonneg (hν i₀) h).eq_or_lt with h0 | hL
  · rw [← h0, zero_mul, mul_zero, zero_add]
    exact xi_nonneg hν hw0 h
  · have hkl := kl_le hν hw0 hws hπd i₀ hi₀ h hL
    have hξ := le_xi hν hw0 hws i₀ h
    have hξpos : 0 < xi ν w h := lt_of_lt_of_le (mul_pos hi₀ hL) hξ
    have hlog : log (xi ν w h / (w i₀ * lik (ν i₀) h)) ≤
        log (1 / w i₀) + xi ν w h / lik (ν i₀) h - 1 := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hξpos hL)
      have e : xi ν w h / (w i₀ * lik (ν i₀) h) = (1 / w i₀) * (xi ν w h / lik (ν i₀) h) := by
        field_simp
      rw [e, Real.log_mul (one_div_pos.2 hi₀).ne' (div_pos hξpos hL).ne']
      linarith
    have h2 := mul_le_mul_of_nonneg_left (hkl.trans hlog) hL.le
    have e1 : lik (ν i₀) h * (xi ν w h / lik (ν i₀) h) = xi ν w h := by field_simp
    have e2 : lik (ν i₀) h * (log (1 / w i₀) + xi ν w h / lik (ν i₀) h - 1) =
        (log (1 / w i₀) - 1) * lik (ν i₀) h + xi ν w h := by
      rw [mul_sub, mul_add, e1]; ring
    rw [e2] at h2
    exact h2

/-- [UNAPPROVED STATEMENT] **Theorem 5: the per-step on-policy bound for Thompson sampling.**

Let `ν i` be a countable class of (semi)environments over finite action and percept types, with
weights `w i ≥ 0`, summable, `Σ w ≤ 1`, and a designated policy `πd i` for each. Let the truth
be `ν i₀`, with `w i₀ > 0` and percept probabilities summing to exactly one. Let `π` be ANY
behaviour policy (for instance `thompson ν w πd` itself). Then at every time `t`, the expected
KL divergence, over the length-`t` histories generated by `π` acting in `ν i₀`, from the truth's
designated policy to the Thompson policy is at most `ln(1 / w i₀)`. -/
theorem thompson_per_step (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hw1 : ∑' i, w i ≤ 1) (hπd : ∀ i, IsPolicy (πd i)) (i₀ : ℕ) (hi₀ : 0 < w i₀)
    (hμ : ∀ h a, ∑ e, ν i₀ h a e = 1) (π : Policy A E) (hπ : IsPolicy π) (t : ℕ) :
    Ex π (ν i₀) t (fun h => klAct (πd i₀ h) (thompson ν w πd h)) ≤ log (1 / w i₀) := by
  rw [Ex_eq_S0]
  have h1 := S0_mono hπ t (pointwise hν hw0 hws hπd i₀ hi₀)
  rw [S0_lin] at h1
  have h3 : S0 π t (lik (ν i₀)) = 1 := by
    have := S0_harm hπ (F := lik (ν i₀)) (fun h a => by
      simp only [lik]; rw [← Finset.mul_sum, hμ, mul_one]) t
    simpa [lik] using this
  have h4 : S0 π t (xi ν w) ≤ 1 :=
    ((S0_super hπ (xi_super hν hw0 hws) t).trans_eq xi_nil).trans hw1
  rw [h3] at h1
  linarith

end Class

/-- [UNAPPROVED STATEMENT] Sanity check on `Ex`: it is a probability (the expectation of the
constant `1` is `1`) when `π` is a policy and `μ` a proper environment. -/
theorem Ex_one {π : Policy A E} (hπ : IsPolicy π) {μ : Env A E}
    (hμ : ∀ h a, ∑ e, μ h a e = 1) (t : ℕ) : Ex π μ t (fun _ => 1) = 1 := by
  rw [Ex_eq_S0]
  have := S0_harm hπ (F := lik μ) (fun h a => by
    simp only [lik]; rw [← Finset.mul_sum, hμ, mul_one]) t
  simpa [lik] using this

/-! ### The uniform-in-time clause of Theorem 5 (Ville's inequality, finite horizon)

The note: "with `P^π_μ`-probability at least `1 - δ`, simultaneously for all `t`,
`KL(π_μ ‖ π_T)(h_{<t}) ≤ ln(1/(w_μ δ))`". Stated here for every finite horizon `n` (the event
"some time-prefix of the length-`n` history is bad" has probability at most `δ`, for every `n`).
A time-prefix of a newest-first history `h` is a list SUFFIX `s <:+ h`.

Proof: the note's Ville step, done by hand. `pot h` is the truth's likelihood once a bad prefix
has occurred and `δ ξ(h)` before; it is superharmonic, starts at most `δ`, and dominates the
likelihood-weighted indicator of the bad event. -/

lemma Ex_mono {π : Policy A E} (hπ : IsPolicy π) {μ : Env A E} (hμ : IsSemiEnv μ) (t : ℕ)
    {f g : Hist A E → ℝ} (h : ∀ x, f x ≤ g x) : Ex π μ t f ≤ Ex π μ t g := by
  rw [Ex_eq_S0, Ex_eq_S0]
  exact S0_mono hπ t fun x => mul_le_mul_of_nonneg_left (h x) (lik_nonneg hμ x)

section Uniform

variable {ν : ℕ → Env A E} {w : ℕ → ℝ} {πd : ℕ → Policy A E}

open Classical in
/-- The stopped potential: the truth's likelihood once some time-prefix `s` has had
`μ(s) ≤ δ ξ(s)` (posterior of the truth `≤ δ w_μ`), and `δ ξ(h)` before that. -/
noncomputable def pot (ν : ℕ → Env A E) (w : ℕ → ℝ) (i₀ : ℕ) (δ : ℝ) (h : Hist A E) : ℝ :=
  if ∃ s, s <:+ h ∧ lik (ν i₀) s ≤ δ * xi ν w s then lik (ν i₀) h else δ * xi ν w h

lemma pot_super (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w) (i₀ : ℕ)
    (hμ : ∀ h a, ∑ e, ν i₀ h a e = 1) {δ : ℝ} (hδ : 0 ≤ δ) (h : Hist A E) (a : A) :
    ∑ e, pot ν w i₀ δ ((a, e) :: h) ≤ pot ν w i₀ δ h := by
  classical
  by_cases hB : ∃ s, s <:+ h ∧ lik (ν i₀) s ≤ δ * xi ν w s
  · have hc : ∀ e, pot ν w i₀ δ ((a, e) :: h) = lik (ν i₀) h * ν i₀ h a e := by
      intro e
      obtain ⟨s, hs, hbad⟩ := hB
      have hB' : ∃ s, s <:+ (a, e) :: h ∧ lik (ν i₀) s ≤ δ * xi ν w s :=
        ⟨s, hs.trans (List.suffix_cons _ _), hbad⟩
      rw [pot, if_pos hB', lik]
    have e1 : pot ν w i₀ δ h = lik (ν i₀) h := by rw [pot, if_pos hB]
    simp_rw [hc]
    exact (show ∑ e, lik (ν i₀) h * ν i₀ h a e = pot ν w i₀ δ h by
      rw [← Finset.mul_sum, hμ, mul_one, e1]).le
  · have hc : ∀ e, pot ν w i₀ δ ((a, e) :: h) ≤ δ * xi ν w ((a, e) :: h) := by
      intro e
      by_cases hB' : ∃ s, s <:+ (a, e) :: h ∧ lik (ν i₀) s ≤ δ * xi ν w s
      · have e2 : pot ν w i₀ δ ((a, e) :: h) = lik (ν i₀) ((a, e) :: h) := by
          rw [pot, if_pos hB']
        obtain ⟨s, hs, hbad⟩ := hB'
        rcases List.suffix_cons_iff.1 hs with hs' | hs'
        · rw [e2, ← hs']; exact hbad
        · exact absurd ⟨s, hs', hbad⟩ hB
      · have e2 : pot ν w i₀ δ ((a, e) :: h) = δ * xi ν w ((a, e) :: h) := by
          rw [pot, if_neg hB']
        exact e2.le
    have e1 : pot ν w i₀ δ h = δ * xi ν w h := by rw [pot, if_neg hB]
    calc ∑ e, pot ν w i₀ δ ((a, e) :: h) ≤ ∑ e, δ * xi ν w ((a, e) :: h) :=
          Finset.sum_le_sum fun e _ => hc e
      _ = δ * ∑ e, xi ν w ((a, e) :: h) := by rw [Finset.mul_sum]
      _ ≤ δ * xi ν w h := mul_le_mul_of_nonneg_left (xi_super hν hw0 hws h a) hδ
      _ = pot ν w i₀ δ h := e1.symm

lemma pot_nil_le (hw1 : ∑' i, w i ≤ 1) (i₀ : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    pot ν w i₀ δ ([] : Hist A E) ≤ δ := by
  classical
  have hxi : xi ν w ([] : Hist A E) ≤ 1 := xi_nil.le.trans hw1
  have hle : δ * xi ν w ([] : Hist A E) ≤ δ :=
    (mul_le_mul_of_nonneg_left hxi hδ).trans_eq (mul_one δ)
  by_cases hB : ∃ s, s <:+ ([] : Hist A E) ∧ lik (ν i₀) s ≤ δ * xi ν w s
  · have e1 : pot ν w i₀ δ ([] : Hist A E) = lik (ν i₀) [] := by rw [pot, if_pos hB]
    obtain ⟨s, hs, hbad⟩ := hB
    have hs0 : s = [] := List.suffix_nil.1 hs
    rw [hs0] at hbad
    rw [e1]
    exact hbad.trans hle
  · have e1 : pot ν w i₀ δ ([] : Hist A E) = δ * xi ν w [] := by rw [pot, if_neg hB]
    rw [e1]
    exact hle

open Classical in
/-- [UNAPPROVED STATEMENT] **Ville's inequality for the truth's posterior, any policy.**
Hypotheses as in `thompson_per_step`, `δ ≥ 0`. For every horizon `n`, the `P^π_μ`-probability
that at SOME time `t ≤ n` the truth's likelihood is at most `δ` times the mixture's (i.e. its
interventional posterior weight `w(μ | h_{<t})` is at most `δ · w_μ`) is at most `δ`. -/
theorem posterior_uniform (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hw1 : ∑' i, w i ≤ 1) (i₀ : ℕ) (hμ : ∀ h a, ∑ e, ν i₀ h a e = 1) (π : Policy A E)
    (hπ : IsPolicy π) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    Ex π (ν i₀) n
      (fun h => if ∃ s, s <:+ h ∧ lik (ν i₀) s ≤ δ * xi ν w s then 1 else 0) ≤ δ := by
  rw [Ex_eq_S0]
  refine (S0_mono hπ n (G := pot ν w i₀ δ) fun h => ?_).trans
    ((S0_super hπ (pot_super hν hw0 hws i₀ hμ hδ) n).trans (pot_nil_le hw1 i₀ hδ))
  by_cases hB : ∃ s, s <:+ h ∧ lik (ν i₀) s ≤ δ * xi ν w s
  · have e1 : pot ν w i₀ δ h = lik (ν i₀) h := by rw [pot, if_pos hB]
    rw [if_pos hB, mul_one, e1]
  · have e1 : pot ν w i₀ δ h = δ * xi ν w h := by rw [pot, if_neg hB]
    rw [if_neg hB, mul_zero, e1]
    exact mul_nonneg hδ (xi_nonneg hν hw0 h)

/-- Where the truth's likelihood exceeds `δ ξ`, the KL is at most `ln(1/(w_μ δ))`. -/
lemma kl_le_of_good (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hπd : ∀ i, IsPolicy (πd i)) (i₀ : ℕ) (hi₀ : 0 < w i₀) {δ : ℝ} (hδ : 0 < δ) (s : Hist A E)
    (hgood : δ * xi ν w s < lik (ν i₀) s) :
    0 < lik (ν i₀) s ∧
      klAct (πd i₀ s) (thompson ν w πd s) ≤ log (1 / (w i₀ * δ)) := by
  have hL : 0 < lik (ν i₀) s :=
    lt_of_le_of_lt (mul_nonneg hδ.le (xi_nonneg hν hw0 s)) hgood
  have hξpos : 0 < xi ν w s := lt_of_lt_of_le (mul_pos hi₀ hL) (le_xi hν hw0 hws i₀ s)
  refine ⟨hL, (kl_le hν hw0 hws hπd i₀ hi₀ s hL).trans
    (Real.log_le_log (div_pos hξpos (mul_pos hi₀ hL)) ?_)⟩
  rw [div_le_div_iff₀ (mul_pos hi₀ hL) (mul_pos hi₀ hδ)]
  nlinarith [mul_le_mul_of_nonneg_left hgood.le hi₀.le]

open Classical in
/-- [UNAPPROVED STATEMENT] **Theorem 5, uniform-in-time clause (finite horizon).**
Hypotheses as in `thompson_per_step`, `δ > 0`. For every horizon `n`, with `P^π_μ`-probability
at least `1 - δ`, at EVERY time `t ≤ n` the history so far has positive probability under the
truth and `KL(π_μ ‖ π_T)(h_{<t}) ≤ ln(1 / (w_μ δ))`. Stated as: the probability that some
time-prefix fails this is at most `δ`. -/
theorem thompson_uniform (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hw1 : ∑' i, w i ≤ 1) (hπd : ∀ i, IsPolicy (πd i)) (i₀ : ℕ) (hi₀ : 0 < w i₀)
    (hμ : ∀ h a, ∑ e, ν i₀ h a e = 1) (π : Policy A E) (hπ : IsPolicy π) {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) :
    Ex π (ν i₀) n
      (fun h => if ∃ s, s <:+ h ∧ ¬ (0 < lik (ν i₀) s ∧
        klAct (πd i₀ s) (thompson ν w πd s) ≤ log (1 / (w i₀ * δ))) then 1 else 0) ≤ δ := by
  refine (Ex_mono hπ (hν i₀) n fun h => ?_).trans
    (posterior_uniform hν hw0 hws hw1 i₀ hμ π hπ hδ.le n)
  by_cases h1 : ∃ s, s <:+ h ∧ ¬ (0 < lik (ν i₀) s ∧
      klAct (πd i₀ s) (thompson ν w πd s) ≤ log (1 / (w i₀ * δ)))
  · have h2 : ∃ s, s <:+ h ∧ lik (ν i₀) s ≤ δ * xi ν w s := by
      obtain ⟨s, hs, hnot⟩ := h1
      refine ⟨s, hs, ?_⟩
      by_contra hgood
      exact hnot (kl_le_of_good hν hw0 hws hπd i₀ hi₀ hδ s (not_le.1 hgood))
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h1]
    split_ifs <;> norm_num

end Uniform

/-- For a deterministic designated policy the KL is the log loss on its action. -/
lemma klAct_pointmass [DecidableEq A] (p q : A → ℝ) (a₀ : A)
    (hp : ∀ a, p a = if a = a₀ then 1 else 0) : klAct p q = -log (q a₀) := by
  unfold klAct
  rw [Finset.sum_eq_single a₀]
  · simp [hp, Real.log_inv]
  · intro b _ hb; simp [hp, hb]
  · intro h; exact absurd (Finset.mem_univ a₀) h

/-- [UNAPPROVED STATEMENT] **Theorem 5, deterministic form.** If the truth's designated policy
is deterministic, playing `astar h` at history `h`, then for ANY behaviour policy `π` and every
`t`: `E^π_μ [ -ln π_T(a*_t | h_{<t}) ] ≤ ln(1 / w_μ)`. Other hypotheses as in
`thompson_per_step`. -/
theorem thompson_per_step_det [DecidableEq A] {ν : ℕ → Env A E} {w : ℕ → ℝ}
    {πd : ℕ → Policy A E} (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hw1 : ∑' i, w i ≤ 1) (hπd : ∀ i, IsPolicy (πd i)) (i₀ : ℕ) (hi₀ : 0 < w i₀)
    (hμ : ∀ h a, ∑ e, ν i₀ h a e = 1) (astar : Hist A E → A)
    (hdet : ∀ h a, πd i₀ h a = if a = astar h then 1 else 0)
    (π : Policy A E) (hπ : IsPolicy π) (t : ℕ) :
    Ex π (ν i₀) t (fun h => -log (thompson ν w πd h (astar h))) ≤ log (1 / w i₀) := by
  have h := thompson_per_step hν hw0 hws hw1 hπd i₀ hi₀ hμ π hπ t
  have e : (fun h => klAct (πd i₀ h) (thompson ν w πd h)) =
      (fun h => -log (thompson ν w πd h (astar h))) :=
    funext fun h => klAct_pointmass _ _ (astar h) (hdet h)
  rw [e] at h
  exact h

/-- [UNAPPROVED STATEMENT] Sanity check on `Ex`: at horizon one it is the sum over the first
action and percept. -/
theorem Ex_step_one (π : Policy A E) (μ : Env A E) (f : Hist A E → ℝ) :
    Ex π μ 1 f = ∑ a, ∑ e, π [] a * μ [] a e * f [(a, e)] := by
  show Ex π μ (0 + 1) f = _
  simp only [Ex]

/-- [UNAPPROVED STATEMENT] **The per-step bound is attained at every step, so it cannot be
summed.** Take a class whose members all have the SAME environment `μ` but different designated
policies: member `0` plays `astar h` for certain, every other member never plays it. No percept
ever separates the members, the posterior never moves, and for every behaviour policy and every
`t` the expected log loss on the optimal action is EXACTLY `ln(1 / w 0)`. So under the hypotheses
of `thompson_per_step` the sum over `t ≤ n` can be `n · ln(1 / w_μ)`.

(This is the limiting case `D = ∞` of the note's delay example, where the two environments
differ but are indistinguishable for the first `D` steps.) -/
theorem thompson_per_step_tight {μ : Env A E} (hμ : ∀ h a, ∑ e, μ h a e = 1) {w : ℕ → ℝ}
    (hw1 : ∑' i, w i = 1) {πd : ℕ → Policy A E} (astar : Hist A E → A)
    (hstar : ∀ h, πd 0 h (astar h) = 1) (hothers : ∀ i, i ≠ 0 → ∀ h, πd i h (astar h) = 0)
    (π : Policy A E) (hπ : IsPolicy π) (t : ℕ) :
    Ex π μ t (fun h => -log (thompson (fun _ => μ) w πd h (astar h))) = log (1 / w 0) := by
  have hx : ∀ h, xi (fun _ => μ) w h = lik μ h := by
    intro h
    unfold xi
    rw [tsum_mul_right, hw1, one_mul]
  have hnum : ∀ h, ∑' i, w i * lik μ h * πd i h (astar h) = w 0 * lik μ h := by
    intro h
    rw [tsum_eq_single 0 (fun i hi => by rw [hothers i hi, mul_zero]), hstar, mul_one]
  have hT : ∀ h, lik μ h ≠ 0 → thompson (fun _ => μ) w πd h (astar h) = w 0 := by
    intro h hL
    have e : thompson (fun _ => μ) w πd h (astar h) =
        (∑' i, w i * lik μ h * πd i h (astar h)) / xi (fun _ => μ) w h := rfl
    rw [e, hnum, hx, mul_div_assoc, div_self hL, mul_one]
  rw [Ex_eq_S0]
  have hfun : (fun h => lik μ h * -log (thompson (fun _ => μ) w πd h (astar h))) =
      (fun h => lik μ h * log (1 / w 0)) := by
    funext h
    by_cases hL : lik μ h = 0
    · rw [hL, zero_mul, zero_mul]
    · rw [hT h hL, one_div, Real.log_inv]
  rw [hfun, S0_harm hπ (F := fun h => lik μ h * log (1 / w 0)) (fun h a => by
    simp only [lik]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hμ, mul_one]) t]
  simp [lik]

end HsiLean.ThompsonLogLoss

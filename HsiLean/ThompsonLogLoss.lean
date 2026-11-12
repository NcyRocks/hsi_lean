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

end HsiLean.ThompsonLogLoss

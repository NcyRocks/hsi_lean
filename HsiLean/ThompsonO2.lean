-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-12 and has NOT been reviewed by Nathan.
import HsiLean.ThompsonLogLoss
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# O2: Thompson sampling's log loss on the optimal action under a uniform gap

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-12. Not reviewed by Nathan.

Source: `PIBBSS/notes/queue/rl-logloss-vs-solind-2026-11-11.md`, OPEN item (O2). The argument on
paper is `paper-drafts/UNAPPROVED_thompson_O2.md`.

## The model added to `ThompsonLogLoss.lean` (every definition is a design decision)

* `IsDisc r γ`: a reward `r : E → [0,1]` read off the percept, and a discount `γ ∈ [0,1)`.
* Values are normalised, geometrically discounted, and defined by value iteration:
  `Vn ν n h` is the optimal `n`-step value, `Vstar ν h = ⨆ n, Vn ν n h`, and
  `Qstar ν h a = Σ_e ν(e|ha) [(1-γ) r(e) + γ Vstar ν (hae)]`. Value iteration is a structural
  recursion and needs no measure on infinite histories; for measures it is the usual
  `sup_π V^π` (standard, not proved here).
* `IsOptAct ν h a`: `a` maximises `Qstar ν h ·`.
* `IsDet ν`: every percept probability is `0` or `1`.
* `detPol p`: the deterministic policy playing `p h` at `h`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.header false

open Real Finset
open HsiLean.ThompsonLogLoss

namespace HsiLean.ThompsonO2

variable {A E : Type*} [Fintype A] [Fintype E]

/-- [UNAPPROVED STATEMENT] A reward function with values in `[0,1]` and a discount factor in
`[0,1)`. -/
structure IsDisc (r : E → ℝ) (γ : ℝ) : Prop where
  r_nonneg : ∀ e, 0 ≤ r e
  r_le : ∀ e, r e ≤ 1
  γ_nonneg : 0 ≤ γ
  γ_lt : γ < 1

/-- The Bellman backup of a value function `V`: `Σ_e ν(e|ha) [(1-γ) r(e) + γ V(hae)]`. -/
noncomputable def qval (r : E → ℝ) (γ : ℝ) (ν : Env A E) (V : Hist A E → ℝ) (h : Hist A E)
    (a : A) : ℝ :=
  ∑ e, ν h a e * ((1 - γ) * r e + γ * V ((a, e) :: h))

/-- [UNAPPROVED STATEMENT] The optimal `n`-step value (normalised, discounted), by value
iteration. -/
noncomputable def Vn [Nonempty A] (r : E → ℝ) (γ : ℝ) (ν : Env A E) : ℕ → Hist A E → ℝ
  | 0, _ => 0
  | n + 1, h => Finset.univ.sup' Finset.univ_nonempty (qval r γ ν (Vn r γ ν n) h)

/-- [UNAPPROVED STATEMENT] The optimal value `V*_ν(h)`: the limit (supremum) of value
iteration. -/
noncomputable def Vstar [Nonempty A] (r : E → ℝ) (γ : ℝ) (ν : Env A E) (h : Hist A E) : ℝ :=
  ⨆ n, Vn r γ ν n h

/-- [UNAPPROVED STATEMENT] The optimal action value
`Q*_ν(h,a) = Σ_e ν(e|ha) [(1-γ) r(e) + γ V*_ν(hae)]`. -/
noncomputable def Qstar [Nonempty A] (r : E → ℝ) (γ : ℝ) (ν : Env A E) (h : Hist A E) (a : A) :
    ℝ :=
  qval r γ ν (Vstar r γ ν) h a

/-- [UNAPPROVED STATEMENT] `a` is an optimal action for `ν` at `h`. -/
def IsOptAct [Nonempty A] (r : E → ℝ) (γ : ℝ) (ν : Env A E) (h : Hist A E) (a : A) : Prop :=
  ∀ b, Qstar r γ ν h b ≤ Qstar r γ ν h a

/-- [UNAPPROVED STATEMENT] A deterministic (semi)environment: every percept probability is `0`
or `1`. -/
def IsDet (ν : Env A E) : Prop := ∀ h a e, ν h a e = 0 ∨ ν h a e = 1

/-- [UNAPPROVED STATEMENT] The deterministic policy that plays `p h` at history `h`. -/
def detPol [DecidableEq A] (p : Hist A E → A) : Policy A E := fun h a => if a = p h then 1 else 0

/-! ### Values: bounds and monotonicity -/

section Values

variable {r : E → ℝ} {γ : ℝ} {ν : Env A E}

lemma qval_mono (hd : IsDisc r γ) (hν : IsSemiEnv ν) {V V' : Hist A E → ℝ}
    (hV : ∀ h, V h ≤ V' h) (h : Hist A E) (a : A) : qval r γ ν V h a ≤ qval r γ ν V' h a :=
  Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left
    (by have := mul_le_mul_of_nonneg_left (hV ((a, e) :: h)) hd.γ_nonneg; linarith)
    (hν.nonneg h a e)

lemma qval_bounds (hd : IsDisc r γ) (hν : IsSemiEnv ν) {V : Hist A E → ℝ}
    (hV : ∀ h, 0 ≤ V h ∧ V h ≤ 1) (h : Hist A E) (a : A) :
    0 ≤ qval r γ ν V h a ∧ qval r γ ν V h a ≤ 1 := by
  have hb : ∀ e, 0 ≤ (1 - γ) * r e + γ * V ((a, e) :: h) ∧
      (1 - γ) * r e + γ * V ((a, e) :: h) ≤ 1 := by
    intro e
    obtain ⟨h0, h1⟩ := hV ((a, e) :: h)
    have h2 : 0 ≤ 1 - γ := sub_nonneg.2 hd.γ_lt.le
    constructor
    · exact add_nonneg (mul_nonneg h2 (hd.r_nonneg e)) (mul_nonneg hd.γ_nonneg h0)
    · nlinarith [mul_nonneg h2 (sub_nonneg.2 (hd.r_le e)),
        mul_nonneg hd.γ_nonneg (sub_nonneg.2 h1)]
  constructor
  · exact Finset.sum_nonneg fun e _ => mul_nonneg (hν.nonneg h a e) (hb e).1
  · calc qval r γ ν V h a ≤ ∑ e, ν h a e * 1 :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hb e).2 (hν.nonneg h a e)
      _ ≤ 1 := by simpa using hν.sum_le h a

/-- In a semi-environment, a percept of probability one leaves no mass for the others. -/
lemma eq_zero_of_ne (hν : IsSemiEnv ν) {h : Hist A E} {a : A} {e₀ : E} (h1 : ν h a e₀ = 1)
    {e : E} (he : e ≠ e₀) : ν h a e = 0 := by
  classical
  have hsum := hν.sum_le h a
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₀), h1] at hsum
  have hle : ν h a e ≤ ∑ x ∈ Finset.univ.erase e₀, ν h a x :=
    Finset.single_le_sum (f := fun x => ν h a x) (fun x _ => hν.nonneg h a x)
      (Finset.mem_erase.2 ⟨he, Finset.mem_univ e⟩)
  exact le_antisymm (by linarith) (hν.nonneg h a e)

/-- A sum against a deterministic percept distribution is evaluation at the percept. -/
lemma sum_det (hν : IsSemiEnv ν) {h : Hist A E} {a : A} {e₀ : E} (h1 : ν h a e₀ = 1)
    (f : E → ℝ) : ∑ e, ν h a e * f e = f e₀ := by
  rw [Finset.sum_eq_single e₀ (fun e _ he => by rw [eq_zero_of_ne hν h1 he, zero_mul])
    (fun hn => absurd (Finset.mem_univ e₀) hn), h1, one_mul]

lemma qval_det (hν : IsSemiEnv ν) {h : Hist A E} {a : A} {e₀ : E} (h1 : ν h a e₀ = 1)
    (V : Hist A E → ℝ) : qval r γ ν V h a = (1 - γ) * r e₀ + γ * V ((a, e₀) :: h) :=
  sum_det hν h1 _

variable [Nonempty A]

lemma Vn_bounds (hd : IsDisc r γ) (hν : IsSemiEnv ν) (n : ℕ) (h : Hist A E) :
    0 ≤ Vn r γ ν n h ∧ Vn r γ ν n h ≤ 1 := by
  induction n generalizing h with
  | zero => simp [Vn]
  | succ n ih =>
    simp only [Vn]
    constructor
    · exact (qval_bounds hd hν ih h (Classical.arbitrary A)).1.trans
        (Finset.le_sup' (qval r γ ν (Vn r γ ν n) h) (Finset.mem_univ _))
    · exact Finset.sup'_le _ _ fun a _ => (qval_bounds hd hν ih h a).2

lemma Vn_le_Vstar (hd : IsDisc r γ) (hν : IsSemiEnv ν) (n : ℕ) (h : Hist A E) :
    Vn r γ ν n h ≤ Vstar r γ ν h :=
  le_ciSup (f := fun n => Vn r γ ν n h)
    ⟨1, by rintro _ ⟨m, rfl⟩; exact (Vn_bounds hd hν m h).2⟩ n

lemma Vstar_bounds (hd : IsDisc r γ) (hν : IsSemiEnv ν) (h : Hist A E) :
    0 ≤ Vstar r γ ν h ∧ Vstar r γ ν h ≤ 1 :=
  ⟨(Vn_bounds hd hν 0 h).1.trans (Vn_le_Vstar hd hν 0 h),
    ciSup_le fun n => (Vn_bounds hd hν n h).2⟩

lemma Qstar_bounds (hd : IsDisc r γ) (hν : IsSemiEnv ν) (h : Hist A E) (a : A) :
    0 ≤ Qstar r γ ν h a ∧ Qstar r γ ν h a ≤ 1 :=
  qval_bounds hd hν (Vstar_bounds hd hν) h a

/-- Half of the Bellman optimality equation: `V* ≤ max_a Q*`, in the form used below. -/
lemma Vstar_le_Qstar_of_opt (hd : IsDisc r γ) (hν : IsSemiEnv ν) {h : Hist A E} {a : A}
    (ha : IsOptAct r γ ν h a) : Vstar r γ ν h ≤ Qstar r γ ν h a := by
  refine ciSup_le fun n => ?_
  cases n with
  | zero => simpa [Vn] using (Qstar_bounds hd hν h a).1
  | succ n =>
    simp only [Vn]
    exact Finset.sup'_le _ _ fun b _ =>
      (qval_mono hd hν (Vn_le_Vstar hd hν n) h b).trans (ha b)

end Values

/-! ### Values along a deterministic path (Lemma 1 of the draft)

`out h a` is the truth's percept after `h` and `a`. `stepP out p h` is one step of policy `p`;
`G n h` is the truncated `n`-step return of `p` from `h` in the truth; `Agree ν out p n h` says
that `ν` gives probability one to the truth's percept at each of those `n` steps. -/

/-- One step of the deterministic policy `p` against the percept function `out`. -/
def stepP (out : Hist A E → A → E) (p : Hist A E → A) (h : Hist A E) : Hist A E :=
  (p h, out h (p h)) :: h

/-- The truncated `n`-step return of `p` from `h`. -/
noncomputable def G (r : E → ℝ) (γ : ℝ) (out : Hist A E → A → E) (p : Hist A E → A) :
    ℕ → Hist A E → ℝ
  | 0, _ => 0
  | n + 1, h => (1 - γ) * r (out h (p h)) + γ * G r γ out p n (stepP out p h)

/-- `ν` predicts the percepts `out` with certainty along the first `n` steps of `p` from `h`. -/
def Agree (ν : Env A E) (out : Hist A E → A → E) (p : Hist A E → A) : ℕ → Hist A E → Prop
  | 0, _ => True
  | n + 1, h => ν h (p h) (out h (p h)) = 1 ∧ Agree ν out p n (stepP out p h)

section Path

variable [Nonempty A] {r : E → ℝ} {γ : ℝ} {ν : Env A E} {out : Hist A E → A → E}
  {p : Hist A E → A}

lemma G_le_Vn (hd : IsDisc r γ) (hν : IsSemiEnv ν) (n : ℕ) (h : Hist A E)
    (hA : Agree ν out p n h) : G r γ out p n h ≤ Vn r γ ν n h := by
  induction n generalizing h with
  | zero => simp [G, Vn]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := hA
    simp only [G, Vn]
    calc (1 - γ) * r (out h (p h)) + γ * G r γ out p n (stepP out p h)
        ≤ (1 - γ) * r (out h (p h)) + γ * Vn r γ ν n (stepP out p h) := by
          have := mul_le_mul_of_nonneg_left (ih _ h2) hd.γ_nonneg; linarith
      _ = qval r γ ν (Vn r γ ν n) h (p h) := (qval_det hν h1 _).symm
      _ ≤ _ := Finset.le_sup' (qval r γ ν (Vn r γ ν n) h) (Finset.mem_univ _)

/-- Lemma 1, lower half: following `p` for `n` steps is worth at most `Q*`. -/
lemma G_le_Qstar (hd : IsDisc r γ) (hν : IsSemiEnv ν) (n : ℕ) (h : Hist A E)
    (hA : Agree ν out p n h) : G r γ out p n h ≤ Qstar r γ ν h (p h) := by
  cases n with
  | zero => simpa [G] using (Qstar_bounds hd hν h (p h)).1
  | succ n =>
    obtain ⟨h1, h2⟩ := hA
    simp only [G]
    rw [Qstar, qval_det hν h1]
    have := mul_le_mul_of_nonneg_left
      ((G_le_Vn hd hν n _ h2).trans (Vn_le_Vstar hd hν n _)) hd.γ_nonneg
    simp only [stepP] at this ⊢
    linarith

/-- Lemma 1, upper half: if `p` is optimal for `ν` everywhere, `Q*` is at most the `n`-step
return of `p` plus `γ^n`. -/
lemma Qstar_le_G (hd : IsDisc r γ) (hν : IsSemiEnv ν) (hopt : ∀ h, IsOptAct r γ ν h (p h))
    (n : ℕ) (h : Hist A E) (hA : Agree ν out p n h) :
    Qstar r γ ν h (p h) ≤ G r γ out p n h + γ ^ n := by
  induction n generalizing h with
  | zero => simpa [G] using (Qstar_bounds hd hν h (p h)).2
  | succ n ih =>
    obtain ⟨h1, h2⟩ := hA
    simp only [G]
    rw [Qstar, qval_det hν h1]
    have h3 := (Vstar_le_Qstar_of_opt hd hν (hopt (stepP out p h))).trans (ih _ h2)
    have := mul_le_mul_of_nonneg_left h3 hd.γ_nonneg
    simp only [stepP] at this ⊢
    rw [pow_succ]
    linarith

lemma Agree_self {μ : Env A E} (hout : ∀ h a, μ h a (out h a) = 1) (n : ℕ) (h : Hist A E) :
    Agree μ out p n h := by
  induction n generalizing h with
  | zero => trivial
  | succ n ih => exact ⟨hout _ _, ih _⟩

/-- [UNAPPROVED STATEMENT] **Lemma 2 of the draft: a rival that disagrees about the optimal
action is refuted on one of two `H`-step paths.** `μ` is a deterministic environment with percept
function `out`; `pμ` and `pν` are everywhere-optimal deterministic policies for `μ` and for a
semi-environment `ν`; at `h` the action `pν h` is worse than `pμ h` in `μ` by at least `Δ`, and
`2 γ^H < Δ`. Then `ν` cannot predict `μ`'s percepts with certainty along both the `H` steps of
`pν` from `h` and the `H` steps of `pμ` from `h`. -/
theorem disagree_refuted (hd : IsDisc r γ) {μ : Env A E} (hμ : IsSemiEnv μ) (hν : IsSemiEnv ν)
    (hout : ∀ h a, μ h a (out h a) = 1) {pμ pν : Hist A E → A}
    (hoμ : ∀ h, IsOptAct r γ μ h (pμ h)) (hoν : ∀ h, IsOptAct r γ ν h (pν h)) {Δ : ℝ} {H : ℕ}
    (hH : 2 * γ ^ H < Δ) (h : Hist A E)
    (hgap : Qstar r γ μ h (pν h) + Δ ≤ Qstar r γ μ h (pμ h)) :
    ¬ (Agree ν out pν H h ∧ Agree ν out pμ H h) := by
  rintro ⟨h1, h2⟩
  have a1 := Qstar_le_G hd hν hoν H h h1
  have a2 := G_le_Qstar hd hμ H h (Agree_self (p := pν) hout H h)
  have a3 := Qstar_le_G hd hμ hoμ H h (Agree_self (p := pμ) hout H h)
  have a4 := G_le_Qstar hd hν H h h2
  have a5 := hoν h (pμ h)
  linarith

end Path

/-! ### Conditional expectations and the Markov property of `Ex` -/

section Markov

/-- `ExH π μ n f h`: the expectation of `f` at the history `n` steps after `h`, when `π` acts in
`μ` from `h` on. -/
noncomputable def ExH (π : Policy A E) (μ : Env A E) : ℕ → (Hist A E → ℝ) → Hist A E → ℝ
  | 0, f, h => f h
  | n + 1, f, h => ∑ a, ∑ e, π h a * μ h a e * ExH π μ n f ((a, e) :: h)

lemma ExH_comm (π : Policy A E) (μ : Env A E) (f : Hist A E → ℝ) (n : ℕ) (h : Hist A E) :
    ExH π μ n (ExH π μ 1 f) h = ExH π μ (n + 1) f h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change (∑ a, ∑ e, π h a * μ h a e * ExH π μ n (ExH π μ 1 f) ((a, e) :: h)) =
      ∑ a, ∑ e, π h a * μ h a e * ExH π μ (n + 1) f ((a, e) :: h)
    simp_rw [ih]

/-- [UNAPPROVED STATEMENT] The Markov property (tower rule) for `Ex`: the expectation at time
`t + n` is the expectation at time `t` of the `n`-step conditional expectation. -/
theorem Ex_markov (π : Policy A E) (μ : Env A E) (t n : ℕ) (f : Hist A E → ℝ) :
    Ex π μ (t + n) f = Ex π μ t (ExH π μ n f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change Ex π μ (t + n) (fun h => ∑ a, ∑ e, π h a * μ h a e * f ((a, e) :: h)) = _
    rw [ih]
    congr 1
    funext h
    exact ExH_comm π μ f n h

variable {π : Policy A E} {μ : Env A E}

lemma Ex_mono' (hπ : IsPolicy π) (hμ : IsSemiEnv μ) (t : ℕ) {f g : Hist A E → ℝ}
    (hfg : ∀ h, lik μ h ≠ 0 → f h ≤ g h) : Ex π μ t f ≤ Ex π μ t g := by
  rw [Ex_eq_S0, Ex_eq_S0]
  refine S0_mono hπ t fun x => ?_
  by_cases hx : lik μ x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (hfg x hx) (lik_nonneg hμ x)

lemma Ex_lin (π : Policy A E) (μ : Env A E) (c : ℝ) (t : ℕ) (f g : Hist A E → ℝ) :
    Ex π μ t (fun h => c * f h + g h) = c * Ex π μ t f + Ex π μ t g := by
  rw [Ex_eq_S0, Ex_eq_S0, Ex_eq_S0, ← S0_lin]
  congr 1
  funext h
  ring

lemma Ex_const (hπ : IsPolicy π) (hμ : ∀ h a, ∑ e, μ h a e = 1) (t : ℕ) (c : ℝ) :
    Ex π μ t (fun _ => c) = c := by
  rw [Ex_eq_S0, S0_harm hπ (F := fun h => lik μ h * c) (fun h a => by
    simp only [lik]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hμ, mul_one]) t]
  simp [lik]

lemma S0_congr_policy {π' : Policy A E} (hππ : ∀ h, lik μ h ≠ 0 → ∀ a, π h a = π' h a) (t : ℕ)
    (F : Hist A E → ℝ) (hF : ∀ h, lik μ h = 0 → F h = 0) : S0 π t F = S0 π' t F := by
  induction t generalizing F with
  | zero => rfl
  | succ t ih =>
    simp only [S0]
    have hz : ∀ (ρ : Policy A E) h, lik μ h = 0 → (∑ a, ρ h a * ∑ e, F ((a, e) :: h)) = 0 := by
      intro ρ h hh
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [Finset.sum_eq_zero fun e _ => hF _ (by simp [lik, hh]), mul_zero]
    have e : (fun h => ∑ a, π h a * ∑ e, F ((a, e) :: h)) =
        fun h => ∑ a, π' h a * ∑ e, F ((a, e) :: h) := by
      funext h
      by_cases hh : lik μ h = 0
      · rw [hz π h hh, hz π' h hh]
      · exact Finset.sum_congr rfl fun a _ => by rw [hππ h hh a]
    rw [ih _ (hz π), e]

/-- The on-policy expectation only depends on the policy at histories the truth can produce. -/
lemma Ex_congr_policy {π' : Policy A E} (hππ : ∀ h, lik μ h ≠ 0 → ∀ a, π h a = π' h a) (t : ℕ)
    (f : Hist A E → ℝ) : Ex π μ t f = Ex π' μ t f := by
  rw [Ex_eq_S0, Ex_eq_S0]
  exact S0_congr_policy hππ t _ fun h hh => by simp [hh]

variable {out : Hist A E → A → E}

lemma ExH_succ_det (hμ : IsSemiEnv μ) (hout : ∀ h a, μ h a (out h a) = 1) (n : ℕ)
    (f : Hist A E → ℝ) (h : Hist A E) :
    ExH π μ (n + 1) f h = ∑ a, π h a * ExH π μ n f ((a, out h a) :: h) := by
  simp only [ExH]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sum_det hμ (hout h a) (fun e => π h a * ExH π μ n f ((a, e) :: h))]
  exact Finset.sum_congr rfl fun e _ => by ring

lemma ExH_super (hπ : IsPolicy π) (hμ : IsSemiEnv μ) (hout : ∀ h a, μ h a (out h a) = 1)
    {g : Hist A E → ℝ} (hg : ∀ h a e, g ((a, e) :: h) ≤ g h) (n : ℕ) (h : Hist A E) :
    ExH π μ n g h ≤ g h := by
  induction n generalizing h with
  | zero => exact le_rfl
  | succ n ih =>
    rw [ExH_succ_det hμ hout]
    calc ∑ a, π h a * ExH π μ n g ((a, out h a) :: h) ≤ ∑ a, π h a * g h :=
          Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left ((ih _).trans (hg h a _)) (hπ.nonneg h a)
      _ = g h := by rw [← Finset.sum_mul, hπ.sum_eq, one_mul]

end Markov

/-! ### Counting the unrefuted members of a finite set -/

section Alive

open Classical in
/-- The members of `F` not refuted by `h`. -/
noncomputable def alive (ν : ℕ → Env A E) (F : Finset ℕ) (h : Hist A E) : Finset ℕ :=
  F.filter fun i => lik (ν i) h ≠ 0

/-- The number of members of `F` not refuted by `h`. -/
noncomputable def Nal (ν : ℕ → Env A E) (F : Finset ℕ) (h : Hist A E) : ℝ :=
  ((alive ν F h).card : ℝ)

variable {ν : ℕ → Env A E} {F : Finset ℕ}

omit [Fintype A] [Fintype E] in
lemma alive_cons_subset (h : Hist A E) (a : A) (e : E) :
    alive ν F ((a, e) :: h) ⊆ alive ν F h := by
  intro i hi
  simp only [alive, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, fun h0 => hi.2 (by simp [lik, h0])⟩

omit [Fintype A] [Fintype E] in
lemma Nal_cons_le (h : Hist A E) (a : A) (e : E) : Nal ν F ((a, e) :: h) ≤ Nal ν F h := by
  unfold Nal
  exact_mod_cast Finset.card_le_card (alive_cons_subset h a e)

omit [Fintype A] [Fintype E] in
lemma Nal_drop {i : ℕ} (hi : i ∈ F) {h : Hist A E} {a : A} {e : E} (hal : lik (ν i) h ≠ 0)
    (hdead : lik (ν i) ((a, e) :: h) = 0) : Nal ν F ((a, e) :: h) ≤ Nal ν F h - 1 := by
  have hlt : (alive ν F ((a, e) :: h)).card < (alive ν F h).card := by
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset (alive_cons_subset h a e)).2
      ⟨i, ?_, ?_⟩)
    · simp only [alive, Finset.mem_filter]; exact ⟨hi, hal⟩
    · simp only [alive, Finset.mem_filter]; exact fun hc => hc.2 hdead
  unfold Nal
  have : ((alive ν F ((a, e) :: h)).card : ℝ) + 1 ≤ ((alive ν F h).card : ℝ) := by
    exact_mod_cast hlt
  linarith

omit [Fintype A] [Fintype E] in
lemma Nal_bounds (h : Hist A E) : 0 ≤ Nal ν F h ∧ Nal ν F h ≤ F.card := by
  unfold Nal
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast Finset.card_filter_le _ _⟩

/-- The drop lemma: from a history where member `i` is unrefuted and is refuted somewhere along
the first `n` steps of `p`, and where the behaviour policy plays `p`'s action with probability
at least `q` as long as `i` is unrefuted, the expected number of unrefuted members after `n`
steps is smaller by at least `q^n`. -/
lemma ExH_drop {π : Policy A E} (hπ : IsPolicy π) {μ : Env A E} (hμ : IsSemiEnv μ)
    {out : Hist A E → A → E} (hout : ∀ h a, μ h a (out h a) = 1) {i : ℕ} (hi : i ∈ F)
    (hdi : IsDet (ν i)) {p : Hist A E → A} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp : ∀ h, lik μ h ≠ 0 → lik (ν i) h ≠ 0 → q ≤ π h (p h)) (n : ℕ) (h : Hist A E)
    (hl : lik μ h ≠ 0) (hal : lik (ν i) h ≠ 0) (hA : ¬ Agree (ν i) out p n h) :
    ExH π μ n (Nal ν F) h ≤ Nal ν F h - q ^ n := by
  classical
  induction n generalizing h with
  | zero => exact absurd trivial hA
  | succ n ih =>
    rw [ExH_succ_det hμ hout]
    have hg : ∀ h a e, Nal ν F ((a, e) :: h) ≤ Nal ν F h := Nal_cons_le
    have hqn : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1
    have hqn0 : 0 ≤ q ^ n := pow_nonneg hq0 n
    have hmain : ExH π μ n (Nal ν F) ((p h, out h (p h)) :: h) ≤ Nal ν F h - q ^ n := by
      by_cases h1 : ν i h (p h) (out h (p h)) = 1
      · have hA' : ¬ Agree (ν i) out p n ((p h, out h (p h)) :: h) := fun c => hA ⟨h1, c⟩
        have hl' : lik μ ((p h, out h (p h)) :: h) ≠ 0 := by simp [lik, hout, hl]
        have hal' : lik (ν i) ((p h, out h (p h)) :: h) ≠ 0 := by simp [lik, h1, hal]
        have h2 := ih _ hl' hal' hA'
        have h3 := hg h (p h) (out h (p h))
        linarith
      · have h0 : ν i h (p h) (out h (p h)) = 0 := (hdi h _ _).resolve_right h1
        have hdead : lik (ν i) ((p h, out h (p h)) :: h) = 0 := by simp [lik, h0]
        have h2 := ExH_super hπ hμ hout hg n ((p h, out h (p h)) :: h)
        have h3 := Nal_drop hi hal hdead
        linarith
    have hothers : ∀ a, ExH π μ n (Nal ν F) ((a, out h a) :: h) ≤ Nal ν F h := fun a =>
      (ExH_super hπ hμ hout hg n _).trans (hg h a _)
    have hP := hp h hl hal
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun a => π h a * ExH π μ n (Nal ν F) ((a, out h a) :: h)) (Finset.mem_univ (p h))
    have hsplitπ := Finset.add_sum_erase Finset.univ (fun a => π h a) (Finset.mem_univ (p h))
    beta_reduce at hsplit hsplitπ
    rw [hπ.sum_eq] at hsplitπ
    have hrest : ∑ a ∈ Finset.univ.erase (p h),
        π h a * ExH π μ n (Nal ν F) ((a, out h a) :: h) ≤ (1 - π h (p h)) * Nal ν F h := by
      have hR : 1 - π h (p h) = ∑ a ∈ Finset.univ.erase (p h), π h a := by linarith
      rw [hR, Finset.sum_mul]
      exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hothers a) (hπ.nonneg h a)
    have e1 := mul_le_mul_of_nonneg_left hmain (hπ.nonneg h (p h))
    have e2 : q * q ^ n ≤ π h (p h) * q ^ n := mul_le_mul_of_nonneg_right hP hqn0
    rw [← hsplit, pow_succ]
    linarith

end Alive

/-! ### Thompson sampling in a deterministic class -/

section Thompson

variable [DecidableEq A] {ν : ℕ → Env A E} {w : ℕ → ℝ}

omit [Fintype E] in
lemma detPol_isPolicy (p : Hist A E → A) : IsPolicy (detPol p) where
  nonneg h a := by unfold detPol; split_ifs <;> norm_num
  sum_eq h := by simp [detPol]

omit [Fintype A] [Fintype E] [DecidableEq A] in
lemma lik_det {ρ : Env A E} (hρ : IsDet ρ) (h : Hist A E) : lik ρ h = 0 ∨ lik ρ h = 1 := by
  induction h with
  | nil => right; simp [lik]
  | cons x h ih =>
    obtain ⟨a, e⟩ := x
    rcases ih with ih | ih <;> rcases hρ h a e with h1 | h1 <;> simp [lik, ih, h1]

omit [Fintype A] [Fintype E] [DecidableEq A] in
lemma lik_eq_one {ρ : Env A E} (hρ : IsDet ρ) {h : Hist A E} (h0 : lik ρ h ≠ 0) : lik ρ h = 1 :=
  (lik_det hρ h).resolve_left h0

lemma exists_out {μ : Env A E} (hdet : IsDet μ) (hμ : ∀ h a, ∑ e, μ h a e = 1) :
    ∃ out : Hist A E → A → E, ∀ h a, μ h a (out h a) = 1 := by
  have hex : ∀ h a, ∃ e, μ h a e = 1 := by
    intro h a
    by_contra hc
    simp only [not_exists] at hc
    have h0 : ∑ e, μ h a e = 0 :=
      Finset.sum_eq_zero fun e _ => (hdet h a e).resolve_right (hc e)
    rw [hμ] at h0
    exact one_ne_zero h0
  choose out hout using hex
  exact ⟨out, hout⟩

lemma xi_le_one (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w)
    (hw1 : ∑' i, w i ≤ 1) (h : Hist A E) : xi ν w h ≤ 1 :=
  (Summable.tsum_le_tsum (fun i => mul_le_of_le_one_right (hw0 i) (lik_le_one (hν i) h))
    (summable_lik hν hw0 hws h) hws).trans hw1

lemma thompson_nonneg {πd : ℕ → Policy A E} (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i)
    (hπd : ∀ i, IsPolicy (πd i)) (h : Hist A E) (a : A) : 0 ≤ thompson ν w πd h a :=
  div_nonneg (tsum_nonneg fun i =>
    mul_nonneg (mul_nonneg (hw0 i) (lik_nonneg (hν i) h)) ((hπd i).nonneg h a))
    (xi_nonneg hν hw0 h)

lemma thompson_sum {πd : ℕ → Policy A E} (hν : ∀ i, IsSemiEnv (ν i)) (hw0 : ∀ i, 0 ≤ w i)
    (hws : Summable w) (hπd : ∀ i, IsPolicy (πd i)) (h : Hist A E) (hξ : xi ν w h ≠ 0) :
    ∑ a, thompson ν w πd h a = 1 := by
  unfold thompson
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Summable.tsum_finsetSum (fun a _ => summable_num hν hw0 hws hπd h a)]
  have e : ∀ i, ∑ a, w i * lik (ν i) h * πd i h a = w i * lik (ν i) h := by
    intro i
    rw [← Finset.mul_sum, (hπd i).sum_eq, mul_one]
  simp_rw [e]
  exact mul_inv_cancel₀ hξ

/-- Thompson sampling completed to a policy at every history: at histories of mixture
probability zero (where the posterior is undefined) it plays the fallback `π0`. Such histories
have probability zero under every member of positive weight. -/
noncomputable def thompsonP (ν : ℕ → Env A E) (w : ℕ → ℝ) (πd : ℕ → Policy A E)
    (π0 : Policy A E) : Policy A E :=
  fun h a => if xi ν w h = 0 then π0 h a else thompson ν w πd h a

lemma thompsonP_isPolicy {πd : ℕ → Policy A E} {π0 : Policy A E} (hν : ∀ i, IsSemiEnv (ν i))
    (hw0 : ∀ i, 0 ≤ w i) (hws : Summable w) (hπd : ∀ i, IsPolicy (πd i)) (hπ0 : IsPolicy π0) :
    IsPolicy (thompsonP ν w πd π0) where
  nonneg h a := by
    unfold thompsonP
    split_ifs
    · exact hπ0.nonneg h a
    · exact thompson_nonneg hν hw0 hπd h a
  sum_eq h := by
    by_cases hξ : xi ν w h = 0
    · simp only [thompsonP, if_pos hξ]; exact hπ0.sum_eq h
    · simp only [thompsonP, if_neg hξ]; exact thompson_sum hν hw0 hws hπd h hξ

/-- [UNAPPROVED STATEMENT] Per-step Thompson sampling when member `i`'s designated policy is the
deterministic policy `act i`. -/
noncomputable def piT (ν : ℕ → Env A E) (w : ℕ → ℝ) (act : ℕ → Hist A E → A) : Policy A E :=
  thompson ν w fun i => detPol (act i)

/-- [UNAPPROVED STATEMENT] The log loss of Thompson sampling on the truth's optimal action:
`ℓ(h) = -ln π_T(act i₀ h | h)`. -/
noncomputable def loss (ν : ℕ → Env A E) (w : ℕ → ℝ) (act : ℕ → Hist A E → A) (i₀ : ℕ)
    (h : Hist A E) : ℝ :=
  -log (piT ν w act h (act i₀ h))

open Classical in
/-- [UNAPPROVED STATEMENT] The indicator that some member of `F` not yet refuted by `h`
disagrees with the truth `i₀` about the optimal action at `h`. -/
noncomputable def badI (ν : ℕ → Env A E) (act : ℕ → Hist A E → A) (i₀ : ℕ) (F : Finset ℕ)
    (h : Hist A E) : ℝ :=
  if ∃ i ∈ F, lik (ν i) h ≠ 0 ∧ act i h ≠ act i₀ h then 1 else 0

/-- The prior weight outside `F`. -/
noncomputable def tailW (w : ℕ → ℝ) (F : Finset ℕ) : ℝ := ∑' i, if i ∈ F then 0 else w i

/-- [UNAPPROVED STATEMENT] **The hypotheses of O2 for a deterministic class.** A countable class
`ν i` of deterministic semi-environments with prior weights `w i`; member `i`'s designated policy
is the deterministic policy `act i`, which is optimal for `ν i` at every history; the truth is
`ν i₀`, a measure of positive weight, with a **uniform gap** `Δ`: at every history the truth can
produce, every action other than `act i₀ h` has `Q*` smaller by at least `Δ`. -/
structure DetClass [Nonempty A] (r : E → ℝ) (γ : ℝ) (ν : ℕ → Env A E) (w : ℕ → ℝ)
    (act : ℕ → Hist A E → A) (i₀ : ℕ) (Δ : ℝ) : Prop where
  disc : IsDisc r γ
  semi : ∀ i, IsSemiEnv (ν i)
  det : ∀ i, IsDet (ν i)
  w_nonneg : ∀ i, 0 ≤ w i
  w_summable : Summable w
  w_le : ∑' i, w i ≤ 1
  opt : ∀ i h, IsOptAct r γ (ν i) h (act i h)
  truth_pos : 0 < w i₀
  truth_meas : ∀ h a, ∑ e, ν i₀ h a e = 1
  gap : ∀ h, lik (ν i₀) h ≠ 0 → ∀ a, a ≠ act i₀ h →
    Qstar r γ (ν i₀) h a + Δ ≤ Qstar r γ (ν i₀) h (act i₀ h)

variable [Nonempty A] {r : E → ℝ} {γ : ℝ} {act : ℕ → Hist A E → A} {i₀ : ℕ} {Δ : ℝ}

/-- The policy used in the proofs: Thompson sampling, completed by the truth's policy. -/
noncomputable def piP (ν : ℕ → Env A E) (w : ℕ → ℝ) (act : ℕ → Hist A E → A) (i₀ : ℕ) :
    Policy A E :=
  thompsonP ν w (fun i => detPol (act i)) (detPol (act i₀))

lemma piP_isPolicy (hC : DetClass r γ ν w act i₀ Δ) : IsPolicy (piP ν w act i₀) :=
  thompsonP_isPolicy hC.semi hC.w_nonneg hC.w_summable (fun _ => detPol_isPolicy _)
    (detPol_isPolicy _)

lemma xi_ge_truth (hC : DetClass r γ ν w act i₀ Δ) {h : Hist A E} (hl : lik (ν i₀) h ≠ 0) :
    w i₀ ≤ xi ν w h := by
  have h1 := le_xi hC.semi hC.w_nonneg hC.w_summable i₀ h
  rwa [lik_eq_one (hC.det i₀) hl, mul_one] at h1

lemma piP_eq (hC : DetClass r γ ν w act i₀ Δ) {h : Hist A E} (hl : lik (ν i₀) h ≠ 0) (a : A) :
    piT ν w act h a = piP ν w act i₀ h a := by
  have hξ : xi ν w h ≠ 0 := (lt_of_lt_of_le hC.truth_pos (xi_ge_truth hC hl)).ne'
  simp [piP, thompsonP, piT, hξ]

lemma Ex_piT_eq (hC : DetClass r γ ν w act i₀ Δ) (t : ℕ) (f : Hist A E → ℝ) :
    Ex (piT ν w act) (ν i₀) t f = Ex (piP ν w act i₀) (ν i₀) t f :=
  Ex_congr_policy (fun _ hl a => piP_eq hC hl a) t f

/-- An unrefuted member's action is played with probability at least its prior weight. -/
lemma piT_ge_w (hC : DetClass r γ ν w act i₀ Δ) {h : Hist A E} (hl : lik (ν i₀) h ≠ 0) (k : ℕ)
    (hk : lik (ν k) h ≠ 0) : w k ≤ piT ν w act h (act k h) := by
  have hξ := xi_ge_truth hC hl
  have hξpos : 0 < xi ν w h := lt_of_lt_of_le hC.truth_pos hξ
  have hξ1 := xi_le_one hC.semi hC.w_nonneg hC.w_summable hC.w_le h
  have h1 : w k * lik (ν k) h * detPol (act k) h (act k h) / xi ν w h ≤
      piT ν w act h (act k h) :=
    thompson_ge hC.semi hC.w_nonneg hC.w_summable (fun i => detPol_isPolicy (act i)) k h
      (act k h)
  have h2 : detPol (act k) h (act k h) = 1 := by simp [detPol]
  rw [h2, lik_eq_one (hC.det k) hk, mul_one, mul_one] at h1
  refine le_trans ?_ h1
  rw [le_div_iff₀ hξpos]
  exact mul_le_of_le_one_right (hC.w_nonneg k) hξ1

lemma piT_le_one (hC : DetClass r γ ν w act i₀ Δ) {h : Hist A E} (hl : lik (ν i₀) h ≠ 0)
    (a : A) : piT ν w act h a ≤ 1 := by
  rw [piP_eq hC hl]
  exact policy_le_one (piP_isPolicy hC) h a

/-- [UNAPPROVED STATEMENT] **The counting bound.** In a deterministic class with a uniform gap
(`DetClass`), let `2 γ^H < Δ`, and let `F` be a finite set of members containing the truth, all
of prior weight at least `q > 0`. Then on Thompson sampling's own trajectory in the truth, the
expected number of times (over any horizon `T`) at which some unrefuted member of `F` disagrees
with the truth about the optimal action is at most `H · |F| / q^H`. -/
theorem sum_bad_le (hC : DetClass r γ ν w act i₀ Δ) {H : ℕ} (hH : 2 * γ ^ H < Δ)
    {F : Finset ℕ} (hi₀ : i₀ ∈ F) {q : ℝ} (hq : 0 < q) (hqF : ∀ i ∈ F, q ≤ w i) (T : ℕ) :
    ∑ t ∈ Finset.range T, Ex (piT ν w act) (ν i₀) t (badI ν act i₀ F) ≤
      H * F.card / q ^ H := by
  classical
  obtain ⟨out, hout⟩ := exists_out (hC.det i₀) hC.truth_meas
  have hπ := piP_isPolicy hC
  have hq1 : q ≤ 1 := (hqF i₀ hi₀).trans
    ((hC.w_summable.le_tsum i₀ fun j _ => hC.w_nonneg j).trans hC.w_le)
  have hqH : 0 < q ^ H := pow_pos hq H
  -- the key step: a bad history loses a member within `H` steps with probability `≥ q^H`
  have hK : ∀ h, lik (ν i₀) h ≠ 0 → ExH (piP ν w act i₀) (ν i₀) H (Nal ν F) h ≤
      -(q ^ H) * badI ν act i₀ F h + Nal ν F h := by
    intro h hl
    by_cases hb : ∃ i ∈ F, lik (ν i) h ≠ 0 ∧ act i h ≠ act i₀ h
    · obtain ⟨i, hiF, hal, hne⟩ := hb
      have hbI : badI ν act i₀ F h = 1 := if_pos ⟨i, hiF, hal, hne⟩
      have href := disagree_refuted hC.disc (hC.semi i₀) (hC.semi i) hout (hC.opt i₀)
        (hC.opt i) hH h (hC.gap h hl (act i h) hne)
      have hdrop : ExH (piP ν w act i₀) (ν i₀) H (Nal ν F) h ≤ Nal ν F h - q ^ H := by
        rcases not_and_or.1 href with hA | hA
        · exact ExH_drop hπ (hC.semi i₀) hout hiF (hC.det i) hq.le hq1
            (fun h' hl' hal' => by
              rw [← piP_eq hC hl']
              exact (hqF i hiF).trans (piT_ge_w hC hl' i hal')) H h hl hal hA
        · exact ExH_drop hπ (hC.semi i₀) hout hiF (hC.det i) hq.le hq1
            (fun h' hl' _ => by
              rw [← piP_eq hC hl']
              exact (hqF i₀ hi₀).trans (piT_ge_w hC hl' i₀ hl')) H h hl hal hA
      rw [hbI]
      linarith
    · have hbI : badI ν act i₀ F h = 0 := if_neg hb
      rw [hbI, mul_zero, zero_add]
      exact ExH_super hπ (hC.semi i₀) hout Nal_cons_le H h
  -- in expectation
  have hstep : ∀ t, Ex (piP ν w act i₀) (ν i₀) (t + H) (Nal ν F) ≤
      -(q ^ H) * Ex (piP ν w act i₀) (ν i₀) t (badI ν act i₀ F) +
        Ex (piP ν w act i₀) (ν i₀) t (Nal ν F) := by
    intro t
    rw [Ex_markov, ← Ex_lin]
    exact Ex_mono' hπ (hC.semi i₀) t hK
  have hx0 : ∀ t, 0 ≤ Ex (piP ν w act i₀) (ν i₀) t (Nal ν F) := by
    intro t
    have := Ex_mono' hπ (hC.semi i₀) t (f := fun _ => 0) (g := Nal ν F)
      (fun h _ => (Nal_bounds h).1)
    rwa [Ex_const hπ hC.truth_meas] at this
  have hxC : ∀ t, Ex (piP ν w act i₀) (ν i₀) t (Nal ν F) ≤ F.card := by
    intro t
    have := Ex_mono' hπ (hC.semi i₀) t (f := Nal ν F) (g := fun _ => (F.card : ℝ))
      (fun h _ => (Nal_bounds h).2)
    rwa [Ex_const hπ hC.truth_meas] at this
  -- telescope
  set x : ℕ → ℝ := fun t => Ex (piP ν w act i₀) (ν i₀) t (Nal ν F) with hx
  have e1 := Finset.sum_range_add x T H
  have e2 := Finset.sum_range_add x H T
  rw [add_comm T H] at e1
  have e4 : ∑ t ∈ Finset.range H, x t ≤ H * F.card := by
    calc ∑ t ∈ Finset.range H, x t ≤ ∑ _t ∈ Finset.range H, (F.card : ℝ) :=
          Finset.sum_le_sum fun t _ => hxC t
      _ = H * F.card := by simp
  have e5 : 0 ≤ ∑ t ∈ Finset.range H, x (T + t) := Finset.sum_nonneg fun t _ => hx0 _
  have e6 : q ^ H * ∑ t ∈ Finset.range T, Ex (piP ν w act i₀) (ν i₀) t (badI ν act i₀ F) ≤
      ∑ t ∈ Finset.range T, x t - ∑ t ∈ Finset.range T, x (H + t) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    have := hstep t
    rw [add_comm t H] at this
    simp only [hx]
    linarith
  simp_rw [Ex_piT_eq hC]
  rw [le_div_iff₀ hqH, mul_comm]
  linarith

/-! ### From disagreement to log loss -/

lemma tailW_summable (hC : DetClass r γ ν w act i₀ Δ) (F : Finset ℕ) :
    Summable (fun i => if i ∈ F then 0 else w i) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs <;> simp [hC.w_nonneg i])
    (fun i => by split_ifs <;> simp [hC.w_nonneg i]) hC.w_summable

lemma tailW_nonneg (hC : DetClass r γ ν w act i₀ Δ) (F : Finset ℕ) : 0 ≤ tailW w F :=
  tsum_nonneg fun i => by split_ifs <;> simp [hC.w_nonneg i]

/-- At a history the truth can produce: `0 ≤ ℓ ≤ ln(1/w_μ)` (Theorem 5, pointwise, for a
deterministic class). -/
lemma loss_bounds (hC : DetClass r γ ν w act i₀ Δ) {h : Hist A E} (hl : lik (ν i₀) h ≠ 0) :
    0 ≤ loss ν w act i₀ h ∧ loss ν w act i₀ h ≤ log (1 / w i₀) := by
  have h1 := piT_ge_w hC hl i₀ hl
  have h2 := piT_le_one hC hl (act i₀ h)
  have hpos : 0 < piT ν w act h (act i₀ h) := lt_of_lt_of_le hC.truth_pos h1
  unfold loss
  constructor
  · exact neg_nonneg.2 (Real.log_nonpos hpos.le h2)
  · rw [one_div, Real.log_inv]
    exact neg_le_neg (Real.log_le_log hC.truth_pos h1)

/-- At a history the truth can produce where no unrefuted member of `F` disagrees, the loss is
at most `-ln(1 - (prior weight outside F)/w_μ)`. -/
lemma loss_le_of_not_bad (hC : DetClass r γ ν w act i₀ Δ) {F : Finset ℕ}
    (hε : tailW w F < w i₀) {h : Hist A E} (hl : lik (ν i₀) h ≠ 0)
    (hnb : ¬ ∃ i ∈ F, lik (ν i) h ≠ 0 ∧ act i h ≠ act i₀ h) :
    loss ν w act i₀ h ≤ -log (1 - tailW w F / w i₀) := by
  have hw0 := hC.truth_pos
  have hξ := xi_ge_truth hC hl
  have hξpos : 0 < xi ν w h := lt_of_lt_of_le hw0 hξ
  have hsumT := tailW_summable hC F
  have hε0 := tailW_nonneg hC F
  have hsl := summable_lik hC.semi hC.w_nonneg hC.w_summable h
  have hnum : xi ν w h - tailW w F ≤
      ∑' i, w i * lik (ν i) h * detPol (act i) h (act i₀ h) := by
    unfold xi tailW
    rw [← Summable.tsum_sub hsl hsumT]
    refine Summable.tsum_le_tsum (fun i => ?_) (hsl.sub hsumT)
      (summable_num hC.semi hC.w_nonneg hC.w_summable (fun i => detPol_isPolicy (act i)) h _)
    by_cases hiF : i ∈ F
    · rw [if_pos hiF, sub_zero]
      by_cases hli : lik (ν i) h = 0
      · simp [hli]
      · have hagree : act i h = act i₀ h := by
          by_contra hne
          exact hnb ⟨i, hiF, hli, hne⟩
        simp [detPol, hagree]
    · rw [if_neg hiF]
      have h1 := mul_le_of_le_one_right (hC.w_nonneg i) (lik_le_one (hC.semi i) h)
      have h2 : 0 ≤ w i * lik (ν i) h * detPol (act i) h (act i₀ h) :=
        mul_nonneg (mul_nonneg (hC.w_nonneg i) (lik_nonneg (hC.semi i) h))
          ((detPol_isPolicy (act i)).nonneg _ _)
      linarith
  have hth : 1 - tailW w F / w i₀ ≤ piT ν w act h (act i₀ h) := by
    have h1 : (xi ν w h - tailW w F) / xi ν w h ≤ piT ν w act h (act i₀ h) :=
      div_le_div_of_nonneg_right hnum hξpos.le
    have h2 : tailW w F / xi ν w h ≤ tailW w F / w i₀ :=
      div_le_div_of_nonneg_left hε0 hw0 hξ
    have h3 : (xi ν w h - tailW w F) / xi ν w h = 1 - tailW w F / xi ν w h := by
      field_simp
    linarith
  have hpos : 0 < 1 - tailW w F / w i₀ := by
    rw [sub_pos, div_lt_one hw0]
    exact hε
  unfold loss
  exact neg_le_neg (Real.log_le_log hpos hth)

/-- The expected loss is at most `ln(1/w_μ)` times the probability of disagreement within `F`,
plus the tail term. -/
lemma Ex_loss_le (hC : DetClass r γ ν w act i₀ Δ) {F : Finset ℕ} (hε : tailW w F < w i₀)
    (t : ℕ) :
    Ex (piT ν w act) (ν i₀) t (loss ν w act i₀) ≤
      log (1 / w i₀) * Ex (piT ν w act) (ν i₀) t (badI ν act i₀ F) +
        -log (1 - tailW w F / w i₀) := by
  classical
  have hπ := piP_isPolicy hC
  have hw0 := hC.truth_pos
  have hδ : 0 ≤ -log (1 - tailW w F / w i₀) := by
    have h1 : 0 ≤ tailW w F / w i₀ := div_nonneg (tailW_nonneg hC F) hw0.le
    have h2 : tailW w F / w i₀ < 1 := by rwa [div_lt_one hw0]
    exact neg_nonneg.2 (Real.log_nonpos (by linarith) (by linarith))
  rw [Ex_piT_eq hC, Ex_piT_eq hC]
  have h1 := Ex_mono' hπ (hC.semi i₀) t (f := loss ν w act i₀)
    (g := fun h => log (1 / w i₀) * badI ν act i₀ F h + -log (1 - tailW w F / w i₀))
    (fun h hl => by
      by_cases hb : ∃ i ∈ F, lik (ν i) h ≠ 0 ∧ act i h ≠ act i₀ h
      · have hbI : badI ν act i₀ F h = 1 := if_pos hb
        rw [hbI, mul_one]
        linarith [(loss_bounds hC hl).2]
      · have hbI : badI ν act i₀ F h = 0 := if_neg hb
        rw [hbI, mul_zero, zero_add]
        exact loss_le_of_not_bad hC hε hl hb)
  rw [Ex_lin, Ex_const hπ hC.truth_meas] at h1
  exact h1

lemma Ex_loss_nonneg (hC : DetClass r γ ν w act i₀ Δ) (t : ℕ) :
    0 ≤ Ex (piT ν w act) (ν i₀) t (loss ν w act i₀) := by
  have hπ := piP_isPolicy hC
  rw [Ex_piT_eq hC]
  have := Ex_mono' hπ (hC.semi i₀) t (f := fun _ => 0) (g := loss ν w act i₀)
    (fun h hl => (loss_bounds hC hl).1)
  rwa [Ex_const hπ hC.truth_meas] at this

lemma Ex_badI_nonneg (hC : DetClass r γ ν w act i₀ Δ) (F : Finset ℕ) (t : ℕ) :
    0 ≤ Ex (piT ν w act) (ν i₀) t (badI ν act i₀ F) := by
  classical
  have hπ := piP_isPolicy hC
  rw [Ex_piT_eq hC]
  have := Ex_mono' hπ (hC.semi i₀) t (f := fun _ => 0) (g := badI ν act i₀ F)
    (fun h _ => by unfold badI; split_ifs <;> norm_num)
  rwa [Ex_const hπ hC.truth_meas] at this

/-- [UNAPPROVED STATEMENT] **O2, finite deterministic class: the log loss is summable.**
Hypotheses: `DetClass` (deterministic semi-environments, deterministic designated policies that
are optimal for their environments, the truth `ν i₀` a measure of positive prior weight with a
uniform gap `Δ`); `2 γ^H < Δ`; the prior is supported on a finite set `F` containing the truth,
with every weight on `F` at least `q > 0`. Then on Thompson sampling's own trajectory in the
truth, for every horizon `T`,

  `Σ_{t < T} E[ -ln π_T(a*_t | h_{<t}) ] ≤ ln(1/w_μ) · H · |F| / q^H`.

In particular `E[ℓ_t] → 0`, and summably. (`thompson_per_step` alone gives `ln(1/w_μ)` per step,
i.e. `T · ln(1/w_μ)`.) -/
theorem thompson_O2_finite (hC : DetClass r γ ν w act i₀ Δ) {H : ℕ} (hH : 2 * γ ^ H < Δ)
    {F : Finset ℕ} (hi₀ : i₀ ∈ F) {q : ℝ} (hq : 0 < q) (hqF : ∀ i ∈ F, q ≤ w i)
    (hsupp : ∀ i, i ∉ F → w i = 0) (T : ℕ) :
    ∑ t ∈ Finset.range T, Ex (piT ν w act) (ν i₀) t (loss ν w act i₀) ≤
      log (1 / w i₀) * (H * F.card / q ^ H) := by
  have htail : tailW w F = 0 := by
    unfold tailW
    have e : ∀ i, (if i ∈ F then (0 : ℝ) else w i) = 0 := fun i => by
      by_cases hi : i ∈ F <;> simp [hi, hsupp i]
    simp_rw [e]
    exact tsum_zero
  have hε : tailW w F < w i₀ := by rw [htail]; exact hC.truth_pos
  have hL : 0 ≤ log (1 / w i₀) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hC.truth_pos, one_mul]
    exact (hC.w_summable.le_tsum i₀ fun j _ => hC.w_nonneg j).trans hC.w_le
  calc ∑ t ∈ Finset.range T, Ex (piT ν w act) (ν i₀) t (loss ν w act i₀)
      ≤ ∑ t ∈ Finset.range T, log (1 / w i₀) * Ex (piT ν w act) (ν i₀) t (badI ν act i₀ F) :=
        Finset.sum_le_sum fun t _ => by
          have := Ex_loss_le hC hε t
          rw [htail] at this
          simpa using this
    _ = log (1 / w i₀) * ∑ t ∈ Finset.range T, Ex (piT ν w act) (ν i₀) t (badI ν act i₀ F) := by
        rw [Finset.mul_sum]
    _ ≤ log (1 / w i₀) * (H * F.card / q ^ H) :=
        mul_le_mul_of_nonneg_left (sum_bad_le hC hH hi₀ hq hqF T) hL

/-- [UNAPPROVED STATEMENT] **O2, countable deterministic class: the log loss vanishes in mean.**
Under `DetClass` (a countable class of deterministic semi-environments with deterministic
designated policies optimal for their environments; the truth a measure of positive prior weight)
with a uniform gap `Δ > 0`: on Thompson sampling's own trajectory in the truth,

  `E[ -ln π_T(a*_t | h_{<t}) ] → 0` as `t → ∞`.

No rate: by the note's Theorem 3 the sum over `t` can be infinite for a countable class. -/
theorem thompson_O2_tendsto (hC : DetClass r γ ν w act i₀ Δ) (hΔ : 0 < Δ) :
    Filter.Tendsto (fun t => Ex (piT ν w act) (ν i₀) t (loss ν w act i₀)) Filter.atTop
      (nhds 0) := by
  classical
  have hw0 := hC.truth_pos
  obtain ⟨H, hH'⟩ := exists_pow_lt_of_lt_one (half_pos hΔ) hC.disc.γ_lt
  have hH : 2 * γ ^ H < Δ := by linarith
  have hL : 0 ≤ log (1 / w i₀) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hw0, one_mul]
    exact (hC.w_summable.le_tsum i₀ fun j _ => hC.w_nonneg j).trans hC.w_le
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun t =>
    lt_of_lt_of_le ha (Ex_loss_nonneg hC t), fun η hη => ?_⟩
  -- a finite set carrying all but a small part of the prior
  have hε₀ : 0 < w i₀ * (1 - exp (-(η / 2))) := by
    refine mul_pos hw0 (sub_pos.2 ?_)
    have := Real.exp_lt_exp.2 (show -(η / 2) < 0 by linarith)
    rwa [Real.exp_zero] at this
  obtain ⟨s, hs⟩ := ((tendsto_tsum_compl_atTop_zero w).eventually (gt_mem_nhds hε₀)).exists
  have hsT : ∑' a : {a // a ∉ s}, w a = tailW w s := by
    rw [show (∑' a : {a // a ∉ s}, w a) = ∑' a : ({a | a ∉ s} : Set ℕ), w a from rfl,
      _root_.tsum_subtype]
    refine tsum_congr fun i => ?_
    by_cases hi : i ∈ s <;> simp [Set.indicator, hi]
  rw [hsT] at hs
  set F : Finset ℕ := insert i₀ (s.filter fun i => 0 < w i) with hF
  have hi₀F : i₀ ∈ F := Finset.mem_insert_self _ _
  have hFpos : ∀ i ∈ F, 0 < w i := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hw0
    · exact (Finset.mem_filter.1 hi).2
  have htF : tailW w F ≤ tailW w s := by
    refine Summable.tsum_le_tsum (fun i => ?_) (tailW_summable hC F) (tailW_summable hC s)
    by_cases hiF : i ∈ F
    · rw [if_pos hiF]; split_ifs <;> simp [hC.w_nonneg i]
    · rw [if_neg hiF]
      by_cases his : i ∈ s
      · rw [if_pos his]
        by_contra hc
        exact hiF (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨his, not_le.1 hc⟩))
      · rw [if_neg his]
  have hεF : tailW w F < w i₀ * (1 - exp (-(η / 2))) := lt_of_le_of_lt htF hs
  have hε : tailW w F < w i₀ := by
    have : w i₀ * (1 - exp (-(η / 2))) ≤ w i₀ := by
      have := Real.exp_pos (-(η / 2))
      nlinarith
    linarith
  have hδ : -log (1 - tailW w F / w i₀) ≤ η / 2 := by
    have h1 : tailW w F / w i₀ < 1 - exp (-(η / 2)) := by
      rw [div_lt_iff₀ hw0, mul_comm]
      exact hεF
    have h2 : exp (-(η / 2)) ≤ 1 - tailW w F / w i₀ := by linarith
    have h3 := Real.log_le_log (Real.exp_pos _) h2
    rw [Real.log_exp] at h3
    linarith
  -- the smallest weight on `F`
  obtain ⟨j, hjF, hjmin⟩ := Finset.exists_min_image F w ⟨i₀, hi₀F⟩
  have hsum : Summable fun t => Ex (piT ν w act) (ν i₀) t (badI ν act i₀ F) :=
    summable_of_sum_range_le (fun t => Ex_badI_nonneg hC F t)
      (fun T => sum_bad_le hC hH hi₀F (hFpos j hjF) hjmin T)
  have hb := (hsum.tendsto_atTop_zero.const_mul (log (1 / w i₀)))
  rw [mul_zero] at hb
  filter_upwards [hb.eventually (gt_mem_nhds (half_pos hη))] with t ht
  have := Ex_loss_le hC hε t
  linarith

end Thompson

/-! ### Non-vacuity: a two-armed bandit class satisfies `DetClass`, with positive loss

Actions and percepts are `Bool`; the percept is the reward bit. In `bandit g` arm `g` pays `1`
and the other arm pays `0`, at every step. The class is `{bandit true, bandit false}` with prior
`1/2` each; each member's designated policy always pulls its paying arm. `Q*` is `1` on the
paying arm and `γ` on the other, so the gap is `1 - γ`. At the first step Thompson sampling's
loss is `ln 2 > 0`, so the theorems above are not about a class where the loss is already zero. -/

section Example

variable {γ : ℝ}

/-- The two-armed bandit in which arm `g` pays. -/
def bandit (g : Bool) : Env Bool Bool := fun _ a e => if e = decide (a = g) then 1 else 0

/-- The reward of a percept bit. -/
def rBit : Bool → ℝ := fun e => if e then 1 else 0

lemma bandit_semi (g : Bool) : IsSemiEnv (bandit g) where
  nonneg h a e := by unfold bandit; split_ifs <;> norm_num
  sum_le h a := by
    have e : ∑ e, bandit g h a e = 1 := by simp [bandit]
    exact e.le

lemma bandit_det (g : Bool) : IsDet (bandit g) := fun h a e => by
  unfold bandit; split_ifs <;> simp

lemma bandit_meas (g : Bool) (h : Hist Bool Bool) (a : Bool) : ∑ e, bandit g h a e = 1 := by
  simp [bandit]

lemma rBit_disc (h0 : 0 ≤ γ) (h1 : γ < 1) : IsDisc rBit γ :=
  ⟨fun e => by unfold rBit; split_ifs <;> norm_num,
    fun e => by unfold rBit; split_ifs <;> norm_num, h0, h1⟩

lemma bandit_qval (g : Bool) (V : Hist Bool Bool → ℝ) (h : Hist Bool Bool) (a : Bool) :
    qval rBit γ (bandit g) V h a =
      (1 - γ) * rBit (decide (a = g)) + γ * V ((a, decide (a = g)) :: h) :=
  qval_det (bandit_semi g) (by simp [bandit]) V

lemma bandit_Vn (hd : IsDisc rBit γ) (g : Bool) (n : ℕ) (h : Hist Bool Bool) :
    Vn rBit γ (bandit g) n h = 1 - γ ^ n := by
  induction n generalizing h with
  | zero => simp [Vn]
  | succ n ih =>
    simp only [Vn]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun a _ => ?_
      rw [bandit_qval, ih, pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.2 hd.γ_lt.le) (sub_nonneg.2 (hd.r_le (decide (a = g))))]
    · refine le_trans (le_of_eq ?_) (Finset.le_sup' (qval rBit γ (bandit g)
        (Vn rBit γ (bandit g) n) h) (Finset.mem_univ g))
      have e : rBit (decide (g = g)) = 1 := by simp [rBit]
      rw [bandit_qval, ih, e]
      ring

lemma bandit_Vstar (hd : IsDisc rBit γ) (g : Bool) (h : Hist Bool Bool) :
    Vstar rBit γ (bandit g) h = 1 := by
  refine le_antisymm (Vstar_bounds hd (bandit_semi g) h).2 ?_
  by_contra hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.2 (not_le.1 hc)) hd.γ_lt
  have := Vn_le_Vstar hd (bandit_semi g) n h
  rw [bandit_Vn hd] at this
  linarith

lemma bandit_Qstar (hd : IsDisc rBit γ) (g : Bool) (h : Hist Bool Bool) (a : Bool) :
    Qstar rBit γ (bandit g) h a = if a = g then 1 else γ := by
  rw [Qstar, bandit_qval, bandit_Vstar hd]
  by_cases ha : a = g
  · simp [rBit, ha]
  · simp [rBit, ha]

/-- The example class: member `0` is `bandit true`, every other member is `bandit false`. -/
def exν (i : ℕ) : Env Bool Bool := bandit (decide (i = 0))

/-- The example prior: `1/2` on members `0` and `1`. -/
noncomputable def exw (i : ℕ) : ℝ := if i < 2 then 1 / 2 else 0

/-- The example designated policies: always pull the paying arm. -/
def exAct (i : ℕ) (_ : Hist Bool Bool) : Bool := decide (i = 0)

lemma exw_summable : Summable exw :=
  summable_of_ne_finset_zero (s := Finset.range 2) fun i hi => by
    simp only [Finset.mem_range] at hi
    simp [exw, hi]

lemma exw_tsum : ∑' i, exw i = 1 := by
  rw [tsum_eq_sum (s := Finset.range 2) fun i hi => by
    simp only [Finset.mem_range] at hi
    simp [exw, hi]]
  simp [Finset.sum_range_succ, exw]
  norm_num

/-- [UNAPPROVED STATEMENT] **The hypotheses are satisfiable.** The two-armed bandit class
satisfies `DetClass` with truth `bandit true` and uniform gap `1 - γ`, for every `γ ∈ [0,1)`. -/
theorem example_detClass (h0 : 0 ≤ γ) (h1 : γ < 1) :
    DetClass rBit γ exν exw exAct 0 (1 - γ) where
  disc := rBit_disc h0 h1
  semi i := bandit_semi _
  det i := bandit_det _
  w_nonneg i := by unfold exw; split_ifs <;> norm_num
  w_summable := exw_summable
  w_le := exw_tsum.le
  opt i h b := by
    simp only [exν, exAct, bandit_Qstar (rBit_disc h0 h1)]
    split_ifs <;> linarith
  truth_pos := by norm_num [exw]
  truth_meas h a := bandit_meas _ h a
  gap h _ a ha := by
    simp only [exν, exAct, bandit_Qstar (rBit_disc h0 h1)]
    have ha' : a ≠ true := by simpa [exAct] using ha
    simp [ha']

/-- [UNAPPROVED STATEMENT] **…and the loss is not already zero.** In the example class Thompson
sampling's log loss on the optimal action at the first step is `ln 2`. -/
theorem example_loss_pos : loss exν exw exAct 0 [] = log 2 := by
  have hnum : ∀ i, exw i * lik (exν i) [] * detPol (exAct i) [] (exAct 0 []) =
      if i = 0 then 1 / 2 else 0 := by
    intro i
    by_cases hi : i = 0
    · simp [hi, exw, lik, detPol, exAct]
    · simp [hi, lik, detPol, exAct]
  have hT : piT exν exw exAct [] (exAct 0 []) = 2⁻¹ := by
    unfold piT thompson
    rw [xi_nil, exw_tsum, tsum_congr hnum, tsum_ite_eq]
    norm_num
  rw [loss, hT, Real.log_inv, neg_neg]

end Example

/-! ## The stochastic case (Theorem C of the draft)

Nothing below assumes determinism of the environments. The designated policies are still
deterministic. -/

/-! ### Values along a policy, and paths -/

section StochValues

variable [Nonempty A] {r : E → ℝ} {γ : ℝ} {ρ σ : Env A E} {p : Hist A E → A}

/-- The truncated `n`-step return of the deterministic policy `p` in `ρ` from `h`. -/
noncomputable def Wn (r : E → ℝ) (γ : ℝ) (ρ : Env A E) (p : Hist A E → A) :
    ℕ → Hist A E → ℝ
  | 0, _ => 0
  | n + 1, h => qval r γ ρ (Wn r γ ρ p n) h (p h)

lemma Wn_le_Vn (hd : IsDisc r γ) (hρ : IsSemiEnv ρ) (n : ℕ) (h : Hist A E) :
    Wn r γ ρ p n h ≤ Vn r γ ρ n h := by
  induction n generalizing h with
  | zero => simp [Wn, Vn]
  | succ n ih =>
    simp only [Wn, Vn]
    exact (qval_mono hd hρ ih h (p h)).trans
      (Finset.le_sup' (qval r γ ρ (Vn r γ ρ n) h) (Finset.mem_univ _))

/-- Stochastic Lemma 1, lower half. -/
lemma Wn_le_Qstar (hd : IsDisc r γ) (hρ : IsSemiEnv ρ) (n : ℕ) (h : Hist A E) :
    Wn r γ ρ p n h ≤ Qstar r γ ρ h (p h) := by
  cases n with
  | zero => simpa [Wn] using (Qstar_bounds hd hρ h (p h)).1
  | succ n =>
    simp only [Wn]
    exact qval_mono hd hρ (fun h' => (Wn_le_Vn hd hρ n h').trans (Vn_le_Vstar hd hρ n h')) h _

lemma qval_add_const (hρ : IsSemiEnv ρ) (hγ : 0 ≤ γ) (V : Hist A E → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : Hist A E) (a : A) :
    qval r γ ρ (fun h => V h + c) h a ≤ qval r γ ρ V h a + γ * c := by
  unfold qval
  have e : ∀ e, ρ h a e * ((1 - γ) * r e + γ * (V ((a, e) :: h) + c)) =
      ρ h a e * ((1 - γ) * r e + γ * V ((a, e) :: h)) + ρ h a e * (γ * c) := fun e => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have := mul_le_mul_of_nonneg_right (hρ.sum_le h a) (mul_nonneg hγ hc)
  linarith

/-- Stochastic Lemma 1, upper half. -/
lemma Qstar_le_Wn (hd : IsDisc r γ) (hρ : IsSemiEnv ρ) (hopt : ∀ h, IsOptAct r γ ρ h (p h))
    (n : ℕ) (h : Hist A E) : Qstar r γ ρ h (p h) ≤ Wn r γ ρ p n h + γ ^ n := by
  induction n generalizing h with
  | zero => simpa [Wn] using (Qstar_bounds hd hρ h (p h)).2
  | succ n ih =>
    simp only [Wn]
    have h1 : Qstar r γ ρ h (p h) ≤ qval r γ ρ (fun h' => Wn r γ ρ p n h' + γ ^ n) h (p h) :=
      qval_mono hd hρ (fun h' => (Vstar_le_Qstar_of_opt hd hρ (hopt h')).trans (ih h')) h _
    have h2 := qval_add_const (r := r) hρ hd.γ_nonneg (Wn r γ ρ p n)
      (pow_nonneg hd.γ_nonneg n) h (p h)
    rw [pow_succ']
    linarith

/-- The probability under `ρ` of the percept sequence `es` when `p` is followed from `h`. -/
noncomputable def plik (ρ : Env A E) (p : Hist A E → A) : Hist A E → List E → ℝ
  | _, [] => 1
  | h, e :: es => ρ h (p h) e * plik ρ p ((p h, e) :: h) es

/-- The history after following `p` from `h` and seeing the percepts `es`. -/
def ext (p : Hist A E → A) : Hist A E → List E → Hist A E
  | h, [] => h
  | h, e :: es => ext p ((p h, e) :: h) es

omit [Nonempty A] in
lemma plik_bounds (hρ : IsSemiEnv ρ) (h : Hist A E) (es : List E) :
    0 ≤ plik ρ p h es ∧ plik ρ p h es ≤ 1 := by
  induction es generalizing h with
  | nil => simp [plik]
  | cons e es ih =>
    simp only [plik]
    exact ⟨mul_nonneg (hρ.nonneg _ _ _) (ih _).1,
      mul_le_one₀ (env_le_one hρ _ _ _) (ih _).1 (ih _).2⟩

omit [Fintype A] [Fintype E] [Nonempty A] in
lemma lik_ext (ρ : Env A E) (p : Hist A E → A) (h : Hist A E) (es : List E) :
    lik ρ (ext p h es) = lik ρ h * plik ρ p h es := by
  induction es generalizing h with
  | nil => simp [ext, plik]
  | cons e es ih =>
    simp only [ext, plik]
    rw [ih]
    simp only [lik]
    ring

/-- If the `n`-step returns of `p` in `ρ` and `σ`, scaled by `α` and `β`, differ by `c > 0`,
then some percept sequence of length at most `n` has scaled probabilities differing by
`c / |E|^n`. -/
lemma exists_path (hd : IsDisc r γ) (hρ : IsSemiEnv ρ) (hσ : IsSemiEnv σ) (p : Hist A E → A) :
    ∀ (n : ℕ) (h : Hist A E) (α β c : ℝ), 0 ≤ α → 0 ≤ β → 0 < c →
      c ≤ α * Wn r γ ρ p n h - β * Wn r γ σ p n h →
      ∃ es : List E, es.length ≤ n ∧
        c / (Fintype.card E : ℝ) ^ n ≤ α * plik ρ p h es - β * plik σ p h es := by
  intro n
  induction n with
  | zero =>
    intro h α β c _ _ hc0 hc
    simp only [Wn, mul_zero, sub_zero] at hc
    linarith
  | succ n ih =>
    intro h α β c hα hβ hc0 hc
    simp only [Wn, qval] at hc
    rcases isEmpty_or_nonempty E with hE | hE
    · simp at hc
      linarith
    have hM1 : (1 : ℝ) ≤ Fintype.card E := by
      exact_mod_cast Fintype.card_pos
    have hM : (0 : ℝ) < Fintype.card E := by linarith
    set M : ℝ := (Fintype.card E : ℝ) with hMdef
    set bρ : E → ℝ := fun e => (1 - γ) * r e + γ * Wn r γ ρ p n ((p h, e) :: h) with hbρ
    set bσ : E → ℝ := fun e => (1 - γ) * r e + γ * Wn r γ σ p n ((p h, e) :: h) with hbσ
    have hsum : α * ∑ e, ρ h (p h) e * bρ e - β * ∑ e, σ h (p h) e * bσ e =
        ∑ e, (α * (ρ h (p h) e * bρ e) - β * (σ h (p h) e * bσ e)) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    obtain ⟨e, he⟩ : ∃ e, c / M ≤ α * (ρ h (p h) e * bρ e) - β * (σ h (p h) e * bσ e) := by
      by_contra hcon
      simp only [not_exists, not_le] at hcon
      have hlt : ∑ e, (α * (ρ h (p h) e * bρ e) - β * (σ h (p h) e * bσ e)) <
          ∑ _e : E, c / M :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun e _ => hcon e
      have hconst : ∑ _e : E, c / M = c := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change M * (c / M) = c
        field_simp
      rw [hconst, ← hsum] at hlt
      linarith
    have hcM : 0 < c / M := div_pos hc0 hM
    have hpow : c / M ^ (n + 1) = c / M / M ^ n := by
      rw [pow_succ', div_div]
    by_cases hA : c / M ≤ α * ρ h (p h) e - β * σ h (p h) e
    · refine ⟨[e], by simp, ?_⟩
      simp only [plik, mul_one]
      refine le_trans ?_ hA
      rw [hpow]
      exact div_le_self hcM.le (one_le_pow₀ hM1)
    · have hB : c / M ≤ α * ρ h (p h) e * Wn r γ ρ p n ((p h, e) :: h) -
          β * σ h (p h) e * Wn r γ σ p n ((p h, e) :: h) := by
        by_contra hB
        have hA' := not_le.1 hA
        have hB' := not_le.1 hB
        have hrA : r e * (α * ρ h (p h) e - β * σ h (p h) e) < c / M := by
          rcases le_or_gt 0 (α * ρ h (p h) e - β * σ h (p h) e) with h0 | h0
          · exact lt_of_le_of_lt (mul_le_of_le_one_left h0 (hd.r_le e)) hA'
          · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (hd.r_nonneg e) h0.le) hcM
        have h1 := mul_lt_mul_of_pos_left hrA (sub_pos.2 hd.γ_lt)
        have h2 := mul_le_mul_of_nonneg_left hB'.le hd.γ_nonneg
        simp only [hbρ, hbσ] at he
        nlinarith
      obtain ⟨es, hlen, hes⟩ := ih ((p h, e) :: h) (α * ρ h (p h) e) (β * σ h (p h) e) (c / M)
        (mul_nonneg hα (hρ.nonneg _ _ _)) (mul_nonneg hβ (hσ.nonneg _ _ _)) hcM hB
      refine ⟨e :: es, by simp; omega, ?_⟩
      simp only [plik]
      rw [hpow]
      linarith

/-- [UNAPPROVED STATEMENT] **Stochastic Lemma 2: disagreement gives a path-level discrepancy.**
`μ`, `ν` semi-environments, `pμ`, `pν` everywhere-optimal deterministic policies for them; at `h`
the action `pν h` is worse than `pμ h` in `μ` by at least `Δ`, and `2 γ^H < Δ`. Then, with
`d = (Δ - 2γ^H) / 2 / |E|^H`: either some percept sequence of length `≤ H` along `pν` is at least
`d` more probable under `ν` than under `μ`, or some percept sequence of length `≤ H` along `pμ`
is at least `d` more probable under `μ` than under `ν`. -/
theorem disagree_path (hd : IsDisc r γ) {μ ν : Env A E} (hμ : IsSemiEnv μ) (hν : IsSemiEnv ν)
    {pμ pν : Hist A E → A} (hoμ : ∀ h, IsOptAct r γ μ h (pμ h))
    (hoν : ∀ h, IsOptAct r γ ν h (pν h)) {Δ : ℝ} {H : ℕ} (hH : 2 * γ ^ H < Δ) (h : Hist A E)
    (hgap : Qstar r γ μ h (pν h) + Δ ≤ Qstar r γ μ h (pμ h)) :
    (∃ es : List E, es.length ≤ H ∧ (Δ - 2 * γ ^ H) / 2 / (Fintype.card E : ℝ) ^ H ≤
        plik ν pν h es - plik μ pν h es) ∨
    (∃ es : List E, es.length ≤ H ∧ (Δ - 2 * γ ^ H) / 2 / (Fintype.card E : ℝ) ^ H ≤
        plik μ pμ h es - plik ν pμ h es) := by
  have a1 := Qstar_le_Wn hd hν hoν H h
  have a2 := Wn_le_Qstar (p := pν) hd hμ H h
  have a3 := Qstar_le_Wn hd hμ hoμ H h
  have a4 := Wn_le_Qstar (p := pμ) hd hν H h
  have a5 := hoν h (pμ h)
  have hc : 0 < (Δ - 2 * γ ^ H) / 2 := by linarith
  by_cases h1 : (Δ - 2 * γ ^ H) / 2 ≤ Wn r γ ν pν H h - Wn r γ μ pν H h
  · left
    obtain ⟨es, hlen, hes⟩ := exists_path hd hν hμ pν H h 1 1 _ zero_le_one zero_le_one hc
      (by simpa using h1)
    exact ⟨es, hlen, by simpa using hes⟩
  · right
    have h2 : (Δ - 2 * γ ^ H) / 2 ≤ Wn r γ μ pμ H h - Wn r γ ν pμ H h := by linarith
    obtain ⟨es, hlen, hes⟩ := exists_path hd hμ hν pμ H h 1 1 _ zero_le_one zero_le_one hc
      (by simpa using h2)
    exact ⟨es, hlen, by simpa using hes⟩

end StochValues

/-! ### Sums over continuations, and the Hellinger potential -/

section Potential

/-- `SH π n F h`: the sum of `F` over the `n`-step continuations of `h`, weighted by the
policy's action probabilities only (the conditional version of `S0`). -/
noncomputable def SH (π : Policy A E) : ℕ → (Hist A E → ℝ) → Hist A E → ℝ
  | 0, F, h => F h
  | n + 1, F, h => ∑ a, π h a * ∑ e, SH π n F ((a, e) :: h)

lemma SH_comm (π : Policy A E) (F : Hist A E → ℝ) (n : ℕ) (h : Hist A E) :
    SH π n (SH π 1 F) h = SH π (n + 1) F h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change (∑ a, π h a * ∑ e, SH π n (SH π 1 F) ((a, e) :: h)) =
      ∑ a, π h a * ∑ e, SH π (n + 1) F ((a, e) :: h)
    simp_rw [ih]

/-- The Markov property for `S0`. -/
lemma S0_markov (π : Policy A E) (t n : ℕ) (F : Hist A E → ℝ) :
    S0 π (t + n) F = S0 π t (SH π n F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    change S0 π (t + n) (fun h => ∑ a, π h a * ∑ e, F ((a, e) :: h)) = _
    rw [ih]
    congr 1
    funext h
    exact SH_comm π F n h

lemma SH_add_steps (π : Policy A E) (F : Hist A E → ℝ) (n k : ℕ) (h : Hist A E) :
    SH π (n + k) F h = SH π n (SH π k F) h := by
  induction n generalizing h with
  | zero => simp [SH]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [SH]
    simp_rw [ih]

variable {π : Policy A E}

lemma SH_mono (hπ : IsPolicy π) {F G : Hist A E → ℝ} (hFG : ∀ h, F h ≤ G h) (n : ℕ)
    (h : Hist A E) : SH π n F h ≤ SH π n G h := by
  induction n generalizing h with
  | zero => exact hFG h
  | succ n ih =>
    simp only [SH]
    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun e _ => ih _) (hπ.nonneg h a)

lemma SH_nonneg (hπ : IsPolicy π) {F : Hist A E → ℝ} (hF : ∀ h, 0 ≤ F h) (n : ℕ)
    (h : Hist A E) : 0 ≤ SH π n F h := by
  induction n generalizing h with
  | zero => exact hF h
  | succ n ih =>
    simp only [SH]
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hπ.nonneg h a)
      (Finset.sum_nonneg fun e _ => ih _)

lemma SH_super (hπ : IsPolicy π) {F : Hist A E → ℝ}
    (hF : ∀ h a, ∑ e, F ((a, e) :: h) ≤ F h) (n : ℕ) (h : Hist A E) : SH π n F h ≤ F h := by
  induction n generalizing h with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [SH]
    calc ∑ a, π h a * ∑ e, SH π n F ((a, e) :: h) ≤ ∑ a, π h a * F h :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
            ((Finset.sum_le_sum fun e _ => ih _).trans (hF h a)) (hπ.nonneg h a)
      _ = F h := by rw [← Finset.sum_mul, hπ.sum_eq, one_mul]

lemma SH_anti (hπ : IsPolicy π) {F : Hist A E → ℝ}
    (hF : ∀ h a, ∑ e, F ((a, e) :: h) ≤ F h) {n m : ℕ} (hnm : n ≤ m) (h : Hist A E) :
    SH π m F h ≤ SH π n F h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [SH_add_steps]
  exact SH_mono hπ (SH_super hπ hF k) n h

lemma SH_smul (π : Policy A E) (c : ℝ) (F : Hist A E → ℝ) (n : ℕ) (h : Hist A E) :
    SH π n (fun h => c * F h) h = c * SH π n F h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [SH]
    simp_rw [ih, ← Finset.mul_sum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

lemma SH_add (π : Policy A E) (F G : Hist A E → ℝ) (n : ℕ) (h : Hist A E) :
    SH π n (fun h => F h + G h) h = SH π n F h + SH π n G h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [SH]
    simp_rw [ih, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]

/-- The probability that `π` plays the actions of `p` along the path `es` from `h`. -/
noncomputable def ppol (π : Policy A E) (p : Hist A E → A) : Hist A E → List E → ℝ
  | _, [] => 1
  | h, e :: es => π h (p h) * ppol π p ((p h, e) :: h) es

lemma ppol_nonneg (hπ : IsPolicy π) (p : Hist A E → A) (h : Hist A E) (es : List E) :
    0 ≤ ppol π p h es := by
  induction es generalizing h with
  | nil => simp [ppol]
  | cons e es ih => simp only [ppol]; exact mul_nonneg (hπ.nonneg _ _) (ih _)

/-- One path is a lower bound for the sum over all continuations of a nonnegative function. -/
lemma SH_path (hπ : IsPolicy π) {D : Hist A E → ℝ} (hD : ∀ h, 0 ≤ D h) (p : Hist A E → A)
    (es : List E) (h : Hist A E) : ppol π p h es * D (ext p h es) ≤ SH π es.length D h := by
  induction es generalizing h with
  | nil => simp [ppol, ext, SH]
  | cons e es ih =>
    simp only [ppol, ext, List.length_cons, SH]
    calc π h (p h) * ppol π p ((p h, e) :: h) es * D (ext p ((p h, e) :: h) es)
        ≤ π h (p h) * SH π es.length D ((p h, e) :: h) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (ih _) (hπ.nonneg _ _)
      _ ≤ π h (p h) * ∑ e', SH π es.length D ((p h, e') :: h) :=
          mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun e' => SH π es.length D ((p h, e') :: h))
              (fun e' _ => SH_nonneg hπ hD _ _) (Finset.mem_univ e)) (hπ.nonneg _ _)
      _ ≤ ∑ a, π h a * ∑ e', SH π es.length D ((a, e') :: h) :=
          Finset.single_le_sum (f := fun a => π h a * ∑ e', SH π es.length D ((a, e') :: h))
            (fun a _ => mul_nonneg (hπ.nonneg _ _)
              (Finset.sum_nonneg fun e' _ => SH_nonneg hπ hD _ _)) (Finset.mem_univ (p h))

/-- The Hellinger-affinity potential `Y(h) = √(ρ(h) · μ(h))`. -/
noncomputable def Y (ρ μ : Env A E) (h : Hist A E) : ℝ := Real.sqrt (lik ρ h * lik μ h)

omit [Fintype A] [Fintype E] in
lemma sqrt_mul_le_avg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [show a * b = Real.sqrt a ^ 2 * Real.sqrt b ^ 2 by
    rw [Real.sq_sqrt ha, Real.sq_sqrt hb], ← mul_pow, Real.sqrt_sq
      (mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

variable {ρ μ : Env A E}

lemma lik_super (hρ : IsSemiEnv ρ) (h : Hist A E) (a : A) :
    ∑ e, lik ρ ((a, e) :: h) ≤ lik ρ h := by
  simp only [lik]
  rw [← Finset.mul_sum]
  exact mul_le_of_le_one_right (lik_nonneg hρ h) (hρ.sum_le h a)

omit [Fintype A] [Fintype E] in
lemma Y_nonneg (ρ μ : Env A E) (h : Hist A E) : 0 ≤ Y ρ μ h := Real.sqrt_nonneg _

lemma Y_super (hρ : IsSemiEnv ρ) (hμ : IsSemiEnv μ) (h : Hist A E) (a : A) :
    ∑ e, Y ρ μ ((a, e) :: h) ≤ Y ρ μ h := by
  have e1 : ∀ e, Y ρ μ ((a, e) :: h) = Y ρ μ h * Real.sqrt (ρ h a e * μ h a e) := by
    intro e
    unfold Y
    simp only [lik]
    rw [← Real.sqrt_mul (mul_nonneg (lik_nonneg hρ h) (lik_nonneg hμ h))]
    congr 1
    ring
  simp_rw [e1]
  rw [← Finset.mul_sum]
  refine mul_le_of_le_one_right (Y_nonneg ρ μ h) ?_
  calc ∑ e, Real.sqrt (ρ h a e * μ h a e) ≤ ∑ e, (ρ h a e + μ h a e) / 2 :=
        Finset.sum_le_sum fun e _ => sqrt_mul_le_avg (hρ.nonneg h a e) (hμ.nonneg h a e)
    _ = (∑ e, ρ h a e + ∑ e, μ h a e) / 2 := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
    _ ≤ 1 := by linarith [hρ.sum_le h a, hμ.sum_le h a]

/-- The drop of the potential over the length of a path is at least the path's probability of
being played times its Hellinger term. -/
lemma Y_deficit (hπ : IsPolicy π) (hρ : IsSemiEnv ρ) (hμ : IsSemiEnv μ) (p : Hist A E → A)
    (h : Hist A E) (es : List E) :
    ppol π p h es * (Y ρ μ h * ((plik ρ p h es + plik μ p h es) / 2 -
        Real.sqrt (plik ρ p h es * plik μ p h es))) ≤
      Y ρ μ h - SH π es.length (Y ρ μ) h := by
  have hsup := SH_super hπ (Y_super hρ hμ) es.length h
  rcases (Y_nonneg ρ μ h).eq_or_lt with h0 | hpos
  · rw [← h0] at hsup ⊢
    simp only [zero_mul, mul_zero]
    linarith
  have hLρ := lik_nonneg hρ h
  have hLμ := lik_nonneg hμ h
  have hYsq : Y ρ μ h * Y ρ μ h = lik ρ h * lik μ h :=
    Real.mul_self_sqrt (mul_nonneg hLρ hLμ)
  -- the auxiliary nonnegative function
  set D : Hist A E → ℝ := fun h' =>
    (lik μ h / 2) * lik ρ h' + ((lik ρ h / 2) * lik μ h' + (-(Y ρ μ h)) * Y ρ μ h') with hD
  have hYY : ∀ h', Y ρ μ h * Y ρ μ h' =
      Real.sqrt ((lik μ h * lik ρ h') * (lik ρ h * lik μ h')) := by
    intro h'
    unfold Y
    rw [← Real.sqrt_mul (mul_nonneg hLρ hLμ)]
    congr 1
    ring
  have hD0 : ∀ h', 0 ≤ D h' := by
    intro h'
    have := sqrt_mul_le_avg (mul_nonneg hLμ (lik_nonneg hρ h'))
      (mul_nonneg hLρ (lik_nonneg hμ h'))
    rw [← hYY] at this
    simp only [hD]
    linarith
  have hpath := SH_path hπ hD0 p es h
  have hSH : SH π es.length D h = (lik μ h / 2) * SH π es.length (lik ρ) h +
      ((lik ρ h / 2) * SH π es.length (lik μ) h +
        (-(Y ρ μ h)) * SH π es.length (Y ρ μ) h) := by
    simp only [hD]
    rw [SH_add, SH_smul, SH_add, SH_smul, SH_smul]
  have h1 := SH_super hπ (lik_super hρ) es.length h
  have h2 := SH_super hπ (lik_super hμ) es.length h
  have h3 := mul_le_mul_of_nonneg_left h1 (div_nonneg hLμ zero_le_two)
  have h4 := mul_le_mul_of_nonneg_left h2 (div_nonneg hLρ zero_le_two)
  have hDext : D (ext p h es) = Y ρ μ h * (Y ρ μ h * ((plik ρ p h es + plik μ p h es) / 2 -
      Real.sqrt (plik ρ p h es * plik μ p h es))) := by
    have hYext : Y ρ μ (ext p h es) =
        Y ρ μ h * Real.sqrt (plik ρ p h es * plik μ p h es) := by
      unfold Y
      rw [lik_ext, lik_ext, ← Real.sqrt_mul (mul_nonneg hLρ hLμ)]
      congr 1
      ring
    simp only [hD]
    rw [lik_ext, lik_ext, hYext]
    linear_combination (-(plik ρ p h es + plik μ p h es) / 2) * hYsq
  rw [hDext] at hpath
  -- divide by `Y h > 0`
  have hfin : Y ρ μ h * (ppol π p h es * (Y ρ μ h * ((plik ρ p h es + plik μ p h es) / 2 -
      Real.sqrt (plik ρ p h es * plik μ p h es)))) ≤
      Y ρ μ h * (Y ρ μ h - SH π es.length (Y ρ μ) h) := by
    rw [hSH] at hpath
    nlinarith
  exact le_of_mul_le_mul_left hfin hpos

lemma S0_nonneg (hπ : IsPolicy π) (t : ℕ) {F : Hist A E → ℝ} (hF : ∀ h, 0 ≤ F h) :
    0 ≤ S0 π t F := by
  induction t generalizing F with
  | zero => exact hF []
  | succ t ih =>
    simp only [S0]
    exact ih fun h => Finset.sum_nonneg fun a _ => mul_nonneg (hπ.nonneg h a)
      (Finset.sum_nonneg fun e _ => hF _)

omit [Fintype A] [Fintype E] in
/-- If `x (t + H) ≤ x t - c · b t` and `0 ≤ x ≤ C`, then `c · Σ_{t<T} b t ≤ H · C`. -/
lemma telescope_bound (x b : ℕ → ℝ) (c C : ℝ) (H : ℕ) (hx0 : ∀ t, 0 ≤ x t)
    (hxC : ∀ t, x t ≤ C) (hstep : ∀ t, x (t + H) ≤ -c * b t + x t) (T : ℕ) :
    c * ∑ t ∈ Finset.range T, b t ≤ H * C := by
  have e1 := Finset.sum_range_add x T H
  have e2 := Finset.sum_range_add x H T
  rw [add_comm T H] at e1
  have e4 : ∑ t ∈ Finset.range H, x t ≤ H * C := by
    calc ∑ t ∈ Finset.range H, x t ≤ ∑ _t ∈ Finset.range H, C :=
          Finset.sum_le_sum fun t _ => hxC t
      _ = H * C := by simp
  have e5 : 0 ≤ ∑ t ∈ Finset.range H, x (T + t) := Finset.sum_nonneg fun t _ => hx0 _
  have e6 : c * ∑ t ∈ Finset.range T, b t ≤
      ∑ t ∈ Finset.range T, x t - ∑ t ∈ Finset.range T, x (H + t) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    have := hstep t
    rw [add_comm t H] at this
    linarith
  linarith

omit [Fintype A] [Fintype E] in
/-- A lower bound for the Hellinger term of two numbers in `[0,1]` that differ by `d`. -/
lemma hell_lower {a b d : ℝ} (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hd : 0 ≤ d)
    (hab : d ≤ a - b) : d ^ 2 / 8 ≤ (a + b) / 2 - Real.sqrt (a * b) := by
  have ha0 : 0 ≤ a := by linarith
  have hs := Real.sqrt_nonneg a
  have ht := Real.sqrt_nonneg b
  have hs2 := Real.sq_sqrt ha0
  have ht2 := Real.sq_sqrt hb0
  have hs1 : Real.sqrt a ≤ 1 := Real.sqrt_le_one.2 ha1
  have ht1 : Real.sqrt b ≤ 1 := Real.sqrt_le_one.2 hb1
  have hst : 0 ≤ Real.sqrt a - Real.sqrt b :=
    sub_nonneg.2 (Real.sqrt_le_sqrt (by linarith))
  have hdiff : d / 2 ≤ Real.sqrt a - Real.sqrt b := by
    nlinarith [mul_nonneg hst (by linarith : 0 ≤ 2 - (Real.sqrt a + Real.sqrt b))]
  have hsq : (d / 2) ^ 2 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hdiff 2
  rw [Real.sqrt_mul ha0]
  nlinarith

end Potential

/-! ### Thompson sampling in a stochastic class -/

section StochThompson

variable [DecidableEq A] [Nonempty A] {r : E → ℝ} {γ : ℝ} {ν : ℕ → Env A E} {w : ℕ → ℝ}
  {act : ℕ → Hist A E → A} {i₀ : ℕ} {Δ : ℝ} {Bad : ℕ → Hist A E → Prop}

/-- [UNAPPROVED STATEMENT] **A Bayesian class with optimal designated policies (no gap).** A
countable class `ν i` of semi-environments with prior weights `w i ≥ 0`, `Σ w ≤ 1`; member `i`'s
designated policy is the deterministic policy `act i`, optimal for `ν i` at every history; the
truth `ν i₀` is a measure of positive weight. -/
structure OptClass (r : E → ℝ) (γ : ℝ) (ν : ℕ → Env A E) (w : ℕ → ℝ)
    (act : ℕ → Hist A E → A) (i₀ : ℕ) : Prop where
  disc : IsDisc r γ
  semi : ∀ i, IsSemiEnv (ν i)
  w_nonneg : ∀ i, 0 ≤ w i
  w_summable : Summable w
  w_le : ∑' i, w i ≤ 1
  opt : ∀ i h, IsOptAct r γ (ν i) h (act i h)
  truth_pos : 0 < w i₀
  truth_meas : ∀ h a, ∑ e, ν i₀ h a e = 1

/-- [UNAPPROVED STATEMENT] **The hypotheses of O2 (stochastic).** As `DetClass` without
determinism: a countable class `ν i` of semi-environments with prior weights `w i`; member `i`'s
designated policy is the deterministic policy `act i`, optimal for `ν i` at every history; the
truth `ν i₀` is a measure of positive weight with a **uniform gap** `Δ`: at every history of
positive probability under the truth, every action other than `act i₀ h` has `Q*` smaller by at
least `Δ`. -/
structure GapClass (r : E → ℝ) (γ : ℝ) (ν : ℕ → Env A E) (w : ℕ → ℝ)
    (act : ℕ → Hist A E → A) (i₀ : ℕ) (Δ : ℝ) : Prop where
  disc : IsDisc r γ
  semi : ∀ i, IsSemiEnv (ν i)
  w_nonneg : ∀ i, 0 ≤ w i
  w_summable : Summable w
  w_le : ∑' i, w i ≤ 1
  opt : ∀ i h, IsOptAct r γ (ν i) h (act i h)
  truth_pos : 0 < w i₀
  truth_meas : ∀ h a, ∑ e, ν i₀ h a e = 1
  gap : ∀ h, lik (ν i₀) h ≠ 0 → ∀ a, a ≠ act i₀ h →
    Qstar r γ (ν i₀) h a + Δ ≤ Qstar r γ (ν i₀) h (act i₀ h)

lemma DetClass.toGapClass (hC : DetClass r γ ν w act i₀ Δ) : GapClass r γ ν w act i₀ Δ :=
  ⟨hC.disc, hC.semi, hC.w_nonneg, hC.w_summable, hC.w_le, hC.opt, hC.truth_pos, hC.truth_meas,
    hC.gap⟩

lemma GapClass.toOptClass (hC : GapClass r γ ν w act i₀ Δ) : OptClass r γ ν w act i₀ :=
  ⟨hC.disc, hC.semi, hC.w_nonneg, hC.w_summable, hC.w_le, hC.opt, hC.truth_pos, hC.truth_meas⟩

/-- The interventional posterior weight `w(k | h) = w_k ν_k(h) / ξ(h)`. -/
noncomputable def post (ν : ℕ → Env A E) (w : ℕ → ℝ) (k : ℕ) (h : Hist A E) : ℝ :=
  w k * lik (ν k) h / xi ν w h

lemma OptClass.piP_isPolicy (hC : OptClass r γ ν w act i₀) : IsPolicy (piP ν w act i₀) :=
  thompsonP_isPolicy hC.semi hC.w_nonneg hC.w_summable (fun _ => detPol_isPolicy _)
    (detPol_isPolicy _)

lemma post_nonneg (hC : OptClass r γ ν w act i₀) (k : ℕ) (h : Hist A E) :
    0 ≤ post ν w k h :=
  div_nonneg (mul_nonneg (hC.w_nonneg k) (lik_nonneg (hC.semi k) h))
    (xi_nonneg hC.semi hC.w_nonneg h)

lemma post_le_one (hC : OptClass r γ ν w act i₀) (k : ℕ) (h : Hist A E) :
    post ν w k h ≤ 1 :=
  div_le_one_of_le₀ (le_xi hC.semi hC.w_nonneg hC.w_summable k h)
    (xi_nonneg hC.semi hC.w_nonneg h)

/-- Thompson sampling plays member `k`'s action with probability at least `k`'s posterior. -/
lemma piP_ge_post (hC : OptClass r γ ν w act i₀) (k : ℕ) (h : Hist A E) :
    post ν w k h ≤ piP ν w act i₀ h (act k h) := by
  by_cases hξ : xi ν w h = 0
  · have e : post ν w k h = 0 := by simp [post, hξ]
    rw [e]
    exact hC.piP_isPolicy.nonneg h _
  · have h1 : w k * lik (ν k) h * detPol (act k) h (act k h) / xi ν w h ≤
        thompson ν w (fun i => detPol (act i)) h (act k h) :=
      thompson_ge hC.semi hC.w_nonneg hC.w_summable (fun i => detPol_isPolicy (act i)) k h
        (act k h)
    have h2 : detPol (act k) h (act k h) = 1 := by simp [detPol]
    rw [h2, mul_one] at h1
    simpa [piP, thompsonP, hξ, post] using h1

lemma post_step (hC : OptClass r γ ν w act i₀) (k : ℕ) (h : Hist A E) (a : A) (e : E) :
    post ν w k h * ν k h a e ≤ post ν w k ((a, e) :: h) := by
  have hnum : 0 ≤ w k * lik (ν k) ((a, e) :: h) :=
    mul_nonneg (hC.w_nonneg k) (lik_nonneg (hC.semi k) _)
  have hle : xi ν w ((a, e) :: h) ≤ xi ν w h :=
    (Finset.single_le_sum (f := fun e => xi ν w ((a, e) :: h))
      (fun e _ => xi_nonneg hC.semi hC.w_nonneg _) (Finset.mem_univ e)).trans
      (xi_super hC.semi hC.w_nonneg hC.w_summable h a)
  have e1 : post ν w k h * ν k h a e = w k * lik (ν k) ((a, e) :: h) / xi ν w h := by
    simp only [post, lik]
    ring
  rw [e1]
  rcases (xi_nonneg hC.semi hC.w_nonneg ((a, e) :: h)).eq_or_lt with h0 | hpos
  · have hz : w k * lik (ν k) ((a, e) :: h) = 0 :=
      le_antisymm ((le_xi hC.semi hC.w_nonneg hC.w_summable k _).trans_eq h0.symm) hnum
    rw [hz, zero_div]
    exact post_nonneg hC k _
  · exact div_le_div_of_nonneg_left hnum hpos hle

/-- Step 3 of the draft: Thompson sampling follows a path of member `k`'s policy with
probability at least `(w(k|h) · ν_k(path))^{length}`. -/
lemma ppol_ge (hC : OptClass r γ ν w act i₀) (k : ℕ) (es : List E) :
    ∀ h : Hist A E, (post ν w k h * plik (ν k) (act k) h es) ^ es.length ≤
      ppol (piP ν w act i₀) (act k) h es := by
  induction es with
  | nil => intro h; simp [ppol]
  | cons e es ih =>
    intro h
    simp only [plik, ppol, List.length_cons]
    have hu0 := post_nonneg hC k h
    have hx := plik_bounds (p := act k) (hC.semi k) ((act k h, e) :: h) es
    have hν0 := (hC.semi k).nonneg h (act k h) e
    have hν1 := env_le_one (hC.semi k) h (act k h) e
    have h1 := piP_ge_post hC k h
    have h2 := ih ((act k h, e) :: h)
    have h3 := post_step hC k h (act k h) e
    have hbase0 : 0 ≤ post ν w k h * (ν k h (act k h) e *
        plik (ν k) (act k) ((act k h, e) :: h) es) :=
      mul_nonneg hu0 (mul_nonneg hν0 hx.1)
    have h4 : (post ν w k h * (ν k h (act k h) e *
        plik (ν k) (act k) ((act k h, e) :: h) es)) ^ es.length ≤
        (post ν w k ((act k h, e) :: h) *
          plik (ν k) (act k) ((act k h, e) :: h) es) ^ es.length := by
      refine pow_le_pow_left₀ hbase0 ?_ _
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h3 hx.1
    have h5 : post ν w k h * (ν k h (act k h) e *
        plik (ν k) (act k) ((act k h, e) :: h) es) ≤ post ν w k h :=
      mul_le_of_le_one_right hu0 (mul_le_one₀ hν1 hx.1 hx.2)
    rw [pow_succ']
    exact (mul_le_mul h5 h4 (pow_nonneg hbase0 _) hu0).trans
      (mul_le_mul h1 h2 (pow_nonneg (mul_nonneg (post_nonneg hC k _) hx.1) _)
        (hC.piP_isPolicy.nonneg _ _))

open Classical in
/-- The indicator of `Bad i h`. In the O2 theorem `Bad i h` is "member `i` disagrees with the
truth about the optimal action at `h`"; in the no-gap theorem it is "member `i`'s action at `h`
is `Δ`-suboptimal in the truth". -/
noncomputable def indI (Bad : ℕ → Hist A E → Prop) (i : ℕ) (h : Hist A E) : ℝ :=
  if Bad i h then 1 else 0

/-- The summand of (★): `Y_i(h) · min(w(i|h), w(μ|h))^H · 1[Bad i h]`. -/
noncomputable def Bterm (ν : ℕ → Env A E) (w : ℕ → ℝ) (Bad : ℕ → Hist A E → Prop) (i₀ : ℕ)
    (H i : ℕ) (h : Hist A E) : ℝ :=
  Y (ν i) (ν i₀) h * min (post ν w i h) (post ν w i₀ h) ^ H * indI Bad i h

lemma Bterm_nonneg (hC : OptClass r γ ν w act i₀) (H i : ℕ) (h : Hist A E) :
    0 ≤ Bterm ν w Bad i₀ H i h := by
  unfold Bterm indI
  have h1 := Y_nonneg (ν i) (ν i₀) h
  have h2 : 0 ≤ min (post ν w i h) (post ν w i₀ h) ^ H :=
    pow_nonneg (le_min (post_nonneg hC i h) (post_nonneg hC i₀ h)) H
  split_ifs
  · simpa using mul_nonneg h1 h2
  · simp

/-- Step 4 of the draft: at every history, over `H` steps the potential of rival `i` drops by at
least `κ · Y_i(h) · min(w(i|h), w(μ|h))^H` if `i` disagrees with the truth at `h`. -/
lemma keyS (hC : OptClass r γ ν w act i₀) {H : ℕ} (hH : 2 * γ ^ H < Δ) (i : ℕ)
    (hBad : ∀ h, lik (ν i₀) h ≠ 0 → Bad i h →
      Qstar r γ (ν i₀) h (act i h) + Δ ≤ Qstar r γ (ν i₀) h (act i₀ h))
    (h : Hist A E) :
    SH (piP ν w act i₀) H (Y (ν i) (ν i₀)) h ≤
      -(((Δ - 2 * γ ^ H) / 2 / (Fintype.card E : ℝ) ^ H) ^ (H + 2) / 8) *
        Bterm ν w Bad i₀ H i h + Y (ν i) (ν i₀) h := by
  have hπ := hC.piP_isPolicy
  have hYs := Y_super (hC.semi i) (hC.semi i₀)
  have hsup := SH_super hπ hYs H h
  by_cases hdis : Bad i h
  swap
  · have e : Bterm ν w Bad i₀ H i h = 0 := by simp [Bterm, indI, hdis]
    rw [e, mul_zero, zero_add]
    exact hsup
  rcases (Y_nonneg (ν i) (ν i₀) h).eq_or_lt with h0 | hpos
  · have e : Bterm ν w Bad i₀ H i h = 0 := by simp [Bterm, ← h0]
    rw [e, mul_zero, zero_add]
    exact hsup
  have hlμ : lik (ν i₀) h ≠ 0 := by
    intro hz
    simp [Y, hz] at hpos
  have hE : Nonempty E := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := hC.truth_meas h (act i h)
    simp at this
  have hM : (0 : ℝ) < (Fintype.card E : ℝ) ^ H := by
    have : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
    exact pow_pos this H
  set d : ℝ := (Δ - 2 * γ ^ H) / 2 / (Fintype.card E : ℝ) ^ H with hd
  have hd0 : 0 < d := div_pos (by linarith) hM
  set m : ℝ := min (post ν w i h) (post ν w i₀ h) with hm
  have hm0 : 0 ≤ m := le_min (post_nonneg hC i h) (post_nonneg hC i₀ h)
  have hm1 : m ≤ 1 := (min_le_left _ _).trans (post_le_one hC i h)
  have hB : Bterm ν w Bad i₀ H i h = Y (ν i) (ν i₀) h * m ^ H := by
    simp [Bterm, indI, hdis, hm]
  have halg : d ^ (H + 2) / 8 * (Y (ν i) (ν i₀) h * m ^ H) =
      (m * d) ^ H * (Y (ν i) (ν i₀) h * (d ^ 2 / 8)) := by
    rw [mul_pow, pow_add]
    ring
  rw [hB]
  -- the common end of both cases
  have hfinish : ∀ (pp X : ℝ) (len : ℕ), len ≤ H → 0 ≤ pp → (m * d) ^ len ≤ pp → m * d ≤ 1 →
      d ^ 2 / 8 ≤ X → pp * (Y (ν i) (ν i₀) h * X) ≤
        Y (ν i) (ν i₀) h - SH (piP ν w act i₀) len (Y (ν i) (ν i₀)) h →
      SH (piP ν w act i₀) len (Y (ν i) (ν i₀)) h ≥ SH (piP ν w act i₀) H (Y (ν i) (ν i₀)) h →
      SH (piP ν w act i₀) H (Y (ν i) (ν i₀)) h ≤
        -(d ^ (H + 2) / 8) * (Y (ν i) (ν i₀) h * m ^ H) + Y (ν i) (ν i₀) h := by
    intro pp X len hlen hpp0 hpp hmd1 hX hdef hanti
    have hmd0 : 0 ≤ m * d := mul_nonneg hm0 hd0.le
    have h1 : (m * d) ^ H ≤ (m * d) ^ len := pow_le_pow_of_le_one hmd0 hmd1 hlen
    have h2 : (m * d) ^ H * (Y (ν i) (ν i₀) h * (d ^ 2 / 8)) ≤
        pp * (Y (ν i) (ν i₀) h * X) :=
      mul_le_mul (h1.trans hpp) (mul_le_mul_of_nonneg_left hX hpos.le)
        (mul_nonneg hpos.le (by positivity)) hpp0
    rw [neg_mul, halg]
    linarith
  have hgap := hBad h hlμ hdis
  rcases disagree_path hC.disc (hC.semi i₀) (hC.semi i) (hC.opt i₀) (hC.opt i) hH h hgap with
    ⟨es, hlen, hes⟩ | ⟨es, hlen, hes⟩
  · have hx := plik_bounds (p := act i) (hC.semi i) h es
    have hy := plik_bounds (p := act i) (hC.semi i₀) h es
    have hdx : d ≤ plik (ν i) (act i) h es := by linarith [hy.1]
    refine hfinish (ppol (piP ν w act i₀) (act i) h es) _ es.length hlen
      (ppol_nonneg hπ _ _ _) ?_ ?_ (hell_lower hx.2 hy.1 hy.2 hd0.le hes)
      (Y_deficit hπ (hC.semi i) (hC.semi i₀) (act i) h es) (SH_anti hπ hYs hlen h)
    · exact (pow_le_pow_left₀ (mul_nonneg hm0 hd0.le)
        (mul_le_mul (min_le_left _ _) hdx hd0.le (post_nonneg hC i h)) _).trans
        (ppol_ge hC i es h)
    · exact mul_le_one₀ hm1 hd0.le (hdx.trans hx.2)
  · have hx := plik_bounds (p := act i₀) (hC.semi i₀) h es
    have hy := plik_bounds (p := act i₀) (hC.semi i) h es
    have hdx : d ≤ plik (ν i₀) (act i₀) h es := by linarith [hy.1]
    have hhell := hell_lower hx.2 hy.1 hy.2 hd0.le hes
    rw [add_comm, mul_comm] at hhell
    refine hfinish (ppol (piP ν w act i₀) (act i₀) h es) _ es.length hlen
      (ppol_nonneg hπ _ _ _) ?_ ?_ hhell
      (Y_deficit hπ (hC.semi i) (hC.semi i₀) (act i₀) h es) (SH_anti hπ hYs hlen h)
    · exact (pow_le_pow_left₀ (mul_nonneg hm0 hd0.le)
        (mul_le_mul (min_le_right _ _) hdx hd0.le (post_nonneg hC i₀ h)) _).trans
        (ppol_ge hC i₀ es h)
    · exact mul_le_one₀ hm1 hd0.le (hdx.trans hx.2)

/-- [UNAPPROVED STATEMENT] **(★) of the draft: the information budget of a rival.** Under
`OptClass` (no gap assumed), let `2 γ^H < Δ` and let `Bad i h` be any condition on histories that,
at histories of positive probability under the truth, implies that member `i`'s action is worse
than the truth's by at least `Δ` in the truth's `Q*`. Then for every horizon `T`, with
`κ = ((Δ - 2γ^H)/2/|E|^H)^(H+2) / 8`:

  `κ · Σ_{t<T} Σ_{|h|=t} π_T-part(h) · √(ν_i(h) μ(h)) · min(w(i|h), w(μ|h))^H · 1[Bad i h] ≤ H`.

Here `Σ_{|h|=t} π_T-part(h) √(ν_i(h) μ(h)) f(h) = E_μ[√(ν_i(h_t)/μ(h_t)) f(h_t)]`. -/
theorem sum_Bterm_le (hC : OptClass r γ ν w act i₀) {H : ℕ} (hH : 2 * γ ^ H < Δ) (i : ℕ)
    (hBad : ∀ h, lik (ν i₀) h ≠ 0 → Bad i h →
      Qstar r γ (ν i₀) h (act i h) + Δ ≤ Qstar r γ (ν i₀) h (act i₀ h))
    (T : ℕ) :
    ((Δ - 2 * γ ^ H) / 2 / (Fintype.card E : ℝ) ^ H) ^ (H + 2) / 8 *
      ∑ t ∈ Finset.range T, S0 (piP ν w act i₀) t (Bterm ν w Bad i₀ H i) ≤ H := by
  have hπ := hC.piP_isPolicy
  have hYs := Y_super (hC.semi i) (hC.semi i₀)
  have h := telescope_bound (fun t => S0 (piP ν w act i₀) t (Y (ν i) (ν i₀)))
    (fun t => S0 (piP ν w act i₀) t (Bterm ν w Bad i₀ H i))
    (((Δ - 2 * γ ^ H) / 2 / (Fintype.card E : ℝ) ^ H) ^ (H + 2) / 8) 1 H
    (fun t => S0_nonneg hπ t (Y_nonneg _ _))
    (fun t => (S0_super hπ hYs t).trans (by simp [Y, lik]))
    (fun t => by
      rw [S0_markov, ← S0_lin]
      exact S0_mono hπ t fun h => keyS hC hH i hBad h) T
  simpa using h

/-! ### From the information budget to the log loss -/

omit [DecidableEq A] [Nonempty A] in
lemma S0_zero (π : Policy A E) (t : ℕ) : S0 π t (fun _ => 0) = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [S0]
    have e : (fun h : Hist A E => ∑ a, π h a * ∑ _e : E, (0 : ℝ)) = fun _ => 0 := by
      funext h
      simp
    rw [e]
    exact ih

omit [DecidableEq A] [Nonempty A] in
lemma S0_smul (π : Policy A E) (c : ℝ) (t : ℕ) (F : Hist A E → ℝ) :
    S0 π t (fun h => c * F h) = c * S0 π t F := by
  simpa [S0_zero] using S0_lin π c t F (fun _ => 0)

omit [DecidableEq A] [Nonempty A] in
lemma S0_add (π : Policy A E) (t : ℕ) (F G : Hist A E → ℝ) :
    S0 π t (fun h => F h + G h) = S0 π t F + S0 π t G := by
  simpa using S0_lin π 1 t F G

omit [DecidableEq A] [Nonempty A] in
lemma S0_sum (π : Policy A E) (t : ℕ) (s : Finset ℕ) (f : ℕ → Hist A E → ℝ) :
    S0 π t (fun h => ∑ i ∈ s, f i h) = ∑ i ∈ s, S0 π t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [S0_zero]
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [S0_add, ih]

lemma OptClass.card_pos (hC : OptClass r γ ν w act i₀) : 0 < Fintype.card E := by
  rw [Fintype.card_pos_iff]
  by_contra hne
  rw [not_nonempty_iff] at hne
  have := hC.truth_meas [] (Classical.arbitrary A)
  simp at this

omit [Fintype A] [Fintype E] [DecidableEq A] [Nonempty A] in
lemma indI_nonneg (Bad : ℕ → Hist A E → Prop) (i : ℕ) (h : Hist A E) : 0 ≤ indI Bad i h := by
  unfold indI
  split_ifs <;> norm_num

/-- Step 5 of the draft, pointwise: the truth-weighted posterior mass of a disagreeing rival is
at most a threshold term, a small-posterior-of-the-truth term, and a multiple of the summand of
(★). -/
lemma eI_le (hC : OptClass r γ ν w act i₀) (H i : ℕ) (hwi : 0 < w i) {θ δ : ℝ} (hθ : 0 < θ)
    (hδ : 0 < δ) (h : Hist A E) :
    lik (ν i₀) h * (post ν w i h * indI Bad i h) ≤
      θ * lik (ν i₀) h + ((δ / w i₀) * xi ν w h +
        (1 / (Real.sqrt (w i₀ * θ / w i) * min θ δ ^ H)) * Bterm ν w Bad i₀ H i h) := by
  have hw0 := hC.truth_pos
  have hL := lik_nonneg (hC.semi i₀) h
  have hξ := xi_nonneg hC.semi hC.w_nonneg h
  have hB := Bterm_nonneg (Bad := Bad) hC H i h
  have hu1 := post_le_one hC i h
  have hs : 0 < Real.sqrt (w i₀ * θ / w i) := Real.sqrt_pos.2 (div_pos (mul_pos hw0 hθ) hwi)
  have hmin : 0 < min θ δ := lt_min hθ hδ
  have hK : 0 < Real.sqrt (w i₀ * θ / w i) * min θ δ ^ H := mul_pos hs (pow_pos hmin H)
  have ht1 : 0 ≤ θ * lik (ν i₀) h := mul_nonneg hθ.le hL
  have ht2 : 0 ≤ δ / w i₀ * xi ν w h := mul_nonneg (div_nonneg hδ.le hw0.le) hξ
  have ht3 : 0 ≤ 1 / (Real.sqrt (w i₀ * θ / w i) * min θ δ ^ H) * Bterm ν w Bad i₀ H i h :=
    mul_nonneg (one_div_nonneg.2 hK.le) hB
  by_cases hdis : Bad i h
  swap
  · have e : indI Bad i h = 0 := by simp [indI, hdis]
    rw [e, mul_zero, mul_zero]
    linarith
  have hd1 : indI Bad i h = 1 := by simp [indI, hdis]
  rw [hd1, mul_one]
  have hLu : lik (ν i₀) h * post ν w i h ≤ lik (ν i₀) h := mul_le_of_le_one_right hL hu1
  by_cases hu : post ν w i h < θ
  · have := mul_le_mul_of_nonneg_left hu.le hL
    linarith
  by_cases hv : w i₀ * lik (ν i₀) h < δ * xi ν w h
  · have : lik (ν i₀) h ≤ δ / w i₀ * xi ν w h := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hw0]
      linarith
    linarith
  have hu' := not_lt.1 hu
  have hv' := not_lt.1 hv
  have hξpos : 0 < xi ν w h := by
    rcases hξ.eq_or_lt with h0 | h0
    · exfalso
      have : post ν w i h = 0 := by simp [post, ← h0]
      linarith
    · exact h0
  have hwL : θ * xi ν w h ≤ w i * lik (ν i) h := by
    have := hu'
    unfold post at this
    rwa [le_div_iff₀ hξpos] at this
  have hvδ : δ ≤ post ν w i₀ h := by
    unfold post
    rw [le_div_iff₀ hξpos]
    exact hv'
  have hmH : min θ δ ^ H ≤ min (post ν w i h) (post ν w i₀ h) ^ H :=
    pow_le_pow_left₀ hmin.le (min_le_min hu' hvδ) H
  have hξge := le_xi hC.semi hC.w_nonneg hC.w_summable i₀ h
  have hY : lik (ν i₀) h * Real.sqrt (w i₀ * θ / w i) ≤ Y (ν i) (ν i₀) h := by
    rw [← Real.sqrt_sq (mul_nonneg hL hs.le)]
    unfold Y
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg hw0.le hθ.le) hwi.le)]
    have h1 : lik (ν i₀) h * (w i₀ * θ) ≤ lik (ν i) h * w i := by
      have := mul_le_mul_of_nonneg_left hξge hθ.le
      linarith
    have h2 : lik (ν i₀) h * (w i₀ * θ / w i) ≤ lik (ν i) h := by
      rw [← mul_div_assoc, div_le_iff₀ hwi]
      exact h1
    have := mul_le_mul_of_nonneg_left h2 hL
    nlinarith
  have hBge : lik (ν i₀) h * (Real.sqrt (w i₀ * θ / w i) * min θ δ ^ H) ≤
      Bterm ν w Bad i₀ H i h := by
    unfold Bterm
    rw [hd1, mul_one, ← mul_assoc]
    exact mul_le_mul hY hmH (pow_nonneg hmin.le H) (Y_nonneg _ _ _)
  have : lik (ν i₀) h ≤
      1 / (Real.sqrt (w i₀ * θ / w i) * min θ δ ^ H) * Bterm ν w Bad i₀ H i h := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hK]
    exact hBge
  linarith

lemma OptClass.S0_lik (hC : OptClass r γ ν w act i₀) (t : ℕ) :
    S0 (piP ν w act i₀) t (lik (ν i₀)) = 1 := by
  have := S0_harm hC.piP_isPolicy (F := lik (ν i₀)) (fun h a => by
    simp only [lik]; rw [← Finset.mul_sum, hC.truth_meas, mul_one]) t
  simpa [lik] using this

lemma OptClass.S0_xi (hC : OptClass r γ ν w act i₀) (t : ℕ) :
    S0 (piP ν w act i₀) t (xi ν w) ≤ 1 :=
  ((S0_super hC.piP_isPolicy (xi_super hC.semi hC.w_nonneg hC.w_summable) t).trans_eq
    xi_nil).trans hC.w_le

/-- Step 5 of the draft: the expected posterior mass of a rival, at the times it disagrees with
the truth about the optimal action, tends to zero. -/
lemma tendsto_eI (hC : OptClass r γ ν w act i₀) (hΔ : 0 < Δ) (i : ℕ) (hwi : 0 < w i)
    (hBad : ∀ h, lik (ν i₀) h ≠ 0 → Bad i h →
      Qstar r γ (ν i₀) h (act i h) + Δ ≤ Qstar r γ (ν i₀) h (act i₀ h)) :
    Filter.Tendsto (fun t => S0 (piP ν w act i₀) t
      (fun h => lik (ν i₀) h * (post ν w i h * indI Bad i h))) Filter.atTop (nhds 0) := by
  have hπ := hC.piP_isPolicy
  have hw0 := hC.truth_pos
  obtain ⟨H, hH'⟩ := exists_pow_lt_of_lt_one (half_pos hΔ) hC.disc.γ_lt
  have hH : 2 * γ ^ H < Δ := by linarith
  have hM : (0 : ℝ) < (Fintype.card E : ℝ) ^ H := by
    have : (0 : ℝ) < Fintype.card E := by exact_mod_cast hC.card_pos
    exact pow_pos this H
  have hκ : 0 < ((Δ - 2 * γ ^ H) / 2 / (Fintype.card E : ℝ) ^ H) ^ (H + 2) / 8 :=
    div_pos (pow_pos (div_pos (by linarith) hM) _) (by norm_num)
  have hsum : Summable fun t => S0 (piP ν w act i₀) t (Bterm ν w Bad i₀ H i) :=
    summable_of_sum_range_le (fun t => S0_nonneg hπ t (Bterm_nonneg hC H i))
      (c := H / (((Δ - 2 * γ ^ H) / 2 / (Fintype.card E : ℝ) ^ H) ^ (H + 2) / 8))
      (fun T => by
        rw [le_div_iff₀ hκ, mul_comm]
        exact sum_Bterm_le hC hH i hBad T)
  have hnn : ∀ t, 0 ≤ S0 (piP ν w act i₀) t
      (fun h => lik (ν i₀) h * (post ν w i h * indI Bad i h)) := fun t =>
    S0_nonneg hπ t fun h => mul_nonneg (lik_nonneg (hC.semi i₀) h)
      (mul_nonneg (post_nonneg hC i h) (indI_nonneg Bad i h))
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun t =>
    lt_of_lt_of_le ha (hnn t), fun η hη => ?_⟩
  have hθ : 0 < η / 3 := by linarith
  have hδ : 0 < w i₀ * η / 3 := by positivity
  have hb := hsum.tendsto_atTop_zero.const_mul
    (1 / (Real.sqrt (w i₀ * (η / 3) / w i) * min (η / 3) (w i₀ * η / 3) ^ H))
  rw [mul_zero] at hb
  filter_upwards [hb.eventually (gt_mem_nhds hθ)] with t ht
  have h1 := S0_mono hπ t (eI_le (Bad := Bad) hC H i hwi hθ hδ)
  rw [S0_lin, S0_lin, S0_smul, hC.S0_lik] at h1
  have h2 := hC.S0_xi t
  have h3 : w i₀ * η / 3 / w i₀ = η / 3 := by field_simp
  rw [h3] at h1
  have h4 : η / 3 * S0 (piP ν w act i₀) t (xi ν w) ≤ η / 3 * 1 :=
    mul_le_mul_of_nonneg_left h2 hθ.le
  linarith

omit [Fintype A] [Fintype E] [DecidableEq A] [Nonempty A] in
lemma neg_log_le_two_div_sqrt {v : ℝ} (hv : 0 < v) : -log v ≤ 2 / Real.sqrt v := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
  rw [Real.log_inv, Real.log_sqrt hv.le] at h1
  have h2 : 2 / Real.sqrt v = 2 * (Real.sqrt v)⁻¹ := div_eq_mul_inv _ _
  have h3 := inv_pos.2 hs
  linarith

omit [Fintype A] [Fintype E] [DecidableEq A] [Nonempty A] in
lemma neg_log_le_div {δ P : ℝ} (hδ : 0 < δ) (hδP : δ ≤ P) (hP1 : P ≤ 1) :
    -log P ≤ (1 - P) / δ := by
  have hP : 0 < P := lt_of_lt_of_le hδ hδP
  have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hP)
  rw [Real.log_inv] at h1
  have h2 : P⁻¹ - 1 = (1 - P) / P := by field_simp
  have h3 : (1 - P) / P ≤ (1 - P) / δ :=
    div_le_div_of_nonneg_left (by linarith) hδ hδP
  linarith

/-- Step 6 of the draft, pointwise. -/
lemma loss_pointwise (hC : OptClass r γ ν w act i₀)
    (hBadDis : ∀ i h, act i h ≠ act i₀ h → Bad i h) (F : Finset ℕ) {δ : ℝ} (hδ0 : 0 < δ)
    (h : Hist A E) :
    lik (ν i₀) h * loss ν w act i₀ h ≤
      (1 / δ) * (∑ i ∈ F, lik (ν i₀) h * (post ν w i h * indI Bad i h)) +
        ((1 / δ / w i₀) * xi ν (fun i => if i ∈ F then 0 else w i) h +
          (2 * Real.sqrt δ / w i₀) * xi ν w h) := by
  have hw0 := hC.truth_pos
  have hL := lik_nonneg (hC.semi i₀) h
  have hξ := xi_nonneg hC.semi hC.w_nonneg h
  have hw'0 : ∀ i, 0 ≤ (fun i => if i ∈ F then 0 else w i) i := fun i => by
    by_cases hi : i ∈ F <;> simp [hi, hC.w_nonneg i]
  have hw's : Summable (fun i => if i ∈ F then 0 else w i) :=
    Summable.of_nonneg_of_le hw'0 (fun i => by
      by_cases hi : i ∈ F <;> simp [hi, hC.w_nonneg i]) hC.w_summable
  have hξ' := xi_nonneg (w := fun i => if i ∈ F then 0 else w i) hC.semi hw'0 h
  have hsumnn : 0 ≤ ∑ i ∈ F, lik (ν i₀) h * (post ν w i h * indI Bad i h) :=
    Finset.sum_nonneg fun i _ => mul_nonneg hL
      (mul_nonneg (post_nonneg hC i h) (indI_nonneg Bad i h))
  have ht1 : 0 ≤ 1 / δ * ∑ i ∈ F, lik (ν i₀) h * (post ν w i h * indI Bad i h) :=
    mul_nonneg (one_div_nonneg.2 hδ0.le) hsumnn
  have ht2 : 0 ≤ 1 / δ / w i₀ * xi ν (fun i => if i ∈ F then 0 else w i) h :=
    mul_nonneg (div_nonneg (one_div_nonneg.2 hδ0.le) hw0.le) hξ'
  have ht3 : 0 ≤ 2 * Real.sqrt δ / w i₀ * xi ν w h :=
    mul_nonneg (div_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg δ)) hw0.le) hξ
  rcases hL.eq_or_lt with hL0 | hLpos
  · have e : lik (ν i₀) h * loss ν w act i₀ h = 0 := by rw [← hL0, zero_mul]
    rw [e]
    linarith
  have hξge := le_xi hC.semi hC.w_nonneg hC.w_summable i₀ h
  have hξpos : 0 < xi ν w h := lt_of_lt_of_le (mul_pos hw0 hLpos) hξge
  have hπd : ∀ i, IsPolicy (detPol (act i) : Policy A E) := fun i => detPol_isPolicy (act i)
  -- facts about `P = π_T(a* | h)`
  have hPdef : piT ν w act h (act i₀ h) =
      (∑' i, w i * lik (ν i) h * detPol (act i) h (act i₀ h)) / xi ν w h := rfl
  have hPv : w i₀ * lik (ν i₀) h / xi ν w h ≤ piT ν w act h (act i₀ h) := by
    have h1 : w i₀ * lik (ν i₀) h * detPol (act i₀) h (act i₀ h) / xi ν w h ≤
        piT ν w act h (act i₀ h) :=
      thompson_ge hC.semi hC.w_nonneg hC.w_summable hπd i₀ h (act i₀ h)
    have h2 : detPol (act i₀) h (act i₀ h) = 1 := by simp [detPol]
    rwa [h2, mul_one] at h1
  have hvpos : 0 < w i₀ * lik (ν i₀) h / xi ν w h := div_pos (mul_pos hw0 hLpos) hξpos
  have hPpos : 0 < piT ν w act h (act i₀ h) := lt_of_lt_of_le hvpos hPv
  have hP1 : piT ν w act h (act i₀ h) ≤ 1 := by
    have e : piT ν w act h (act i₀ h) = piP ν w act i₀ h (act i₀ h) := by
      simp [piP, thompsonP, piT, hξpos.ne']
    rw [e]
    exact policy_le_one hC.piP_isPolicy h _
  by_cases hv : δ * xi ν w h ≤ w i₀ * lik (ν i₀) h
  · -- the truth's posterior is at least `δ`
    have hδP : δ ≤ piT ν w act h (act i₀ h) :=
      le_trans ((le_div_iff₀ hξpos).2 hv) hPv
    have hloss : loss ν w act i₀ h ≤ (1 - piT ν w act h (act i₀ h)) / δ :=
      neg_log_le_div hδ0 hδP hP1
    -- `(1 - P) ξ ≤ Σ_F w_i L_i dis_i + ξ'`
    have hsl := summable_lik hC.semi hC.w_nonneg hC.w_summable h
    have hsl' := summable_lik (w := fun i => if i ∈ F then 0 else w i) hC.semi hw'0 hw's h
    have hsF : Summable fun i => if i ∈ F then w i * lik (ν i) h * indI Bad i h else 0 :=
      summable_of_ne_finset_zero (s := F) fun i hi => if_neg hi
    have hFsum : ∑' i, (if i ∈ F then w i * lik (ν i) h * indI Bad i h else 0) =
        ∑ i ∈ F, w i * lik (ν i) h * indI Bad i h := by
      rw [tsum_eq_sum (s := F) fun i hi => if_neg hi]
      exact Finset.sum_congr rfl fun i hi => if_pos hi
    have hnum : xi ν w h - ∑ i ∈ F, w i * lik (ν i) h * indI Bad i h -
        xi ν (fun i => if i ∈ F then 0 else w i) h ≤
        ∑' i, w i * lik (ν i) h * detPol (act i) h (act i₀ h) := by
      rw [← hFsum]
      unfold xi
      rw [← Summable.tsum_sub hsl hsF, ← Summable.tsum_sub (hsl.sub hsF) hsl']
      refine Summable.tsum_le_tsum (fun i => ?_) ((hsl.sub hsF).sub hsl')
        (summable_num hC.semi hC.w_nonneg hC.w_summable hπd h _)
      have hwl : 0 ≤ w i * lik (ν i) h := mul_nonneg (hC.w_nonneg i) (lik_nonneg (hC.semi i) h)
      by_cases hiF : i ∈ F
      · by_cases hdis : act i h ≠ act i₀ h
        · have hne : ¬ act i₀ h = act i h := fun hc => hdis hc.symm
          simp [hiF, indI, hBadDis i h hdis, detPol, hne]
        · have heq : act i h = act i₀ h := not_not.1 hdis
          have hI := indI_nonneg Bad i h
          have hdp : detPol (act i) h (act i₀ h) = 1 := by simp [detPol, heq]
          simp only [hiF, if_true, hdp, mul_one, zero_mul, sub_zero]
          nlinarith [mul_nonneg hwl hI]
      · have h2 : 0 ≤ w i * lik (ν i) h * detPol (act i) h (act i₀ h) :=
          mul_nonneg hwl ((hπd i).nonneg _ _)
        simp only [hiF, if_false, sub_zero]
        linarith
    have hPξ : piT ν w act h (act i₀ h) * xi ν w h =
        ∑' i, w i * lik (ν i) h * detPol (act i) h (act i₀ h) := by
      rw [hPdef, div_mul_cancel₀ _ hξpos.ne']
    -- multiply by `L_μ / ξ`
    have hr0 : 0 ≤ lik (ν i₀) h / xi ν w h := div_nonneg hL hξpos.le
    have hr1 : lik (ν i₀) h / xi ν w h ≤ 1 / w i₀ := by
      rw [div_le_div_iff₀ hξpos hw0]
      linarith
    have hmain : lik (ν i₀) h * (1 - piT ν w act h (act i₀ h)) ≤
        ∑ i ∈ F, lik (ν i₀) h * (post ν w i h * indI Bad i h) +
          1 / w i₀ * xi ν (fun i => if i ∈ F then 0 else w i) h := by
      have e1 : lik (ν i₀) h * (1 - piT ν w act h (act i₀ h)) =
          lik (ν i₀) h / xi ν w h *
            (xi ν w h - piT ν w act h (act i₀ h) * xi ν w h) := by
        field_simp
      have e2 : ∑ i ∈ F, lik (ν i₀) h * (post ν w i h * indI Bad i h) =
          lik (ν i₀) h / xi ν w h * ∑ i ∈ F, w i * lik (ν i) h * indI Bad i h := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold post
        field_simp
      rw [e1, e2]
      have h5 : xi ν w h - piT ν w act h (act i₀ h) * xi ν w h ≤
          ∑ i ∈ F, w i * lik (ν i) h * indI Bad i h +
            xi ν (fun i => if i ∈ F then 0 else w i) h := by
        rw [hPξ]
        linarith
      have h6 := mul_le_mul_of_nonneg_left h5 hr0
      have h7 := mul_le_mul_of_nonneg_right hr1 hξ'
      rw [mul_add] at h6
      linarith
    have h8 : lik (ν i₀) h * loss ν w act i₀ h ≤
        1 / δ * (lik (ν i₀) h * (1 - piT ν w act h (act i₀ h))) := by
      have := mul_le_mul_of_nonneg_left hloss hL
      calc lik (ν i₀) h * loss ν w act i₀ h
          ≤ lik (ν i₀) h * ((1 - piT ν w act h (act i₀ h)) / δ) := this
        _ = 1 / δ * (lik (ν i₀) h * (1 - piT ν w act h (act i₀ h))) := by ring
    have h9 := mul_le_mul_of_nonneg_left hmain (one_div_nonneg.2 hδ0.le)
    have h10 : 1 / δ * (∑ i ∈ F, lik (ν i₀) h * (post ν w i h * indI Bad i h) +
        1 / w i₀ * xi ν (fun i => if i ∈ F then 0 else w i) h) =
        1 / δ * (∑ i ∈ F, lik (ν i₀) h * (post ν w i h * indI Bad i h)) +
          1 / δ / w i₀ * xi ν (fun i => if i ∈ F then 0 else w i) h := by
      ring
    linarith
  · -- the truth's posterior is below `δ`
    have hv' := not_le.1 hv
    have hvδ : w i₀ * lik (ν i₀) h / xi ν w h < δ := (div_lt_iff₀ hξpos).2 hv'
    have hloss : loss ν w act i₀ h ≤ 2 / Real.sqrt (w i₀ * lik (ν i₀) h / xi ν w h) := by
      refine le_trans ?_ (neg_log_le_two_div_sqrt hvpos)
      exact neg_le_neg (Real.log_le_log hvpos hPv)
    have hv2 : 2 * xi ν w h / w i₀ * (w i₀ * lik (ν i₀) h / xi ν w h) =
        2 * lik (ν i₀) h := by
      field_simp
    have hsq : Real.sqrt (w i₀ * lik (ν i₀) h / xi ν w h) ≤ Real.sqrt δ :=
      Real.sqrt_le_sqrt hvδ.le
    have h1 := mul_le_mul_of_nonneg_left hloss hL
    have h2 : lik (ν i₀) h * (2 / Real.sqrt (w i₀ * lik (ν i₀) h / xi ν w h)) =
        2 * xi ν w h / w i₀ * ((w i₀ * lik (ν i₀) h / xi ν w h) /
          Real.sqrt (w i₀ * lik (ν i₀) h / xi ν w h)) := by
      generalize Real.sqrt (w i₀ * lik (ν i₀) h / xi ν w h) = S
      have e : 2 * xi ν w h / w i₀ * (w i₀ * lik (ν i₀) h / xi ν w h / S) =
          (2 * xi ν w h / w i₀ * (w i₀ * lik (ν i₀) h / xi ν w h)) / S := by ring
      rw [e, hv2]
      ring
    rw [h2, Real.div_sqrt] at h1
    have h3 := mul_le_mul_of_nonneg_left hsq
      (div_nonneg (mul_nonneg zero_le_two hξpos.le) hw0.le)
    have h4 : 2 * xi ν w h / w i₀ * Real.sqrt δ = 2 * Real.sqrt δ / w i₀ * xi ν w h := by ring
    linarith

/-- [UNAPPROVED STATEMENT] **O2, stochastic: the log loss on the optimal action vanishes in
mean.** Hypotheses (`GapClass`): a countable class of (stochastic) semi-environments over finite
action and percept types, with prior weights `w i ≥ 0`, `Σ w ≤ 1`; rewards in `[0,1]` read off
the percept, geometric discounting with `γ ∈ [0,1)`; member `i`'s designated policy is a
deterministic policy `act i` that is optimal for `ν i` at every history; the truth `ν i₀` is a
measure with `w i₀ > 0` and has a uniform gap `Δ > 0`. Then on per-step Thompson sampling's own
trajectory in the truth,

  `E^{π_T}_μ [ -ln π_T(a*_t | h_{<t}) ] → 0` as `t → ∞`.

No rate is claimed. -/
theorem thompson_O2_stochastic (hC : GapClass r γ ν w act i₀ Δ) (hΔ : 0 < Δ) :
    Filter.Tendsto (fun t => Ex (piT ν w act) (ν i₀) t (loss ν w act i₀)) Filter.atTop
      (nhds 0) := by
  classical
  have hO := hC.toOptClass
  have hπ := hO.piP_isPolicy
  have hw0 := hC.truth_pos
  -- rewrite the expectation as a weighted sum under the completed policy
  have hEx : ∀ t, Ex (piT ν w act) (ν i₀) t (loss ν w act i₀) =
      S0 (piP ν w act i₀) t (fun h => lik (ν i₀) h * loss ν w act i₀ h) := by
    intro t
    rw [← Ex_eq_S0]
    refine Ex_congr_policy (fun h hl a => ?_) t _
    have hξ : xi ν w h ≠ 0 :=
      (lt_of_lt_of_le (mul_pos hw0 ((lik_nonneg (hC.semi i₀) h).lt_of_ne' hl))
        (le_xi hC.semi hC.w_nonneg hC.w_summable i₀ h)).ne'
    simp [piP, thompsonP, piT, hξ]
  simp_rw [hEx]
  have hnn : ∀ t, 0 ≤ S0 (piP ν w act i₀) t (fun h => lik (ν i₀) h * loss ν w act i₀ h) := by
    intro t
    refine S0_nonneg hπ t fun h => ?_
    rcases (lik_nonneg (hC.semi i₀) h).eq_or_lt with hL0 | hLpos
    · rw [← hL0, zero_mul]
    · refine mul_nonneg hLpos.le ?_
      have hξpos : 0 < xi ν w h := lt_of_lt_of_le (mul_pos hw0 hLpos)
        (le_xi hC.semi hC.w_nonneg hC.w_summable i₀ h)
      have e : piT ν w act h (act i₀ h) = piP ν w act i₀ h (act i₀ h) := by
        simp [piP, thompsonP, piT, hξpos.ne']
      have hP1 : piT ν w act h (act i₀ h) ≤ 1 := by
        rw [e]; exact policy_le_one hπ h _
      have hP0 : 0 ≤ piT ν w act h (act i₀ h) := by
        rw [e]; exact hπ.nonneg h _
      exact neg_nonneg.2 (Real.log_nonpos hP0 hP1)
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun t =>
    lt_of_lt_of_le ha (hnn t), fun η hη => ?_⟩
  -- choose `δ`
  set δ : ℝ := min (1 / 2) ((w i₀ * η / 6) ^ 2) with hδdef
  have hq : 0 < w i₀ * η / 6 := by positivity
  have hδ0 : 0 < δ := lt_min (by norm_num) (pow_pos hq 2)
  have hsqδ : Real.sqrt δ ≤ w i₀ * η / 6 := by
    rw [← Real.sqrt_sq hq.le]
    exact Real.sqrt_le_sqrt (min_le_right _ _)
  have hterm3 : 2 * Real.sqrt δ / w i₀ ≤ η / 3 := by
    rw [div_le_iff₀ hw0]
    linarith
  -- choose `F`
  have hε₀ : 0 < δ * w i₀ * (η / 3) := by positivity
  obtain ⟨s, hs⟩ := ((tendsto_tsum_compl_atTop_zero w).eventually (gt_mem_nhds hε₀)).exists
  have hsT : ∑' a : {a // a ∉ s}, w a = tailW w s := by
    rw [show (∑' a : {a // a ∉ s}, w a) = ∑' a : ({a | a ∉ s} : Set ℕ), w a from rfl,
      _root_.tsum_subtype]
    refine tsum_congr fun i => ?_
    by_cases hi : i ∈ s <;> simp [Set.indicator, hi]
  rw [hsT] at hs
  set F : Finset ℕ := s.filter fun i => 0 < w i with hF
  have hFpos : ∀ i ∈ F, 0 < w i := fun i hi => (Finset.mem_filter.1 hi).2
  have hsumm : ∀ G : Finset ℕ, Summable fun i => if i ∈ G then 0 else w i := fun G =>
    Summable.of_nonneg_of_le (fun i => by split_ifs <;> simp [hC.w_nonneg i])
      (fun i => by split_ifs <;> simp [hC.w_nonneg i]) hC.w_summable
  have htF : tailW w F ≤ tailW w s := by
    refine Summable.tsum_le_tsum (fun i => ?_) (hsumm F) (hsumm s)
    by_cases hiF : i ∈ F
    · rw [if_pos hiF]; split_ifs <;> simp [hC.w_nonneg i]
    · rw [if_neg hiF]
      by_cases his : i ∈ s
      · rw [if_pos his]
        by_contra hc
        exact hiF (Finset.mem_filter.2 ⟨his, not_le.1 hc⟩)
      · rw [if_neg his]
  have hterm2 : 1 / δ / w i₀ * tailW w F ≤ η / 3 := by
    rw [div_div, one_div, inv_mul_le_iff₀ (mul_pos hδ0 hw0)]
    linarith
  -- the finitely many rivals in `F`
  have hlim : Filter.Tendsto (fun t => ∑ i ∈ F, S0 (piP ν w act i₀) t
      (fun h => lik (ν i₀) h * (post ν w i h *
        indI (fun i h => act i h ≠ act i₀ h) i h))) Filter.atTop (nhds 0) := by
    have := tendsto_finsetSum F fun i hi =>
      tendsto_eI (Bad := fun i h => act i h ≠ act i₀ h) hO hΔ i (hFpos i hi)
        (fun h hl hb => hC.gap h hl (act i h) hb)
    simpa using this
  have hlim' := hlim.const_mul (1 / δ)
  rw [mul_zero] at hlim'
  filter_upwards [hlim'.eventually (gt_mem_nhds (show 0 < η / 3 by linarith))] with t ht
  have h1 := S0_mono hπ t (loss_pointwise (Bad := fun i h => act i h ≠ act i₀ h) hO
    (fun _ _ hd => hd) F hδ0)
  rw [S0_lin, S0_lin, S0_smul, S0_sum] at h1
  have hw'0 : ∀ i, 0 ≤ (fun i => if i ∈ F then 0 else w i) i := fun i => by
    by_cases hi : i ∈ F <;> simp [hi, hC.w_nonneg i]
  have h2 : S0 (piP ν w act i₀) t (xi ν fun i => if i ∈ F then 0 else w i) ≤ tailW w F :=
    (S0_super hπ (xi_super hC.semi hw'0 (hsumm F)) t).trans_eq xi_nil
  have h3 := hO.S0_xi t
  have h4 := mul_le_mul_of_nonneg_left h2
    (div_nonneg (one_div_nonneg.2 hδ0.le) hw0.le)
  have h5 := mul_le_mul_of_nonneg_left h3
    (div_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg δ)) hw0.le)
  linarith

end StochThompson

end HsiLean.ThompsonO2

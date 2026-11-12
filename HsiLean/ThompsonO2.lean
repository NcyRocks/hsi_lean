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

end Thompson

end HsiLean.ThompsonO2

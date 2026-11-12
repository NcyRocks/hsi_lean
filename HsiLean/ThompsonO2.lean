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

end HsiLean.ThompsonO2

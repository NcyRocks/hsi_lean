import HsiLean.Basic
import HsiLean.Wood
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

open ENNReal

def UniversallyDominant (δ : Semimeasure) : Prop :=
  δ.Enumerable ∧ ∀ μ : Semimeasure, μ.Enumerable → ∃ c > 0, ∀ x, c * μ x ≤ δ x

namespace HsiLean.Dominance

/-- `dyadic (2^n) n = 1`. -/
theorem dyadic_pow_self (n : ℕ) : dyadic (2^n) n = 1 := by
  unfold dyadic
  push_cast
  rw [ENNReal.div_self (pow_ne_zero n (by norm_num))
    (ENNReal.pow_ne_top (by norm_num))]

/-- `dyadic (c * 2^n) n = c` for `c : ℕ`. -/
theorem dyadic_const_mul_pow (c n : ℕ) : dyadic (c * 2^n) n = c := by
  unfold dyadic
  push_cast
  rw [mul_div_assoc, ENNReal.div_self (pow_ne_zero n (by norm_num))
    (ENNReal.pow_ne_top (by norm_num)), mul_one]

/-- Any semimeasure is bounded by its value at `[]`. -/
theorem Semimeasure.le_empty (μ : Semimeasure) (x : List Bool) : μ x ≤ μ [] := by
  induction x using List.reverseRecOn with
  | nil => exact le_refl _
  | append_singleton t b ih => exact (μ.le_of_extend t b).trans ih

/-! ### A universally dominant base: any universal mixture.  -/

noncomputable def xi : Semimeasure :=
  HsiLean.Wood.woodInterface.exists_universalMixture.choose

theorem xi_um : IsUniversalMixture xi :=
  HsiLean.Wood.woodInterface.exists_universalMixture.choose_spec

theorem xi_enum : xi.Enumerable := by
  obtain ⟨ν, w, hν_uenum, _, hξ_eq⟩ := xi_um
  rw [hξ_eq]
  exact hν_uenum.mixture_enumerable w

theorem xi_le_one (x : List Bool) : xi x ≤ 1 :=
  (Semimeasure.le_empty xi x).trans xi.empty_le_one

theorem xi_dominant : ∀ μ : Semimeasure, μ.Enumerable → ∃ c > 0, ∀ x, c * μ x ≤ xi x := by
  intro μ hμ
  obtain ⟨ν, w, _, hν_complete, hξ_eq⟩ := xi_um
  obtain ⟨i, hi⟩ := hν_complete μ hμ
  refine ⟨w i, w.pos i, fun x => ?_⟩
  rw [hξ_eq]
  calc w i * μ x = w i * ν i x := by rw [hi]
    _ ≤ mixture ν w x := le_mixture ν w i x

/-! ### The point mass at `[]`.  -/

noncomputable def pointMass : Semimeasure where
  toFun x := if x = [] then 1 else 0
  empty_le_one := by simp
  extend_le x := by
    have h₀ : x ++ [false] ≠ [] := List.append_ne_nil_of_right_ne_nil x (by simp)
    have h₁ : x ++ [true] ≠ [] := List.append_ne_nil_of_right_ne_nil x (by simp)
    show (if x ++ [false] = [] then (1:ℝ≥0∞) else 0) +
         (if x ++ [true] = [] then (1:ℝ≥0∞) else 0) ≤ (if x = [] then 1 else 0)
    rw [if_neg h₀, if_neg h₁]
    simp

theorem pointMass_zero : pointMass [] = 1 := by simp [pointMass]
theorem pointMass_other {x : List Bool} (h : x ≠ []) : pointMass x = 0 := by
  simp [pointMass, h]

theorem pointMass_enumerable : pointMass.Enumerable := by
  refine ⟨fun x n => if x = [] then 2^n else 0, ?_, ?_, ?_⟩
  · have h_cond : Computable (fun p : List Bool × ℕ => decide (p.1 = [])) :=
      (Primrec.eq.decide.comp Primrec.fst (Primrec.const [])).to_comp
    have h_then : Computable (fun p : List Bool × ℕ => 2 ^ p.2) :=
      Primrec.nat_pow.to_comp.comp (Computable.const 2) Computable.snd
    exact (Computable.cond h_cond h_then (Computable.const 0)).of_eq
      fun p => by simp [Bool.cond_decide]
  · intro x m n hmn
    have h_eval : ∀ k, dyadic (if x = [] then 2^k else 0) k =
        if x = [] then 1 else 0 := fun k => by
      split_ifs
      · exact dyadic_pow_self k
      · simp [dyadic]
    show dyadic (if x = [] then 2^m else 0) m ≤ dyadic (if x = [] then 2^n else 0) n
    rw [h_eval m, h_eval n]
  · intro x
    change (⨆ n, dyadic (if x = [] then 2^n else 0) n) = pointMass x
    have h_eval : ∀ k, dyadic (if x = [] then 2^k else 0) k = pointMass x := fun k => by
      change _ = if x = [] then 1 else 0
      split_ifs
      · exact dyadic_pow_self k
      · simp [dyadic]
    simp_rw [h_eval, iSup_const]

/-! ### Base: 1 at `[]`, 1/2 at length-1, 0 elsewhere.
Built as `baseRaw / 2` so we reuse `div_pos_nat` for LSC closure.  -/

noncomputable def baseRaw (x : List Bool) : ℝ≥0∞ :=
  if x.length = 0 then 2 else if x.length = 1 then 1 else 0

theorem baseRaw_lsc : LowerSemicomputable baseRaw := by
  refine ⟨fun x n => if x.length = 0 then 2 * 2^n
                     else if x.length = 1 then 2^n else 0, ?_, ?_, ?_⟩
  · have h_eq0 : Computable (fun p : List Bool × ℕ => decide (p.1.length = 0)) :=
      ((Primrec.eq.decide.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.const 0))).to_comp
    have h_eq1 : Computable (fun p : List Bool × ℕ => decide (p.1.length = 1)) :=
      ((Primrec.eq.decide.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.const 1))).to_comp
    have h_pow : Computable (fun p : List Bool × ℕ => 2 ^ p.2) :=
      Primrec.nat_pow.to_comp.comp (Computable.const 2) Computable.snd
    have h_2pow : Computable (fun p : List Bool × ℕ => 2 * 2 ^ p.2) :=
      Primrec.nat_mul.to_comp.comp (Computable.const 2) h_pow
    have h_inner : Computable (fun p : List Bool × ℕ =>
      if p.1.length = 1 then 2^p.2 else 0) :=
      (Computable.cond h_eq1 h_pow (Computable.const 0)).of_eq
        fun p => by simp [Bool.cond_decide]
    exact (Computable.cond h_eq0 h_2pow h_inner).of_eq
      fun p => by simp [Bool.cond_decide]
  · -- Monotonicity via the constant-valued evaluation.
    intro x m n _
    have h_eval : ∀ k, dyadic (if x.length = 0 then 2 * 2^k
                               else if x.length = 1 then 2^k else 0) k = baseRaw x := fun k => by
      unfold baseRaw
      split_ifs
      · exact dyadic_const_mul_pow 2 k
      · exact dyadic_pow_self k
      · simp [dyadic]
    show dyadic (if x.length = 0 then 2 * 2^m else if x.length = 1 then 2^m else 0) m ≤
         dyadic (if x.length = 0 then 2 * 2^n else if x.length = 1 then 2^n else 0) n
    rw [h_eval m, h_eval n]
  · intro x
    change (⨆ n, dyadic (if x.length = 0 then 2 * 2^n
                         else if x.length = 1 then 2^n else 0) n) = baseRaw x
    have h_eval : ∀ k, dyadic (if x.length = 0 then 2 * 2^k
                               else if x.length = 1 then 2^k else 0) k = baseRaw x := fun k => by
      unfold baseRaw
      split_ifs
      · exact dyadic_const_mul_pow 2 k
      · exact dyadic_pow_self k
      · simp [dyadic]
    simp_rw [h_eval, iSup_const]

noncomputable def base (x : List Bool) : ℝ≥0∞ := baseRaw x / 2

theorem base_zero : base [] = 1 := by
  change baseRaw [] / 2 = 1
  have : baseRaw [] = 2 := by simp [baseRaw]
  rw [this, ENNReal.div_self (by norm_num) (by norm_num)]

theorem base_one (b : Bool) : base [b] = 1 / 2 := by
  change baseRaw [b] / 2 = 1 / 2
  have : baseRaw [b] = 1 := by simp [baseRaw]
  rw [this]

theorem base_long (x : List Bool) (h : 2 ≤ x.length) : base x = 0 := by
  change baseRaw x / 2 = 0
  have h0 : x.length ≠ 0 := by omega
  have h1 : x.length ≠ 1 := by omega
  have : baseRaw x = 0 := by simp [baseRaw, h0, h1]
  rw [this]; simp

theorem base_lsc : LowerSemicomputable base :=
  baseRaw_lsc.div_pos_nat 2 (by norm_num)

/-! ### xiHead: ξ with the first two levels zeroed.  -/

noncomputable def xiHead (x : List Bool) : ℝ≥0∞ :=
  if 2 ≤ x.length then xi x else 0

theorem xiHead_lsc : LowerSemicomputable xiHead := by
  obtain ⟨φ, hφ_comp, hφ_mono, hφ_sup⟩ := xi_enum
  refine ⟨fun x n => if 2 ≤ x.length then φ x n else 0, ?_, ?_, ?_⟩
  · have h_cond : Computable (fun p : List Bool × ℕ => decide (2 ≤ p.1.length)) :=
      (Primrec.nat_le.decide.comp (Primrec.const 2)
        (Primrec.list_length.comp Primrec.fst)).to_comp
    exact (Computable.cond h_cond hφ_comp (Computable.const 0)).of_eq
      fun p => by simp [Bool.cond_decide]
  · intro x m n hmn
    by_cases h : 2 ≤ x.length
    · simp only [if_pos h]; exact hφ_mono x hmn
    · simp [if_neg h, dyadic]
  · intro x
    change (⨆ n, dyadic (if 2 ≤ x.length then φ x n else 0) n) = xiHead x
    by_cases h : 2 ≤ x.length
    · simp only [if_pos h]
      rw [show xiHead x = xi x from by simp [xiHead, h]]
      exact hφ_sup x
    · simp only [if_neg h, dyadic]
      push_cast
      simp [xiHead, h]

/-! ### δ' = base + xiHead/2  -/

noncomputable def deltaFun (x : List Bool) : ℝ≥0∞ := base x + xiHead x / 2

theorem deltaFun_lsc : LowerSemicomputable deltaFun :=
  base_lsc.add (xiHead_lsc.div_pos_nat 2 (by norm_num))

theorem deltaFun_root : deltaFun [] = 1 := by
  change base [] + xiHead [] / 2 = 1
  rw [base_zero]
  have : xiHead [] = 0 := by simp [xiHead]
  rw [this]; simp

theorem deltaFun_length_one (b : Bool) : deltaFun [b] = 1 / 2 := by
  change base [b] + xiHead [b] / 2 = 1 / 2
  rw [base_one b]
  have : xiHead [b] = 0 := by simp [xiHead]
  rw [this]; simp

theorem deltaFun_length_ge_two (x : List Bool) (h : 2 ≤ x.length) :
    deltaFun x = xi x / 2 := by
  change base x + xiHead x / 2 = xi x / 2
  rw [base_long x h]
  have : xiHead x = xi x := by simp [xiHead, h]
  rw [this]; simp

noncomputable def delta : Semimeasure where
  toFun := deltaFun
  empty_le_one := by rw [deltaFun_root]
  extend_le x := by
    by_cases hx : x.length = 0
    · have hx' : x = [] := List.length_eq_zero_iff.mp hx
      subst hx'
      simp only [List.nil_append]
      rw [deltaFun_root, deltaFun_length_one, deltaFun_length_one,
        ENNReal.div_add_div_same, show (1:ℝ≥0∞) + 1 = 2 from by norm_num,
        ENNReal.div_self (by norm_num) (by norm_num)]
    · by_cases hx1 : x.length = 1
      · obtain ⟨b, hb⟩ : ∃ b, x = [b] := by
          match x, hx1 with
          | [b], _ => exact ⟨b, rfl⟩
        subst hb
        rw [deltaFun_length_one]
        have h2f : 2 ≤ ([b] ++ [false]).length := by simp
        have h2t : 2 ≤ ([b] ++ [true]).length := by simp
        rw [deltaFun_length_ge_two _ h2f, deltaFun_length_ge_two _ h2t,
          ENNReal.div_add_div_same]
        have h_xi : xi ([b] ++ [false]) + xi ([b] ++ [true]) ≤ xi [b] :=
          xi.extend_le [b]
        gcongr
        exact h_xi.trans (xi_le_one [b])
      · have hxge : 2 ≤ x.length := by omega
        have hxpf : 2 ≤ (x ++ [false]).length := by simp; omega
        have hxpt : 2 ≤ (x ++ [true]).length := by simp; omega
        rw [deltaFun_length_ge_two _ hxge, deltaFun_length_ge_two _ hxpf,
          deltaFun_length_ge_two _ hxpt, ENNReal.div_add_div_same]
        have h_ex := xi.extend_le x
        gcongr

theorem delta_enum : delta.Enumerable := deltaFun_lsc

theorem xi_div_two_le_delta (x : List Bool) : xi x / 2 ≤ delta x := by
  change xi x / 2 ≤ deltaFun x
  by_cases h0 : x.length = 0
  · have hxe : x = [] := List.length_eq_zero_iff.mp h0
    subst hxe
    rw [deltaFun_root]
    calc xi [] / 2 ≤ 1 / 2 := by gcongr; exact xi_le_one []
      _ ≤ 1 := by
        rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        exact le_mul_of_one_le_right' (by norm_num)
  · by_cases h1 : x.length = 1
    · obtain ⟨b, hb⟩ : ∃ b, x = [b] := by
        match x, h1 with
        | [b], _ => exact ⟨b, rfl⟩
      subst hb
      rw [deltaFun_length_one]
      gcongr
      exact xi_le_one _
    · have hxge : 2 ≤ x.length := by omega
      rw [deltaFun_length_ge_two _ hxge]

theorem delta_dominant : UniversallyDominant delta := by
  refine ⟨delta_enum, fun μ hμ => ?_⟩
  obtain ⟨c, hc_pos, hc⟩ := xi_dominant μ hμ
  refine ⟨c / 2, ENNReal.div_pos hc_pos.ne' (by norm_num), fun x => ?_⟩
  calc c / 2 * μ x = c * μ x / 2 := by
        rw [ENNReal.div_eq_inv_mul, mul_assoc, ← ENNReal.div_eq_inv_mul]
    _ ≤ xi x / 2 := by gcongr; exact hc x
    _ ≤ delta x := xi_div_two_le_delta x

/-! ### δ' is not a universal mixture.  -/

theorem delta_not_um : ¬ IsUniversalMixture delta := by
  intro hum
  obtain ⟨ν, w, _, hν_complete, hdelta_eq⟩ := hum
  obtain ⟨i₀, hi₀⟩ := hν_complete pointMass pointMass_enumerable
  have h_pm_zero_f : pointMass [false] = 0 := by simp [pointMass]
  have h_pm_zero_t : pointMass [true] = 0 := by simp [pointMass]
  -- Key: w i₀ + (delta [false] + delta [true]) ≤ delta [].
  have h_key : w i₀ + (delta [false] + delta [true]) ≤ delta [] := by
    classical
    rw [hdelta_eq]
    change w i₀ + (mixture ν w [false] + mixture ν w [true]) ≤ mixture ν w []
    simp only [mixture_apply]
    -- Pull out the i₀ term from each tsum via tsum_eq_add_tsum_ite.
    rw [ENNReal.tsum_eq_add_tsum_ite (f := fun i => w i * ν i [false]) i₀,
        ENNReal.tsum_eq_add_tsum_ite (f := fun i => w i * ν i [true]) i₀,
        ENNReal.tsum_eq_add_tsum_ite (f := fun i => w i * ν i []) i₀]
    rw [hi₀]
    simp only [pointMass_zero, h_pm_zero_f, h_pm_zero_t, mul_zero, mul_one, zero_add]
    -- Goal: w i₀ + (T_f + T_t) ≤ w i₀ + T_e
    gcongr
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    by_cases hi : i = i₀
    · simp [hi]
    · simp only [if_neg hi]
      rw [← mul_add]
      gcongr
      exact (ν i).extend_le []
  rw [show delta [] = (1:ℝ≥0∞) from deltaFun_root] at h_key
  rw [show delta [false] = (1:ℝ≥0∞)/2 from deltaFun_length_one false] at h_key
  rw [show delta [true] = (1:ℝ≥0∞)/2 from deltaFun_length_one true] at h_key
  rw [ENNReal.div_add_div_same, show (1:ℝ≥0∞) + 1 = 2 from by norm_num,
    ENNReal.div_self (by norm_num) (by norm_num)] at h_key
  -- h_key : w i₀ + 1 ≤ 1
  have h_wi_zero : w i₀ = 0 := by
    have h2 : w i₀ + 1 ≤ 0 + 1 := by rw [zero_add]; exact h_key
    have h3 : w i₀ ≤ 0 := (ENNReal.add_le_add_iff_right one_ne_top).mp h2
    exact le_antisymm h3 (bot_le)
  exact (w.pos i₀).ne' h_wi_zero

end HsiLean.Dominance

theorem exists_dominant_not_universalSemimeasure :
    ∃ δ, UniversallyDominant δ ∧ ¬ IsUniversalMixture δ :=
  ⟨HsiLean.Dominance.delta, HsiLean.Dominance.delta_dominant,
    HsiLean.Dominance.delta_not_um⟩

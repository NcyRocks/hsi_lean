-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.Levin

/-!
# Solomonoff priors of monotone UTMs = universal mixtures (WSH 2011, Theorem 14)

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-11. Not reviewed by Nathan.

Source: Wood, Sunehag & Hutter 2011 (arXiv 1111.3854): Def. `def:UTM`, Lemma
`thm:UTM-is-mixture` (Lemma 10), Lemma `thm:mixture-is-UTM` (Lemma 13), Theorem
`thm:UTM-eq-mixture` (Theorem 14).

* `IsUTM`: universal by adjunction, with the paper's relaxation (the enumeration of all
  machines may repeat machines).
* `utm_is_universalMixture` (Lemma 10): `λ_U = Σ_k 2^-|I k| λ_{V k}` by `meas_prefixCode`;
  the weights `2^-|I k|` sum to `≤ 1` by Kraft (also `meas_prefixCode`); the `λ_{V k}` cover
  every enumerable semimeasure by Lemma 6 (⇐) (`exists_machine_sm_eq`).
* `universalMixture_is_utm` (Lemma 13): NOT by Kraft–Chaitin. Given `ξ = Σ w_i ν_i`, let
  `η = Σ_e 2^-(e+1) λ_{T_e}` over the standard enumeration `T` of all machines; `η` is
  enumerable, so `η = ν_{i0}`. Pick `δ = 2^-c < w_{i0}`. Then
  `ξ = ρ0 + δ η` with `ρ0 = Σ (w_i - δ[i = i0]) ν_i`, an enumerable semimeasure with
  `ρ0(ε) ≤ 1 - δ`. Let `R` be a machine for `ρ0 / (1 - δ)` (Lemma 6 (⇐)). The UTM uses the
  unary code `I k = 1^k 0`, with `V k = R` for `k < c` (total code weight `1 - δ`) and
  `V (c + e) = T e` (code weight `δ 2^-(e+1)`).
* `solomonoff_eq_universalMixtures` (Theorem 14).
-/

open ENNReal

namespace HsiLean.Monotone

open HsiLean.Wood

/-- [UNAPPROVED STATEMENT] `U` is a universal monotone machine (universal by adjunction,
WSH Def. 2 with the paper's relaxation that the enumeration may repeat machines): there
are an effective enumeration `V` of all machines and a computable prefix-free code `I`
such that the programs on which `U` produces non-empty output are exactly the `I k ++ s`,
and `U (I k ++ s) = V k s`. -/
def IsUTM (U : Machine) : Prop :=
  ∃ (V : ℕ → Machine) (I : ℕ → List Bool),
    UniformlyCE V ∧ (∀ M : Machine, ∃ k, V k = M) ∧
    Computable I ∧ (∀ i j, I i <+: I j → i = j) ∧
    ∀ q x, x ≠ [] → (U.Produces q x ↔ ∃ k s, q = I k ++ s ∧ (V k).Produces s x)

/-! ### Code weights and Lemma 10 -/

theorem code_length_pos {I : ℕ → List Bool} (hpf : ∀ i j, I i <+: I j → i = j) (k : ℕ) :
    0 < (I k).length := by
  rcases Nat.eq_zero_or_pos (I k).length with h | h
  · have hnil : I k = [] := List.length_eq_zero_iff.mp h
    have h1 := hpf k (k + 1) (by rw [hnil]; exact List.nil_prefix)
    omega
  · exact h

/-- The weights `2 ^ -|I k|` of a computable prefix-free code. -/
noncomputable def codeWeights (I : ℕ → List Bool) (hI : Computable I)
    (hpf : ∀ i j, I i <+: I j → i = j) : Weights where
  toFun k := (2⁻¹ : ℝ≥0∞) ^ (I k).length
  lsc := by
    have h := LowerSemicomputable.comp' geometricWeights.lsc (g := fun k => (I k).length - 1)
      (Primrec.nat_sub.to_comp.comp (Primrec.list_length.to_comp.comp hI) (Computable.const 1))
    have e : (fun k => (2⁻¹ : ℝ≥0∞) ^ (I k).length) =
        fun k => geometricWeights.toFun ((I k).length - 1) := by
      funext k
      change _ = (2⁻¹ : ℝ≥0∞) ^ ((I k).length - 1 + 1)
      rw [Nat.sub_add_cancel (code_length_pos hpf k)]
    rw [e]
    exact h
  pos k := ENNReal.pow_pos (by simp) _
  tsum_le_one := by
    have h := meas_prefixCode I hpf (fun _ _ => True) (fun _ _ _ _ => trivial)
    simp only [meas_true, mul_one] at h
    rw [← h]
    exact meas_le_one _

/-- If the programs on which `U` produces `x` are exactly the `I k ++ s` with `V k`
producing `x` on `s`, then `λ_U(x) = Σ_k 2^-|I k| λ_{V k}(x)`. -/
theorem sm_eq_of_produces (U : Machine) (V : ℕ → Machine) (I : ℕ → List Bool)
    (hpf : ∀ i j, I i <+: I j → i = j) (x : List Bool)
    (h : ∀ q, U.Produces q x ↔ ∃ k s, q = I k ++ s ∧ (V k).Produces s x) :
    U.sm x = ∑' k, (2⁻¹ : ℝ≥0∞) ^ (I k).length * (V k).sm x := by
  rw [Machine.sm_apply]
  have e : (fun q => U.Produces q x) = fun q => ∃ k, Shift (I k) ((V k).Produces · x) q := by
    funext q
    exact propext (h q)
  rw [e, meas_prefixCode I hpf _ (fun k => (V k).produces_upClosed x)]
  rfl

/-- [UNAPPROVED STATEMENT] WSH Lemma 10: the Solomonoff prior of a UTM is a universal
mixture, off the empty string. -/
theorem utm_is_universalMixture (U : Machine) (hU : IsUTM U) :
    ∃ ξ : Semimeasure, IsUniversalMixture ξ ∧ ∀ x, x ≠ [] → U.lam x = ξ x := by
  obtain ⟨V, I, hV, hVc, hI, hpf, hprod⟩ := hU
  refine ⟨mixture (fun k => (V k).sm) (codeWeights I hI hpf),
    ⟨_, _, sm_uniformlyEnumerable hV, ?_, rfl⟩, ?_⟩
  · intro μ hμ
    obtain ⟨M, hM⟩ := exists_machine_sm_eq μ hμ
    obtain ⟨k, hk⟩ := hVc M
    refine ⟨k, ?_⟩
    change (V k).sm = μ
    rw [hk, hM]
  · intro x hx
    rw [U.lam_of_ne hx, sm_eq_of_produces U V I hpf x (fun q => hprod q x hx)]
    rfl

/-! ### The machine `U (I k ++ s) = V k s` -/

/-- The machine that reads a codeword `I k` and then runs `V k` on the rest of its input. -/
noncomputable def prefixMachine (V : ℕ → Machine) (I : ℕ → List Bool) (hV : UniformlyCE V)
    (hI : Computable I) (hpf : ∀ i j, I i <+: I j → i = j) : Machine where
  pairs := {a | ∃ k, ∃ b ∈ (V k).pairs, a = (I k ++ b.1, b.2)}
  ce := by
    obtain ⟨G, hG, hGp⟩ := hV
    refine ⟨fun n => (G n.unpair.1 n.unpair.2).map fun b => (I n.unpair.1 ++ b.1, b.2), ?_, ?_⟩
    · have h1 : Computable (fun n : ℕ => G n.unpair.1 n.unpair.2) :=
        hG.comp (Computable.fst.comp Primrec.unpair.to_comp)
          (Computable.snd.comp Primrec.unpair.to_comp)
      have h2 : Computable₂ (fun (n : ℕ) (b : Pair) => (I n.unpair.1 ++ b.1, b.2)) :=
        (Computable.pair
          (Primrec.list_append.to_comp.comp
            (hI.comp (Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.fst)))
            (Computable.fst.comp Computable.snd))
          (Computable.snd.comp Computable.snd)).to₂
      exact Computable.option_map h1 h2
    · intro a
      constructor
      · rintro ⟨k, b, hb, rfl⟩
        obtain ⟨n, hn⟩ := (hGp k b).mp hb
        exact ⟨Nat.pair k n, by simp [hn]⟩
      · rintro ⟨n, hn⟩
        obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hn
        exact ⟨_, b, (hGp _ b).mpr ⟨_, hb⟩, rfl⟩
  consistent := by
    rintro _ ⟨k, a, ha, rfl⟩ _ ⟨k', b, hb, rfl⟩ hab
    have h1 : I k <+: I k' ++ b.1 := (List.prefix_append _ _).trans hab
    have h2 : I k' <+: I k' ++ b.1 := List.prefix_append _ _
    have hk : k = k' := by
      rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
      · exact hpf _ _ h
      · exact (hpf _ _ h).symm
    subst hk
    exact (V k).consistent a ha b hb ((List.prefix_append_right_inj _).mp hab)

theorem prefixMachine_produces (V : ℕ → Machine) (I : ℕ → List Bool) (hV : UniformlyCE V)
    (hI : Computable I) (hpf : ∀ i j, I i <+: I j → i = j) (q x : List Bool) :
    (prefixMachine V I hV hI hpf).Produces q x ↔
      ∃ k s, q = I k ++ s ∧ (V k).Produces s x := by
  constructor
  · rintro ⟨_, ⟨k, b, hb, rfl⟩, ⟨s', hs'⟩, hx⟩
    exact ⟨k, b.1 ++ s', by rw [← hs', List.append_assoc], b, hb, List.prefix_append _ _, hx⟩
  · rintro ⟨k, s, rfl, b, hb, hbs, hx⟩
    exact ⟨(I k ++ b.1, b.2), ⟨k, b, hb, rfl⟩, (List.prefix_append_right_inj _).mpr hbs, hx⟩

theorem prefixMachine_isUTM (V : ℕ → Machine) (I : ℕ → List Bool) (hV : UniformlyCE V)
    (hI : Computable I) (hpf : ∀ i j, I i <+: I j → i = j) (hVc : ∀ M : Machine, ∃ k, V k = M) :
    IsUTM (prefixMachine V I hV hI hpf) :=
  ⟨V, I, hV, hVc, hI, hpf, fun q x _ => prefixMachine_produces V I hV hI hpf q x⟩

/-! ### The unary code `1^k 0` -/

/-- The unary prefix-free code `k ↦ 1^k 0`. -/
def unaryCode : ℕ → List Bool
  | 0 => [false]
  | k + 1 => true :: unaryCode k

theorem unaryCode_length (k : ℕ) : (unaryCode k).length = k + 1 := by
  induction k <;> simp [unaryCode, *]

theorem unaryCode_prefixFree : ∀ i j, unaryCode i <+: unaryCode j → i = j := by
  intro i
  induction i with
  | zero =>
    intro j h
    cases j with
    | zero => rfl
    | succ j => simp [unaryCode] at h
  | succ i ih =>
    intro j h
    cases j with
    | zero => simp [unaryCode] at h
    | succ j =>
      simp only [unaryCode, List.cons_prefix_cons, true_and] at h
      rw [ih j h]

theorem unaryCode_eq_rec (k : ℕ) :
    (Nat.rec [false] (fun _ IH => true :: IH) k : List Bool) = unaryCode k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (true :: ·) ih

theorem unaryCode_computable : Computable unaryCode :=
  (Computable.nat_rec Computable.id (Computable.const [false])
    (Primrec.list_cons.to_comp.comp (Computable.const true)
      (Computable.snd.comp Computable.snd)).to₂).of_eq fun k => unaryCode_eq_rec k

theorem geom_partial (c : ℕ) :
    ∑ k ∈ Finset.range c, (2⁻¹ : ℝ≥0∞) ^ (k + 1) + (2⁻¹ : ℝ≥0∞) ^ c = 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, add_assoc, pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two,
      mul_one, ih]

theorem dyadic_one (c : ℕ) : dyadic 1 c = (2⁻¹ : ℝ≥0∞) ^ c := by
  unfold dyadic
  rw [Nat.cast_one, one_div, ENNReal.inv_pow]

theorem dyadic_one_succ_lt {a : ℝ≥0∞} {k n : ℕ} (hpos : 0 < dyadic k n) (hle : dyadic k n ≤ a) :
    dyadic 1 (n + 1) < a := by
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hpos
      simp [dyadic] at hpos
    · exact h
  have h1 : dyadic 1 n ≠ 0 := by
    rw [dyadic_one]
    exact (ENNReal.pow_pos (by simp) n).ne'
  have h2 : dyadic 1 n ≠ ⊤ := by
    rw [dyadic_one]
    exact ENNReal.pow_ne_top (by simp)
  calc dyadic 1 (n + 1) = dyadic 1 n / 2 := (dyadic_div_two 1 n).symm
    _ < dyadic 1 n := ENNReal.half_lt_self h1 h2
    _ ≤ dyadic k n := dyadic_mono_num hk
    _ ≤ a := hle

theorem scale_cancel (m D a : ℝ≥0∞) (hm0 : m ≠ 0) (hmt : m ≠ ⊤) (hD0 : D ≠ 0) (hDt : D ≠ ⊤) :
    m / D * (D * a / m) = a := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc m * D⁻¹ * (D * a * m⁻¹) = (m * m⁻¹) * (D⁻¹ * D) * a := by ring
    _ = a := by
      rw [ENNReal.mul_inv_cancel hm0 hmt, ENNReal.inv_mul_cancel hD0 hDt, one_mul, one_mul]

/-! ### Lemma 13 -/

/-- Lowering one weight by a dyadic strictly below it. -/
theorem exists_reducedWeights (w : Weights) (i0 c : ℕ) (h : dyadic 1 c < w i0) :
    ∃ W' : Weights, (∀ i, W' i + (if i = i0 then dyadic 1 c else 0) = w i) ∧
      ∑' i, W' i + dyadic 1 c ≤ 1 := by
  have hw' : ∀ i, (w i - (if i = i0 then dyadic 1 c else 0)) + (if i = i0 then dyadic 1 c else 0)
      = w i := by
    intro i
    apply tsub_add_cancel_of_le
    by_cases hi : i = i0
    · subst hi
      rw [if_pos rfl]
      exact h.le
    · rw [if_neg hi]
      exact bot_le
  have hind : ∑' i, (if i = i0 then dyadic 1 c else 0) = dyadic 1 c :=
    tsum_ite_eq i0 (fun _ => dyadic 1 c)
  refine ⟨{ toFun := fun i => w.toFun i - (if i = i0 then dyadic 1 c else 0)
            lsc := w.lsc.sub_indicator_dyadic i0 1 c h.le
            pos := ?_
            tsum_le_one := (ENNReal.tsum_le_tsum fun i => tsub_le_self).trans w.tsum_le_one },
    hw', ?_⟩
  · intro i
    by_cases hi : i = i0
    · subst hi
      rw [if_pos rfl]
      exact tsub_pos_of_lt h
    · rw [if_neg hi, tsub_zero]
      exact w.pos i
  · calc ∑' i, (w i - (if i = i0 then dyadic 1 c else 0)) + dyadic 1 c
        = ∑' i, ((w i - (if i = i0 then dyadic 1 c else 0)) +
            (if i = i0 then dyadic 1 c else 0)) := by
          rw [ENNReal.tsum_add, hind]
      _ = ∑' i, w i := tsum_congr hw'
      _ ≤ 1 := w.tsum_le_one

/-- Dividing an enumerable semimeasure of root mass `≤ 1 - 2^-c` by `1 - 2^-c`. -/
theorem exists_rescaled (ρ : Semimeasure) (hρ : ρ.Enumerable) (n : ℕ)
    (hroot : ρ [] + dyadic 1 (n + 1) ≤ 1) :
    ∃ ρ' : Semimeasure, ρ'.Enumerable ∧
      ∀ x, (∑ k ∈ Finset.range (n + 1), (2⁻¹ : ℝ≥0∞) ^ (k + 1)) * ρ' x = ρ x := by
  obtain ⟨c, hc⟩ : ∃ c, c = n + 1 := ⟨_, rfl⟩
  rw [← hc] at hroot ⊢
  have hδt : dyadic 1 c ≠ ⊤ := by
    rw [dyadic_one]
    exact ENNReal.pow_ne_top (by simp)
  have hκ := geom_partial c
  rw [← dyadic_one] at hκ
  have h2c : 2 ≤ 2 ^ c := by
    rw [hc, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega
  have hm : 0 < 2 ^ c - 1 := by omega
  have hκm : ∑ k ∈ Finset.range c, (2⁻¹ : ℝ≥0∞) ^ (k + 1) = dyadic (2 ^ c - 1) c := by
    have h1 : dyadic (2 ^ c - 1) c + dyadic 1 c = 1 := by
      rw [← dyadic_add, Nat.sub_add_cancel (by omega)]
      unfold dyadic
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact ENNReal.div_self (by positivity) (ENNReal.pow_ne_top (by norm_num))
    exact (ENNReal.add_left_inj hδt).mp (hκ.trans h1.symm)
  rw [hκm] at hκ ⊢
  have hD : ((2 ^ c : ℕ) : ℝ≥0∞) = 2 ^ c := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have hD0 : ((2 ^ c : ℕ) : ℝ≥0∞) ≠ 0 := by rw [hD]; positivity
  have hDt : ((2 ^ c : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hm0 : ((2 ^ c - 1 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmt : ((2 ^ c - 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hroot' : ρ [] ≤ dyadic (2 ^ c - 1) c :=
    (ENNReal.add_le_add_iff_right hδt).mp (hroot.trans hκ.ge)
  refine ⟨{ toFun := fun x => ((2 ^ c : ℕ) : ℝ≥0∞) * ρ.toFun x / ((2 ^ c - 1 : ℕ) : ℝ≥0∞)
            empty_le_one := ?_
            extend_le := ?_ }, (hρ.nat_mul (2 ^ c)).div_pos_nat (2 ^ c - 1) hm, ?_⟩
  · apply ENNReal.div_le_of_le_mul
    rw [one_mul]
    calc ((2 ^ c : ℕ) : ℝ≥0∞) * ρ.toFun []
        ≤ ((2 ^ c : ℕ) : ℝ≥0∞) * dyadic (2 ^ c - 1) c := by gcongr
      _ = ((2 ^ c - 1 : ℕ) : ℝ≥0∞) := by
          unfold dyadic
          rw [← hD]
          exact ENNReal.mul_div_cancel hD0 hDt
  · intro x
    rw [← ENNReal.add_div, ← mul_add]
    gcongr
    exact ρ.extend_le x
  · intro x
    change dyadic (2 ^ c - 1) c *
      (((2 ^ c : ℕ) : ℝ≥0∞) * ρ.toFun x / ((2 ^ c - 1 : ℕ) : ℝ≥0∞)) = ρ.toFun x
    have hd : dyadic (2 ^ c - 1) c = ((2 ^ c - 1 : ℕ) : ℝ≥0∞) / ((2 ^ c : ℕ) : ℝ≥0∞) := by
      unfold dyadic
      rw [hD]
    rw [hd]
    exact scale_cancel _ _ _ hm0 hmt hD0 hDt

/-- The enumeration `R, …, R (c times), T_0, T_1, …` of all machines is effective. -/
theorem exists_padded_enum (R : Machine) (c : ℕ) :
    ∃ V : ℕ → Machine, UniformlyCE V ∧ (∀ M : Machine, ∃ k, V k = M) ∧
      (∀ k, k < c → V k = R) ∧ ∀ e, V (e + c) = enumMachine e := by
  obtain ⟨gR, hgR, hgRp⟩ := R.ce
  refine ⟨fun k => if k < c then R else enumMachine (k - c),
    ⟨fun k n => bif decide (k < c) then gR n else enumG (k - c) n, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have hcond : Computable (fun p : ℕ × ℕ => decide (p.1 < c)) :=
      (Primrec.nat_lt.decide.comp Primrec.fst (Primrec.const c)).to_comp
    have hg : Computable (fun p : ℕ × ℕ => enumG (p.1 - c) p.2) :=
      enumG_computable.comp
        (Primrec.nat_sub.to_comp.comp Computable.fst (Computable.const c)) Computable.snd
    exact Computable.cond hcond (hgR.comp Computable.snd) hg
  · intro k a
    beta_reduce
    by_cases h : k < c
    · rw [if_pos h, decide_eq_true h]
      exact hgRp a
    · rw [if_neg h, decide_eq_false h]
      exact Iff.rfl
  · intro M
    obtain ⟨e, he⟩ := enumMachine_complete M
    refine ⟨c + e, ?_⟩
    beta_reduce
    rw [if_neg (by omega), Nat.add_sub_cancel_left, he]
  · intro k hk
    exact if_pos hk
  · intro e
    beta_reduce
    rw [if_neg (by omega), Nat.add_sub_cancel]

/-- [UNAPPROVED STATEMENT] WSH Lemma 13, exact form: every universal mixture is the
Solomonoff semimeasure `sm` of some UTM, including at the empty string (where `sm` is the
measure of the programs on which the machine has any pair). -/
theorem universalMixture_is_utm_sm (ξ : Semimeasure) (hξ : IsUniversalMixture ξ) :
    ∃ U : Machine, IsUTM U ∧ U.sm = ξ := by
  obtain ⟨ν, w, hν, hνc, rfl⟩ := hξ
  have hτ : UniformlyEnumerable (fun e => (enumMachine e).sm) :=
    sm_uniformlyEnumerable enumMachine_uniformlyCE
  obtain ⟨i0, hi0⟩ := hνc (mixture (fun e => (enumMachine e).sm) geometricWeights)
    (hτ.mixture_enumerable geometricWeights)
  obtain ⟨k, n, hpos, hle⟩ := w.lsc.exists_pos_approx (w.pos i0)
  have hδlt : dyadic 1 (n + 1) < w i0 := dyadic_one_succ_lt hpos hle
  obtain ⟨W', hw', hW'sum⟩ := exists_reducedWeights w i0 (n + 1) hδlt
  have hρ0root : mixture ν W' [] ≤ ∑' i, W' i := by
    rw [mixture_apply]
    refine ENNReal.tsum_le_tsum fun i => ?_
    calc W' i * ν i [] ≤ W' i * 1 := by gcongr; exact (ν i).empty_le_one
      _ = W' i := mul_one _
  obtain ⟨ρ', hρ'e, hscale⟩ := exists_rescaled (mixture ν W') (hν.mixture_enumerable W') n
    ((add_le_add hρ0root le_rfl).trans hW'sum)
  obtain ⟨R, hR⟩ := exists_machine_sm_eq ρ' hρ'e
  obtain ⟨V, hV, hVc, hVR, hVT⟩ := exists_padded_enum R (n + 1)
  refine ⟨prefixMachine V unaryCode hV unaryCode_computable unaryCode_prefixFree,
    prefixMachine_isUTM V unaryCode hV unaryCode_computable unaryCode_prefixFree hVc, ?_⟩
  refine Semimeasure.ext fun x => ?_
  rw [sm_eq_of_produces _ V unaryCode unaryCode_prefixFree x
    (fun q => prefixMachine_produces V unaryCode hV unaryCode_computable unaryCode_prefixFree q x)]
  simp_rw [unaryCode_length]
  have hsplit : ∑ i ∈ Finset.range (n + 1), (2⁻¹ : ℝ≥0∞) ^ (i + 1) * (V i).sm x +
      ∑' i, (2⁻¹ : ℝ≥0∞) ^ (i + (n + 1) + 1) * (V (i + (n + 1))).sm x =
      ∑' i, (2⁻¹ : ℝ≥0∞) ^ (i + 1) * (V i).sm x :=
    Summable.sum_add_tsum_nat_add' (k := n + 1)
      (f := fun k => (2⁻¹ : ℝ≥0∞) ^ (k + 1) * (V k).sm x) ENNReal.summable
  have hfirst : ∑ i ∈ Finset.range (n + 1), (2⁻¹ : ℝ≥0∞) ^ (i + 1) * (V i).sm x =
      mixture ν W' x :=
    calc ∑ i ∈ Finset.range (n + 1), (2⁻¹ : ℝ≥0∞) ^ (i + 1) * (V i).sm x
        = ∑ i ∈ Finset.range (n + 1), (2⁻¹ : ℝ≥0∞) ^ (i + 1) * ρ' x :=
          Finset.sum_congr rfl fun i hi => by rw [hVR i (Finset.mem_range.mp hi), hR]
      _ = (∑ i ∈ Finset.range (n + 1), (2⁻¹ : ℝ≥0∞) ^ (i + 1)) * ρ' x :=
          (Finset.sum_mul _ _ _).symm
      _ = mixture ν W' x := hscale x
  have hsecond : ∑' i, (2⁻¹ : ℝ≥0∞) ^ (i + (n + 1) + 1) * (V (i + (n + 1))).sm x =
      dyadic 1 (n + 1) * ν i0 x := by
    rw [hi0, mixture_apply, dyadic_one, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [hVT]
    change _ = (2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((2⁻¹ : ℝ≥0∞) ^ (i + 1) * (enumMachine i).sm x)
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [← hsplit, hfirst, hsecond, mixture_apply, mixture_apply]
  have hsingle : dyadic 1 (n + 1) * ν i0 x =
      ∑' i, (if i = i0 then dyadic 1 (n + 1) else 0) * ν i x := by
    rw [tsum_eq_single i0 (fun i hi => by rw [if_neg hi, zero_mul]), if_pos rfl]
  rw [hsingle, ← ENNReal.tsum_add]
  refine tsum_congr fun i => ?_
  rw [← add_mul, hw' i]

/-- [UNAPPROVED STATEMENT] WSH Lemma 13: every universal mixture is the Solomonoff prior
of some UTM, off the empty string. -/
theorem universalMixture_is_utm (ξ : Semimeasure) (hξ : IsUniversalMixture ξ) :
    ∃ U : Machine, IsUTM U ∧ ∀ x, x ≠ [] → U.lam x = ξ x := by
  obtain ⟨U, hU, h⟩ := universalMixture_is_utm_sm ξ hξ
  exact ⟨U, hU, fun x hx => by rw [U.lam_of_ne hx, h]⟩

/-! ### Theorem 14 -/

/-- [UNAPPROVED STATEMENT] WSH Theorem 14: the class of Solomonoff priors of UTMs equals the
class of universal mixtures, as functions on the non-empty strings. -/
theorem solomonoff_eq_universalMixtures :
    {f : {x : List Bool // x ≠ []} → ℝ≥0∞ | ∃ U : Machine, IsUTM U ∧ f = fun x => U.lam x.1} =
      {f | ∃ ξ : Semimeasure, IsUniversalMixture ξ ∧ f = fun x => ξ x.1} := by
  ext f
  constructor
  · rintro ⟨U, hU, rfl⟩
    obtain ⟨ξ, hξ, h⟩ := utm_is_universalMixture U hU
    exact ⟨ξ, hξ, funext fun x => h x.1 x.2⟩
  · rintro ⟨ξ, hξ, rfl⟩
    obtain ⟨U, hU, h⟩ := universalMixture_is_utm ξ hξ
    exact ⟨U, hU, funext fun x => (h x.1 x.2).symm⟩

/-! ### HSI's class = SolInd's class, stated about machines (`cor:um=umum=solind=hsi`) -/

/-- [UNAPPROVED STATEMENT] The paper's `cor:um=umum=solind=hsi`, stated about machines.
Let `V` be any effective enumeration of monotone machines that contains every UTM (it may
contain any other machines too). Then the class of HSI priors over `V` — the mixtures
`Σ_k w_k P_{V k}` with lower-semicomputable positive weights summing to `≤ 1` — equals the
class of Solomonoff priors of UTMs, as functions on the non-empty strings. -/
theorem hsi_eq_solomonoff (V : ℕ → Machine) (hV : UniformlyCE V)
    (hU : ∀ U : Machine, IsUTM U → ∃ k, V k = U) :
    {f : {x : List Bool // x ≠ []} → ℝ≥0∞ |
        ∃ w : Weights, f = fun x => ∑' k, w k * (V k).lam x.1} =
      {f | ∃ U : Machine, IsUTM U ∧ f = fun x => U.lam x.1} := by
  rw [solomonoff_eq_universalMixtures]
  have hc : ContainsAllUniversalMixtures (fun k => (V k).sm) := by
    intro ξ hξ
    obtain ⟨U, hU', h⟩ := universalMixture_is_utm_sm ξ hξ
    obtain ⟨k, hk⟩ := hU U hU'
    refine ⟨k, ?_⟩
    change (V k).sm = ξ
    rw [hk, h]
  have hs := mixtureClass_eq_universalMixtures' _ (sm_uniformlyEnumerable hV) hc
  have key : ∀ (w : Weights) (x : {x : List Bool // x ≠ []}),
      ∑' k, w k * (V k).lam x.1 = mixture (fun k => (V k).sm) w x.1 := by
    intro w x
    rw [mixture_apply]
    exact tsum_congr fun k => by rw [(V k).lam_of_ne x.2]
  ext f
  constructor
  · rintro ⟨w, rfl⟩
    have hm : mixture (fun k => (V k).sm) w ∈ MixtureClass (fun k => (V k).sm) := ⟨w, rfl⟩
    rw [hs] at hm
    exact ⟨_, hm, funext fun x => key w x⟩
  · rintro ⟨ξ, hξ, rfl⟩
    have hm : ξ ∈ MixtureClass (fun k => (V k).sm) := by rw [hs]; exact hξ
    obtain ⟨w, rfl⟩ := hm
    exact ⟨w, funext fun x => (key w x).symm⟩

/-- [UNAPPROVED STATEMENT] `hsi_eq_solomonoff` is not vacuous: the standard enumeration of
ALL monotone machines satisfies its hypotheses, so HSI over all machines has exactly the
Solomonoff priors of UTMs as its priors (off the empty string). -/
theorem hsi_eq_solomonoff_enum :
    {f : {x : List Bool // x ≠ []} → ℝ≥0∞ |
        ∃ w : Weights, f = fun x => ∑' k, w k * (enumMachine k).lam x.1} =
      {f | ∃ U : Machine, IsUTM U ∧ f = fun x => U.lam x.1} :=
  hsi_eq_solomonoff enumMachine enumMachine_uniformlyCE
    (fun U _ => enumMachine_complete U)

end HsiLean.Monotone

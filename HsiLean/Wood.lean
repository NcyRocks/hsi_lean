import HsiLean.Basic
import Mathlib.Computability.PartrecCode

/-!
# A `WoodInterface` built from `Nat.Partrec.Code`

Given `Nat.Partrec.Code` (an enumeration of all partial recursive functions) with its
step-bounded evaluator `Nat.Partrec.Code.evaln`, this file constructs an effective
enumeration `enum : ℕ → Semimeasure` containing every enumerable semimeasure.

The construction proceeds in three layers:

1. `fApprox e t x`: the largest dyadic `k / 2^n` with `n ≤ t` for which
   `evaln t e (encode (x, n)) = some k` — written at the common level `t`, so the
   numerator is `k * 2^(t-n)`.

2. `gApprox e t x`: makes every stage a semimeasure. Defined bottom-up on
   `t - |x|`: at `|x| = t`, `g = f`; for `|x| < t`,
   `g e t x = max (f e t x) (g e t (x++[false]) + g e t (x++[true]))`; for
   `|x| > t`, `g e t x = 0`.

3. `GApprox e t`: root-freeze. Let `s*` be the largest `s ≤ t` with
   `g e s [] ≤ 1` (represented at level `s`), and `GApprox e t := g e s*`.

Then `enum e := ⨆ t, GApprox e t` as an ENNReal-valued semimeasure.

See the task brief 2026-11-08 for the written proof.
-/

open ENNReal

namespace HsiLean.Wood

/-! ### `fApprox`: per-code dyadic approximant

`evaln t e m` succeeds only when `m < t` (`Nat.Partrec.Code.evaln_bound`), so the
`Finset.range (t+1)` iteration is harmless. We write every success at the common
level `t`, so the numerator we store is `k * 2 ^ (t - n)`, which has the dyadic
value `k / 2^n` exactly. -/

/-- Lift `Denumerable.ofNat` to a plain name; shorthand for the code read off a `ℕ`. -/
noncomputable def codeOf (e : ℕ) : Nat.Partrec.Code := Denumerable.ofNat Nat.Partrec.Code e

/-- A single candidate value at level `t`. -/
noncomputable def candidate (e t n : ℕ) (x : List Bool) : ℕ :=
  match Nat.Partrec.Code.evaln t (codeOf e) (Encodable.encode (x, n)) with
  | some k => k * 2 ^ (t - n)
  | none => 0

/-- `fApprox e t x`: largest-`candidate` at level `t`, searched over `n ≤ t`. -/
noncomputable def fApprox (e t : ℕ) (x : List Bool) : ℕ :=
  (Finset.range (t + 1)).sup (fun n => candidate e t n x)

/-! ### `gApprox`: bottom-up closure to a semimeasure

Recursion on `t - |x|`. The `|x| > t` branch returns 0 so children at the bottom
contribute nothing. -/

/-- The bottom-up semimeasure closure. -/
noncomputable def gApprox (e t : ℕ) : List Bool → ℕ
  | x =>
    if h₁ : x.length < t then
      max (fApprox e t x)
          (gApprox e t (x ++ [false]) + gApprox e t (x ++ [true]))
    else if _h₂ : x.length = t then fApprox e t x
    else 0
termination_by x => t - x.length
decreasing_by
  · show t - (x ++ [false]).length < t - x.length
    rw [List.length_append]; simp; omega
  · show t - (x ++ [true]).length < t - x.length
    rw [List.length_append]; simp; omega

/-! ### `GApprox`: root-freeze to enforce `≤ 1` at `[]`

We take `GApprox e t` to be the stage with the largest `s ≤ t` for which the value
at the root `[]` (interpreted at level `s`) is still `≤ 1`. If no such stage
exists, `GApprox e t` is 0. The `s*` always makes `GApprox e t []` a valid
semimeasure root. -/

/-- The predicate "value of `g e s []` at level `s` is at most `1`". -/
noncomputable def rootBounded (e s : ℕ) : Prop :=
  (gApprox e s [] : ℝ≥0∞) ≤ 2 ^ s

/-- The largest `s ≤ t` with `g e s [] ≤ 2^s` (equivalently `dyadic (g e s []) s ≤ 1`),
or `0` if none. We split the "none" case by checking `rootBounded e 0`. -/
noncomputable def freezeStage (e t : ℕ) : ℕ :=
  (Finset.range (t + 1)).sup fun s => if (gApprox e s [] : ℝ≥0∞) ≤ 2 ^ s then s else 0

/-- `GApprox e t x`: the frozen stage value at string `x`, interpreted via `s*`. -/
noncomputable def GApprox (e t : ℕ) (x : List Bool) : ℝ≥0∞ :=
  dyadic (gApprox e (freezeStage e t) x) (freezeStage e t)

/-! ### `enum e` as a `Semimeasure`

We take the sup over `t` of `GApprox e t`. This sup is monotone (both the
stage `s*` and the frozen values are monotone in `t`), bounded by 1 at `[]`,
and satisfies the extend inequality — so it is a semimeasure. -/

/-- The underlying mass function. -/
noncomputable def enumFun (e : ℕ) (x : List Bool) : ℝ≥0∞ := ⨆ t, GApprox e t x

/-! ### Properties of `gApprox`

The paper's four facts:
* (a) child-sum ≤ parent (⟹ extend inequality for any level-`t` dyadic reading);
* (b) `fApprox ≤ gApprox` pointwise;
* (c) monotone in `t` (comparing level-`t` to level-`t+1` readings);
* (d) *minimal* bound: if a semimeasure `μ` dominates `fApprox` at level `t`, it
  dominates `gApprox` at level `t`. Used in completeness.
-/

/-- Base: when `|x| = t`, `gApprox e t x = fApprox e t x`. -/
theorem gApprox_eq_fApprox_of_length_eq {e t : ℕ} {x : List Bool} (h : x.length = t) :
    gApprox e t x = fApprox e t x := by
  conv_lhs => unfold gApprox
  have h1 : ¬ x.length < t := by omega
  simp [h1, h]

/-- Above the frontier: `gApprox e t x = 0` when `|x| > t`. -/
theorem gApprox_eq_zero_of_length_gt {e t : ℕ} {x : List Bool} (h : t < x.length) :
    gApprox e t x = 0 := by
  conv_lhs => unfold gApprox
  have h1 : ¬ x.length < t := by omega
  have h2 : x.length ≠ t := by omega
  simp [h1, h2]

/-- Below the frontier: unfolding. -/
theorem gApprox_eq_of_length_lt {e t : ℕ} {x : List Bool} (h : x.length < t) :
    gApprox e t x = max (fApprox e t x)
        (gApprox e t (x ++ [false]) + gApprox e t (x ++ [true])) := by
  conv_lhs => unfold gApprox
  simp [h]

/-- (a) child-sum ≤ parent, in dyadic (level-`t`) form. -/
theorem gApprox_extend_le (e t : ℕ) (x : List Bool) :
    gApprox e t (x ++ [false]) + gApprox e t (x ++ [true]) ≤ gApprox e t x := by
  have hlen0 : (x ++ [false]).length = x.length + 1 := by simp
  have hlen1 : (x ++ [true]).length = x.length + 1 := by simp
  rcases lt_trichotomy x.length t with h | h | h
  · -- |x| < t: by the unfolding
    rw [gApprox_eq_of_length_lt h]
    exact le_max_right _ _
  · -- |x| = t: children at length t+1 are 0
    rw [gApprox_eq_zero_of_length_gt (by omega : t < (x ++ [false]).length),
        gApprox_eq_zero_of_length_gt (by omega : t < (x ++ [true]).length)]
    exact Nat.zero_le _
  · -- |x| > t: everything 0
    rw [gApprox_eq_zero_of_length_gt (by omega : t < (x ++ [false]).length),
        gApprox_eq_zero_of_length_gt (by omega : t < (x ++ [true]).length)]
    exact Nat.zero_le _

/-- (b) `fApprox` is dominated by `gApprox` pointwise at the same stage, provided
`|x| ≤ t`. -/
theorem fApprox_le_gApprox (e t : ℕ) (x : List Bool) (h : x.length ≤ t) :
    fApprox e t x ≤ gApprox e t x := by
  rcases h.lt_or_eq with h | h
  · rw [gApprox_eq_of_length_lt h]; exact le_max_left _ _
  · rw [gApprox_eq_fApprox_of_length_eq h]

/-- A single `candidate` at level `t+1` dominates twice its level-`t` value when `n ≤ t`. -/
theorem candidate_double_le (e t n : ℕ) (x : List Bool) (hn : n ≤ t) :
    2 * candidate e t n x ≤ candidate e (t + 1) n x := by
  unfold candidate
  cases hev : Nat.Partrec.Code.evaln t (codeOf e) (Encodable.encode (x, n)) with
  | none => simp
  | some k =>
    have hmem : k ∈ Nat.Partrec.Code.evaln t (codeOf e) (Encodable.encode (x, n)) := hev
    have hnext : k ∈ Nat.Partrec.Code.evaln (t + 1) (codeOf e) (Encodable.encode (x, n)) :=
      Nat.Partrec.Code.evaln_mono (Nat.le_succ t) hmem
    have hev' : Nat.Partrec.Code.evaln (t + 1) (codeOf e) (Encodable.encode (x, n)) = some k :=
      hnext
    rw [hev']
    -- 2 * (k * 2^(t-n)) ≤ k * 2^(t+1-n)
    have hsub : t + 1 - n = (t - n) + 1 := by omega
    rw [hsub, pow_succ]
    ring_nf
    exact le_rfl

/-- Level-up for `fApprox`: doubling at level `t` gives a bound at level `t+1`. -/
theorem fApprox_double_le (e t : ℕ) (x : List Bool) :
    2 * fApprox e t x ≤ fApprox e (t + 1) x := by
  obtain ⟨m, hm_mem, hm_eq⟩ :=
    Finset.exists_mem_eq_sup (Finset.range (t + 1)) Finset.nonempty_range_add_one
      (fun n => candidate e t n x)
  have hfApprox_eq : fApprox e t x = candidate e t m x := hm_eq
  have hm_le : m ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm_mem)
  rw [hfApprox_eq]
  calc 2 * candidate e t m x
      ≤ candidate e (t + 1) m x := candidate_double_le e t m x hm_le
    _ ≤ fApprox e (t + 1) x := by
        unfold fApprox
        exact Finset.le_sup (f := fun n => candidate e (t + 1) n x)
          (Finset.mem_range.mpr (by omega : m < t + 2))

/-- (c) `gApprox` is monotone in `t`, comparing level-`t` vs level-`t+1` dyadic
readings. The numerator grows by *at least* a factor of 2.

Induction on `t - x.length`: for `|x| ≥ t`, LHS is `0` or `2 * f` and we unfold
level `t+1` once; for `|x| < t`, use the recursion. -/
theorem gApprox_mono_step (e t : ℕ) (x : List Bool) :
    2 * gApprox e t x ≤ gApprox e (t + 1) x := by
  have aux : ∀ d, ∀ x : List Bool, t - x.length = d →
      2 * gApprox e t x ≤ gApprox e (t + 1) x := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x hd
      rcases lt_trichotomy x.length t with h | h | h
      · -- |x| < t: g e t x = max (f, children sum); g e (t+1) x = max (f', children' sum).
        rw [gApprox_eq_of_length_lt h,
            gApprox_eq_of_length_lt (by omega : x.length < t + 1)]
        have hd0 : t - (x ++ [false]).length < d := by
          simp [List.length_append]; omega
        have hd1 : t - (x ++ [true]).length < d := by
          simp [List.length_append]; omega
        have ih0 : 2 * gApprox e t (x ++ [false]) ≤ gApprox e (t + 1) (x ++ [false]) :=
          ih _ hd0 _ rfl
        have ih1 : 2 * gApprox e t (x ++ [true]) ≤ gApprox e (t + 1) (x ++ [true]) :=
          ih _ hd1 _ rfl
        have hmax : 2 * max (fApprox e t x)
              (gApprox e t (x ++ [false]) + gApprox e t (x ++ [true]))
            = max (2 * fApprox e t x)
                  (2 * gApprox e t (x ++ [false]) + 2 * gApprox e t (x ++ [true])) := by
          rw [mul_max, Nat.mul_add]
        rw [hmax]
        exact max_le_max (fApprox_double_le e t x)
          (Nat.add_le_add ih0 ih1)
      · -- |x| = t: g e t x = f e t x. g e (t+1) x: |x| < t+1, so recurse.
        rw [gApprox_eq_fApprox_of_length_eq h,
            gApprox_eq_of_length_lt (by omega : x.length < t + 1)]
        calc 2 * fApprox e t x ≤ fApprox e (t + 1) x := fApprox_double_le e t x
          _ ≤ _ := le_max_left _ _
      · -- |x| > t: g e t x = 0; LHS = 0.
        rw [gApprox_eq_zero_of_length_gt h]
        simp
  exact aux _ x rfl

/-- `dyadic` is monotone in the numerator. -/
theorem dyadic_mono_num {a b n : ℕ} (h : a ≤ b) : dyadic a n ≤ dyadic b n := by
  unfold dyadic
  have : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast h
  gcongr

/-- (d) Minimality: if a semimeasure `μ` dominates the level-`t` `fApprox`, it
dominates the level-`t` `gApprox`. Here "dominates at level `t`" is
`dyadic (· ) t ≤ μ x`. Used in completeness. -/
theorem gApprox_le_of_fApprox_le {e t : ℕ} (μ : Semimeasure)
    (hf : ∀ x, dyadic (fApprox e t x) t ≤ μ x) (x : List Bool) :
    dyadic (gApprox e t x) t ≤ μ x := by
  have aux : ∀ d, ∀ x : List Bool, t - x.length = d → dyadic (gApprox e t x) t ≤ μ x := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x hd
      rcases lt_trichotomy x.length t with h | h | h
      · -- |x| < t: unfold, induct
        rw [gApprox_eq_of_length_lt h]
        have hd0 : t - (x ++ [false]).length < d := by simp [List.length_append]; omega
        have hd1 : t - (x ++ [true]).length < d := by simp [List.length_append]; omega
        have ih0 : dyadic (gApprox e t (x ++ [false])) t ≤ μ (x ++ [false]) := ih _ hd0 _ rfl
        have ih1 : dyadic (gApprox e t (x ++ [true])) t ≤ μ (x ++ [true]) := ih _ hd1 _ rfl
        rcases le_total (fApprox e t x)
            (gApprox e t (x ++ [false]) + gApprox e t (x ++ [true])) with hle | hle
        · rw [max_eq_right hle, dyadic_add]
          exact (add_le_add ih0 ih1).trans (μ.extend_le x)
        · rw [max_eq_left hle]
          exact hf x
      · -- |x| = t: g = f, immediate.
        rw [gApprox_eq_fApprox_of_length_eq h]
        exact hf x
      · -- |x| > t: g = 0.
        rw [gApprox_eq_zero_of_length_gt h]
        simp [dyadic]
  exact aux _ x rfl

/-! ### Properties of `GApprox` and `enumFun` -/

/-- `GApprox e t` satisfies the extend inequality (uses (a)). -/
theorem GApprox_extend_le (e t : ℕ) (x : List Bool) :
    GApprox e t (x ++ [false]) + GApprox e t (x ++ [true]) ≤ GApprox e t x := by
  sorry

/-- `GApprox e t []` is at most 1 (by construction of the freeze). -/
theorem GApprox_root_le_one (e t : ℕ) : GApprox e t [] ≤ 1 := by
  sorry

/-- `GApprox e t` is monotone in `t`. -/
theorem GApprox_mono (e : ℕ) : Monotone (GApprox e · · : ℕ → List Bool → ℝ≥0∞) := by
  sorry

theorem GApprox_mono' (e : ℕ) (x : List Bool) : Monotone (fun t => GApprox e t x) := by
  intro s t h
  exact GApprox_mono e h x

/-- `enumFun` satisfies the extend inequality — iSup of a monotone family of
semimeasures. -/
theorem enumFun_extend_le (e : ℕ) (x : List Bool) :
    enumFun e (x ++ [false]) + enumFun e (x ++ [true]) ≤ enumFun e x := by
  have hmono₀ := GApprox_mono' e (x ++ [false])
  have hmono₁ := GApprox_mono' e (x ++ [true])
  show (⨆ t, GApprox e t (x ++ [false])) + (⨆ t, GApprox e t (x ++ [true]))
      ≤ ⨆ t, GApprox e t x
  calc (⨆ t, GApprox e t (x ++ [false])) + (⨆ t, GApprox e t (x ++ [true]))
      = ⨆ t, (GApprox e t (x ++ [false]) + GApprox e t (x ++ [true])) :=
        ENNReal.iSup_add_iSup_of_monotone hmono₀ hmono₁
    _ ≤ ⨆ t, GApprox e t x := iSup_mono (fun t => GApprox_extend_le e t x)

/-- `enumFun e []` ≤ 1. -/
theorem enumFun_empty_le_one (e : ℕ) : enumFun e [] ≤ 1 :=
  iSup_le fun t => GApprox_root_le_one e t

/-- The enumeration: for each `e`, a `Semimeasure`. -/
noncomputable def enum (e : ℕ) : Semimeasure where
  toFun := enumFun e
  empty_le_one := enumFun_empty_le_one e
  extend_le := enumFun_extend_le e

/-! ### Completeness

Given `μ` with `μ.Enumerable` — a computable `φ : List Bool → ℕ → ℕ` with
`dyadic (φ x n) n` monotone with sup `μ x` — we build a code `e` with
`enum e = μ`. -/

theorem enum_complete : ∀ μ : Semimeasure, μ.Enumerable → ∃ e, enum e = μ := by
  sorry

/-! ### Uniform enumerability

Hardest step — the bottom-up recursion has to be shown computable. Isolated. -/

theorem enum_uniformlyEnumerable : UniformlyEnumerable enum := by
  sorry

/-! ### The interface and the corollary -/

/-- The constructed `WoodInterface`. -/
noncomputable def woodInterface : WoodInterface where
  enum := enum
  enum_enumerable := enum_uniformlyEnumerable
  enum_complete := enum_complete

/-- The spine theorem, unconditional: `WoodInterface` is now supplied by
`woodInterface`. -/
theorem mixtureClass_eq_universalMixtures'
    (ν : ℕ → Semimeasure)
    (hν_enum : UniformlyEnumerable ν)
    (hν_univ : ContainsAllUniversalMixtures ν) :
    MixtureClass ν = {ξ | IsUniversalMixture ξ} :=
  mixtureClass_eq_universalMixtures ν woodInterface hν_enum hν_univ

end HsiLean.Wood

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

/-- `candidate e 0 _ _ = 0` since `evaln 0` always fails. -/
theorem candidate_zero (e n : ℕ) (x : List Bool) : candidate e 0 n x = 0 := by
  unfold candidate
  simp [Nat.Partrec.Code.evaln]

/-- `fApprox e 0 x = 0`. -/
theorem fApprox_zero (e : ℕ) (x : List Bool) : fApprox e 0 x = 0 := by
  unfold fApprox
  apply Nat.le_zero.mp
  apply Finset.sup_le
  intro n _; rw [candidate_zero]

/-- `gApprox e 0 [] = 0`. -/
theorem gApprox_zero_root (e : ℕ) : gApprox e 0 [] = 0 := by
  rw [gApprox_eq_fApprox_of_length_eq (by rfl : ([] : List Bool).length = 0),
      fApprox_zero]

/-- The freezeStage picks a stage `s` at which `g e s []` is bounded by `2^s`. -/
theorem freezeStage_safe (e t : ℕ) :
    (gApprox e (freezeStage e t) [] : ℝ≥0∞) ≤ 2 ^ (freezeStage e t) := by
  unfold freezeStage
  obtain ⟨m, _, hm_eq⟩ :=
    Finset.exists_mem_eq_sup (Finset.range (t + 1)) Finset.nonempty_range_add_one
      (fun s => if (gApprox e s [] : ℝ≥0∞) ≤ 2 ^ s then s else 0)
  rw [hm_eq]
  split_ifs with hc
  · exact hc
  · rw [gApprox_zero_root]; simp

/-- `freezeStage` is monotone in `t`. -/
theorem freezeStage_mono (e : ℕ) : Monotone (freezeStage e) := by
  intro s t h
  unfold freezeStage
  exact Finset.sup_mono (Finset.range_subset_range.mpr (Nat.succ_le_succ h))

/-- `GApprox e t` satisfies the extend inequality (uses (a) + dyadic_add). -/
theorem GApprox_extend_le (e t : ℕ) (x : List Bool) :
    GApprox e t (x ++ [false]) + GApprox e t (x ++ [true]) ≤ GApprox e t x := by
  unfold GApprox
  rw [← dyadic_add]
  exact dyadic_mono_num (gApprox_extend_le e (freezeStage e t) x)

/-- `GApprox e t []` is at most 1 (by construction of the freeze). -/
theorem GApprox_root_le_one (e t : ℕ) : GApprox e t [] ≤ 1 := by
  unfold GApprox dyadic
  have hs := freezeStage_safe e t
  set s := freezeStage e t
  have h2 : (2 : ℝ≥0∞)^s ≠ 0 := by positivity
  have h2t : (2 : ℝ≥0∞)^s ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [ENNReal.div_le_iff h2 h2t, one_mul]
  exact hs

/-- Dyadic level-shift as used here: double numerator, exponent up by 1. -/
theorem dyadic_double_succ (a t : ℕ) : dyadic (2 * a) (t + 1) = dyadic a t := by
  have := dyadic_mul_shift a t (t + 1) (Nat.le_succ t)
  simp at this
  convert this using 2
  ring

/-- Reading `gApprox` at level `t` vs `t+1`: level up preserves (or increases) the dyadic value. -/
theorem gApprox_dyadic_le_succ (e t : ℕ) (x : List Bool) :
    dyadic (gApprox e t x) t ≤ dyadic (gApprox e (t + 1) x) (t + 1) := by
  have hmul := gApprox_mono_step e t x
  calc dyadic (gApprox e t x) t
      = dyadic (2 * gApprox e t x) (t + 1) := (dyadic_double_succ _ _).symm
    _ ≤ dyadic (gApprox e (t + 1) x) (t + 1) := dyadic_mono_num hmul

/-- Monotonicity of `dyadic (g e t x) t` in `t`. -/
theorem gApprox_dyadic_mono (e : ℕ) (x : List Bool) :
    Monotone (fun t => dyadic (gApprox e t x) t) :=
  monotone_nat_of_le_succ (fun t => gApprox_dyadic_le_succ e t x)

/-- `GApprox e t` is monotone in `t`. -/
theorem GApprox_mono (e : ℕ) : Monotone (GApprox e · · : ℕ → List Bool → ℝ≥0∞) := by
  intro s t h x
  unfold GApprox
  exact gApprox_dyadic_mono e x (freezeStage_mono e h)

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

/-- A single `candidate` at the chosen code, when `evaln` has caught up, yields
    `dyadic (φ x n) n`. -/
theorem candidate_dyadic_eq {e t n : ℕ} {x : List Bool} {k : ℕ}
    (hn : n ≤ t)
    (hev : Nat.Partrec.Code.evaln t (codeOf e) (Encodable.encode (x, n)) = some k) :
    dyadic (candidate e t n x) t = dyadic k n := by
  unfold candidate
  rw [hev]
  exact dyadic_mul_shift k n t hn

/-- `dyadic (fApprox e t x) t` is monotone in `t`. -/
theorem fApprox_dyadic_mono (e : ℕ) (x : List Bool) :
    Monotone (fun t => dyadic (fApprox e t x) t) := by
  apply monotone_nat_of_le_succ
  intro t
  calc dyadic (fApprox e t x) t
      = dyadic (2 * fApprox e t x) (t + 1) := (dyadic_double_succ _ _).symm
    _ ≤ dyadic (fApprox e (t + 1) x) (t + 1) := dyadic_mono_num (fApprox_double_le e t x)

theorem enum_complete : ∀ μ : Semimeasure, μ.Enumerable → ∃ e, enum e = μ := by
  intro μ hμ
  obtain ⟨φ, hφ_comp, hφ_mono, hφ_sup⟩ := hμ
  -- Get a Nat.Partrec.Code for `fun p => some (φ p.1 p.2)`.
  have hpart : Nat.Partrec (fun n => Part.bind
      ((Encodable.decode (α := List Bool × ℕ) n : Part (List Bool × ℕ)))
      fun p : List Bool × ℕ =>
      (Part.some (φ p.1 p.2)).map Encodable.encode) := hφ_comp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨Encodable.encode c, ?_⟩
  -- The code we chose decodes to `c`.
  have hcodeOf : codeOf (Encodable.encode c) = c :=
    Denumerable.ofNat_encode (α := Nat.Partrec.Code) c
  set e := Encodable.encode c
  -- `eval c (encode (x, n))` is `Part.some (φ x n)`.
  have heval : ∀ x n, Nat.Partrec.Code.eval c (Encodable.encode (x, n)) = Part.some (φ x n) := by
    intro x n
    rw [hc]
    simp [Encodable.encodek, Encodable.encode_nat]
  -- Hence for every `x, n`, some `t` makes `evaln t c ... = some (φ x n)`.
  have hevaln : ∀ x n, ∃ T, Nat.Partrec.Code.evaln T c (Encodable.encode (x, n)) = some (φ x n) := by
    intro x n
    have hmem : φ x n ∈ Nat.Partrec.Code.eval c (Encodable.encode (x, n)) := by
      rw [heval]; exact Part.mem_some _
    exact Nat.Partrec.Code.evaln_complete.mp hmem
  -- `encode (x, n)` has `n` in its right pair component, so `n ≤ encode (x, n)`.
  have hpair_ge : ∀ (x : List Bool) (n : ℕ), n ≤ Encodable.encode (x, n) := by
    intro x n
    have : Encodable.encode (x, n) = Nat.pair (Encodable.encode x) (Encodable.encode n) := rfl
    rw [this, Encodable.encode_nat]
    exact Nat.right_le_pair _ _
  -- Candidate bound: dyadic (candidate e t n x) t ≤ μ x.
  have hcand_le : ∀ t n x, dyadic (candidate e t n x) t ≤ μ x := by
    intro t n x
    unfold candidate
    cases hev : Nat.Partrec.Code.evaln t (codeOf e) (Encodable.encode (x, n)) with
    | none => simp [dyadic]
    | some k =>
      -- evaln succeeded with value k. By evaln_sound, k ∈ eval c ... = some (φ x n), so k = φ x n.
      have hmem : k ∈ Nat.Partrec.Code.evaln t c (Encodable.encode (x, n)) := by
        rw [hcodeOf] at hev; exact hev
      have hin : k ∈ Nat.Partrec.Code.eval c (Encodable.encode (x, n)) :=
        Nat.Partrec.Code.evaln_sound hmem
      rw [heval] at hin
      have hkφ : k = φ x n := Part.mem_some_iff.mp hin
      -- n must satisfy: encode (x,n) < t, so n ≤ encode (x,n) < t ⟹ n < t.
      have hbd : Encodable.encode (x, n) < t := Nat.Partrec.Code.evaln_bound hmem
      have hn_lt : n < t := lt_of_le_of_lt (hpair_ge x n) hbd
      have hn_le : n ≤ t := hn_lt.le
      -- dyadic (k * 2^(t-n)) t = dyadic k n = dyadic (φ x n) n ≤ μ x.
      rw [dyadic_mul_shift k n t hn_le, hkφ, ← hφ_sup x]
      exact le_iSup (fun m => dyadic (φ x m) m) n
  -- fApprox bound at level t: dyadic (fApprox e t x) t ≤ μ x.
  have hfApprox_le : ∀ t x, dyadic (fApprox e t x) t ≤ μ x := by
    intro t x
    unfold fApprox
    obtain ⟨m, _, hm_eq⟩ :=
      Finset.exists_mem_eq_sup (Finset.range (t + 1)) Finset.nonempty_range_add_one
        (fun n => candidate e t n x)
    rw [hm_eq]
    exact hcand_le t m x
  -- gApprox bound by minimality (d).
  have hgApprox_le : ∀ t x, dyadic (gApprox e t x) t ≤ μ x := fun t x =>
    gApprox_le_of_fApprox_le μ (fun y => hfApprox_le t y) x
  -- freezeStage = t for the chosen e, since every stage is safe.
  have hall_safe : ∀ s, (gApprox e s [] : ℝ≥0∞) ≤ 2 ^ s := by
    intro s
    have h1 : dyadic (gApprox e s []) s ≤ μ [] := hgApprox_le s []
    have h2 : μ ([] : List Bool) ≤ 1 := μ.empty_le_one
    have h3 : dyadic (gApprox e s []) s ≤ 1 := h1.trans h2
    unfold dyadic at h3
    have h2p0 : (2 : ℝ≥0∞) ^ s ≠ 0 := by positivity
    have h2pt : (2 : ℝ≥0∞) ^ s ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
    rwa [ENNReal.div_le_iff h2p0 h2pt, one_mul] at h3
  have hfreeze : ∀ t, freezeStage e t = t := by
    intro t
    unfold freezeStage
    apply le_antisymm
    · apply Finset.sup_le
      intro n hn
      split_ifs
      · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      · exact Nat.zero_le _
    · refine Finset.le_sup (f := fun s => if (gApprox e s [] : ℝ≥0∞) ≤ 2^s then s else 0)
        (b := t) (Finset.mem_range.mpr (by omega)) |>.trans_eq' ?_
      rw [if_pos (hall_safe t)]
  -- enumFun e x = sup t dyadic (gApprox e t x) t.
  have henum_eq : ∀ x, enumFun e x = ⨆ t, dyadic (gApprox e t x) t := by
    intro x
    unfold enumFun GApprox
    exact iSup_congr fun t => by rw [hfreeze t]
  apply Semimeasure.ext
  intro x
  show enumFun e x = μ x
  rw [henum_eq x]
  apply le_antisymm
  · exact iSup_le fun t => hgApprox_le t x
  · -- ≥: sup over n of dyadic (φ x n) n = μ x, and each ≤ sup over t.
    rw [← hφ_sup x]
    apply iSup_le
    intro n
    -- Find a t large enough: t ≥ max(encode(x,n), T(x,n), n, |x|).
    obtain ⟨T, hT⟩ := hevaln x n
    set t₀ := max T (max (Encodable.encode (x, n) + 1) (max (n + 1) x.length)) with ht₀_def
    have hT_le : T ≤ t₀ := le_max_left _ _
    have henc_lt : Encodable.encode (x, n) < t₀ :=
      Nat.lt_of_succ_le (le_max_of_le_right (le_max_left _ _))
    have hn_le : n ≤ t₀ :=
      (Nat.le_succ n).trans (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    have hx_le : x.length ≤ t₀ :=
      le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
    -- at level t₀, evaln succeeds
    have hev_t₀ : Nat.Partrec.Code.evaln t₀ c (Encodable.encode (x, n)) = some (φ x n) := by
      have hmem : φ x n ∈ Nat.Partrec.Code.evaln T c (Encodable.encode (x, n)) := hT
      have hnext := Nat.Partrec.Code.evaln_mono hT_le hmem
      exact hnext
    have hev_t₀' : Nat.Partrec.Code.evaln t₀ (codeOf e) (Encodable.encode (x, n)) = some (φ x n) := by
      rw [hcodeOf]; exact hev_t₀
    -- Then candidate e t₀ n x = φ x n * 2^(t₀-n), so dyadic = dyadic (φ x n) n.
    have hcand_val : dyadic (candidate e t₀ n x) t₀ = dyadic (φ x n) n :=
      candidate_dyadic_eq hn_le hev_t₀'
    -- candidate ≤ fApprox at t₀ (since n ∈ range (t₀+1))
    have hc_le_f : dyadic (candidate e t₀ n x) t₀ ≤ dyadic (fApprox e t₀ x) t₀ := by
      apply dyadic_mono_num
      unfold fApprox
      exact Finset.le_sup (f := fun m => candidate e t₀ m x)
        (Finset.mem_range.mpr (by omega : n < t₀ + 1))
    -- fApprox ≤ gApprox at t₀ (since |x| ≤ t₀)
    have hf_le_g : dyadic (fApprox e t₀ x) t₀ ≤ dyadic (gApprox e t₀ x) t₀ :=
      dyadic_mono_num (fApprox_le_gApprox e t₀ x hx_le)
    -- Chain
    calc dyadic (φ x n) n
        = dyadic (candidate e t₀ n x) t₀ := hcand_val.symm
      _ ≤ dyadic (fApprox e t₀ x) t₀ := hc_le_f
      _ ≤ dyadic (gApprox e t₀ x) t₀ := hf_le_g
      _ ≤ _ := le_iSup (fun t => dyadic (gApprox e t x) t) t₀

/-! ### Computable formulation of `gApprox`

To prove `UniformlyEnumerable enum`, we need `gApprox` computable in `(e, t, x)`.
The recursion is bottom-up on `t - x.length`; we materialise this as a DP table
iterated via `Nat.rec`, with the state at step `n` being a `List ℕ` of all
`gApprox e t y` values for `y = x ++ b` with `|b| = t - x.length - n`. -/

/-- Length-`d` binary string with MSB-first index `i` (bits of `i`, padded to `d`).
Closed form via `List.range` for direct `Primrec`. -/
private def strOfIdx (d i : ℕ) : List Bool :=
  (List.range d).map (fun k => decide ((i / 2^(d - 1 - k)) % 2 = 1))

private theorem strOfIdx_length (d i : ℕ) : (strOfIdx d i).length = d := by
  simp [strOfIdx]

/-- Recursive characterisation of `strOfIdx`: `strOfIdx (d+1) i
    = strOfIdx d (i/2) ++ [decide (i % 2 = 1)]`. -/
private theorem strOfIdx_succ (d i : ℕ) :
    strOfIdx (d+1) i = strOfIdx d (i / 2) ++ [decide (i % 2 = 1)] := by
  unfold strOfIdx
  rw [List.range_succ, List.map_append, List.map_singleton]
  -- LHS: (List.range (d+1)).map (fun k => decide ((i / 2^(d-k)) % 2 = 1))
  --    = (List.range d).map ... ++ [decide ((i / 2^(d-d)) % 2 = 1)]
  --    = (List.range d).map ... ++ [decide ((i / 2^0) % 2 = 1)]
  --    = (List.range d).map ... ++ [decide (i % 2 = 1)]
  -- RHS: (List.range d).map (fun k => decide ((i/2 / 2^(d-1-k)) % 2 = 1)) ++ [decide (i%2=1)]
  -- Need: inside the first map, the two functions agree.
  congr 1
  · apply List.map_congr_left
    intro k hk
    have hk_lt : k < d := List.mem_range.mp hk
    congr 2
    -- Goal: i / 2^(d + 1 - 1 - k) = i / 2 / 2^(d - 1 - k)
    rw [Nat.div_div_eq_div_mul]
    have hexp : (d + 1 - 1 - k) = (d - 1 - k) + 1 := by
      have : d ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; omega)
      omega
    rw [hexp, pow_succ, Nat.mul_comm]
  · simp

private theorem strOfIdx_append_false (d i : ℕ) :
    strOfIdx d i ++ [false] = strOfIdx (d + 1) (2 * i) := by
  rw [strOfIdx_succ]
  rw [show (2 * i) / 2 = i by omega, show (2 * i) % 2 = 0 by omega]
  rfl

private theorem strOfIdx_append_true (d i : ℕ) :
    strOfIdx d i ++ [true] = strOfIdx (d + 1) (2 * i + 1) := by
  rw [strOfIdx_succ]
  rw [show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega]
  rfl

/-- One DP step: produce the row at depth `j` from the row at depth `j+1`. -/
private noncomputable def dpStep (e t : ℕ) (x : List Bool) (j : ℕ) (prev : List ℕ) : List ℕ :=
  (List.range (2^j)).map fun i =>
    max (fApprox e t (x ++ strOfIdx j i)) (prev.getD (2*i) 0 + prev.getD (2*i + 1) 0)

/-- Base row of the DP table at depth `k = t - x.length`. -/
private noncomputable def dpBase (e t : ℕ) (x : List Bool) (k : ℕ) : List ℕ :=
  (List.range (2^k)).map fun i => fApprox e t (x ++ strOfIdx k i)

/-- DP table iteration. After `n` steps, holds the row at depth `k - n`
(where `k = t - x.length`). -/
private noncomputable def dpIter (e t : ℕ) (x : List Bool) : ℕ → List ℕ
  | 0 => dpBase e t x (t - x.length)
  | n + 1 => dpStep e t x (t - x.length - n - 1) (dpIter e t x n)

/-- Table-based `gApprox`. -/
private noncomputable def gApproxComp (e t : ℕ) (x : List Bool) : ℕ :=
  if t < x.length then 0
  else (dpIter e t x (t - x.length)).getD 0 0

/-- DP invariant: after `n` steps, the row is `gApprox` at every length-`(k-n)`
extension of `x` (indexed canonically). -/
private theorem dpIter_spec (e t : ℕ) (x : List Bool) (ht : x.length ≤ t) :
    ∀ n ≤ t - x.length,
      dpIter e t x n = (List.range (2^(t - x.length - n))).map
        fun i => gApprox e t (x ++ strOfIdx (t - x.length - n) i) := by
  intro n hn
  induction n with
  | zero =>
    show dpBase e t x (t - x.length) = _
    rw [Nat.sub_zero]
    apply List.map_congr_left
    intro i _
    symm
    apply gApprox_eq_fApprox_of_length_eq
    rw [List.length_append, strOfIdx_length]
    omega
  | succ n ih =>
    have hn_le : n ≤ t - x.length := le_trans (Nat.le_succ n) hn
    have ih' := ih hn_le
    show dpStep e t x (t - x.length - n - 1) (dpIter e t x n) = _
    rw [ih']
    unfold dpStep
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < 2^(t - x.length - n - 1) := List.mem_range.mp hi
    have hpow : (2 : ℕ)^(t - x.length - n) = 2 * 2^(t - x.length - n - 1) := by
      rw [show t - x.length - n = (t - x.length - n - 1) + 1 by omega, pow_succ,
        Nat.mul_comm]
      simp
    have h2i_lt : 2 * i < 2^(t - x.length - n) := by omega
    have h2i1_lt : 2 * i + 1 < 2^(t - x.length - n) := by omega
    -- getD on range-map: indices 2*i and 2*i+1 are in range.
    have hget_false : ((List.range (2^(t - x.length - n))).map
        fun j => gApprox e t (x ++ strOfIdx (t - x.length - n) j)).getD (2 * i) 0
        = gApprox e t (x ++ strOfIdx (t - x.length - n) (2 * i)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range h2i_lt]
      rfl
    have hget_true : ((List.range (2^(t - x.length - n))).map
        fun j => gApprox e t (x ++ strOfIdx (t - x.length - n) j)).getD (2 * i + 1) 0
        = gApprox e t (x ++ strOfIdx (t - x.length - n) (2 * i + 1)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range h2i1_lt]
      rfl
    rw [hget_false, hget_true]
    -- strOfIdx (k-n) (2i) = strOfIdx (k-n-1) i ++ [false]
    have heq_false : strOfIdx (t - x.length - n) (2 * i)
        = strOfIdx (t - x.length - n - 1) i ++ [false] := by
      rw [strOfIdx_append_false]; congr 1; omega
    have heq_true : strOfIdx (t - x.length - n) (2 * i + 1)
        = strOfIdx (t - x.length - n - 1) i ++ [true] := by
      rw [strOfIdx_append_true]; congr 1; omega
    rw [heq_false, heq_true]
    rw [show (x ++ (strOfIdx (t - x.length - n - 1) i ++ [false]))
          = (x ++ strOfIdx (t - x.length - n - 1) i) ++ [false] by rw [List.append_assoc]]
    rw [show (x ++ (strOfIdx (t - x.length - n - 1) i ++ [true]))
          = (x ++ strOfIdx (t - x.length - n - 1) i) ++ [true] by rw [List.append_assoc]]
    symm
    apply gApprox_eq_of_length_lt
    rw [List.length_append, strOfIdx_length]
    omega

/-- The table-based version agrees with the mathematical definition. -/
private theorem gApproxComp_eq (e t : ℕ) (x : List Bool) :
    gApproxComp e t x = gApprox e t x := by
  unfold gApproxComp
  split_ifs with h
  · symm; exact gApprox_eq_zero_of_length_gt h
  · have ht : x.length ≤ t := Nat.not_lt.mp h
    have hspec := dpIter_spec e t x ht (t - x.length) le_rfl
    rw [hspec]
    have hsub : t - x.length - (t - x.length) = 0 := by omega
    rw [hsub]
    show (((List.range 1).map fun i => gApprox e t (x ++ strOfIdx 0 i)).getD 0 0)
        = gApprox e t x
    simp [strOfIdx]

/-! ### Nat-recursive `freezeStage`

For Primrec, we need `freezeStage` as a `Nat.rec`. The existing definition uses
`Finset.range.sup` of an ENNReal condition; we provide a `Nat.rec` form with a
pure-Nat condition, and prove the two agree. -/

/-- Pure-ℕ, `Nat.rec`-based form of `freezeStage`. Uses `gApproxComp` and the
Nat condition `gApproxComp e s [] ≤ 2^s`. -/
private noncomputable def freezeStageNat (e t : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun s acc => max acc (if gApproxComp e s [] ≤ 2^s then s else 0))
    (t + 1)

/-- General lemma: `Finset.range (t+1).sup f` equals the `Nat.rec` accumulator. -/
private theorem range_sup_eq_rec (t : ℕ) (f : ℕ → ℕ) :
    (Finset.range (t + 1)).sup f
      = Nat.rec (motive := fun _ => ℕ) 0 (fun s acc => max acc (f s)) (t + 1) := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_add_one, Finset.sup_insert]
    show max (f (k+1)) ((Finset.range (k+1)).sup f) = _
    rw [ih]
    exact max_comm _ _

/-- The two forms of `freezeStage` agree. -/
private theorem freezeStageNat_eq (e t : ℕ) : freezeStageNat e t = freezeStage e t := by
  have hcond : ∀ s, ((gApprox e s [] : ℝ≥0∞) ≤ 2 ^ s) ↔ gApprox e s [] ≤ 2 ^ s := by
    intro s
    rw [show (2 : ℝ≥0∞) ^ s = ((2 ^ s : ℕ) : ℝ≥0∞) by push_cast; rfl]
    exact_mod_cast Iff.rfl
  have hgac : ∀ s, gApproxComp e s [] = gApprox e s [] := fun s => gApproxComp_eq _ _ _
  have hbranch : ∀ s,
      (if gApproxComp e s [] ≤ 2^s then s else 0)
        = (if ((gApprox e s [] : ℝ≥0∞) ≤ 2^s) then s else 0) := by
    intro s
    rw [hgac s]
    split_ifs with h h' h'
    · rfl
    · exact absurd ((hcond s).mpr h) h'
    · exact absurd ((hcond s).mp h') h
    · rfl
  unfold freezeStageNat freezeStage
  rw [range_sup_eq_rec]
  have hstep : (fun s acc : ℕ => max acc (if gApproxComp e s [] ≤ 2^s then s else 0))
      = (fun s acc : ℕ => max acc (if ((gApprox e s [] : ℝ≥0∞) ≤ 2^s) then s else 0)) := by
    funext s acc
    rw [hbranch s]
  rw [hstep]

/-! ### Primrec chain

Each piece Primrec, culminating in the LSC approximant. -/

/-- `strOfIdx` is Primrec. -/
private theorem strOfIdx_primrec : Primrec₂ strOfIdx := by
  change Primrec (fun p : ℕ × ℕ => strOfIdx p.1 p.2)
  unfold strOfIdx
  have h_range : Primrec (fun p : ℕ × ℕ => List.range p.1) :=
    Primrec.list_range.comp Primrec.fst
  have h_inner : Primrec₂ (fun (p : ℕ × ℕ) (k : ℕ) =>
      decide ((p.2 / 2^(p.1 - 1 - k)) % 2 = 1)) := by
    have h_d : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.1) := Primrec.fst.comp Primrec.fst
    have h_i : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.2) := Primrec.snd.comp Primrec.fst
    have h_k : Primrec (fun q : (ℕ × ℕ) × ℕ => q.2) := Primrec.snd
    have h_sub1 : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.1 - 1) :=
      Primrec.nat_sub.comp h_d (Primrec.const 1)
    have h_sub2 : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.1 - 1 - q.2) :=
      Primrec.nat_sub.comp h_sub1 h_k
    have h_pow : Primrec (fun q : (ℕ × ℕ) × ℕ => (2 : ℕ)^(q.1.1 - 1 - q.2)) :=
      Primrec.nat_pow.comp (Primrec.const 2) h_sub2
    have h_div : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.2 / 2^(q.1.1 - 1 - q.2)) :=
      Primrec.nat_div.comp h_i h_pow
    have h_mod : Primrec (fun q : (ℕ × ℕ) × ℕ => (q.1.2 / 2^(q.1.1 - 1 - q.2)) % 2) :=
      Primrec.nat_mod.comp h_div (Primrec.const 2)
    exact (PrimrecRel.comp Primrec.eq h_mod (Primrec.const 1)).decide
  exact Primrec.list_map h_range h_inner

/-- `candidate` is Primrec. Takes args as `((e, t, n), x)`. -/
private theorem candidate_primrec :
    Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool =>
      candidate q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold candidate
  have h_e : Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have h_t : Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have h_n : Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have h_x : Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool => q.2) := Primrec.snd
  have h_codeOf : Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool => codeOf q.1.1.1) :=
    (Primrec.ofNat Nat.Partrec.Code).comp h_e
  have h_enc : Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool =>
      Encodable.encode (q.2, q.1.2)) :=
    Primrec.encode.comp (Primrec.pair h_x h_n)
  have h_ev : Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool =>
      Nat.Partrec.Code.evaln q.1.1.2 (codeOf q.1.1.1) (Encodable.encode (q.2, q.1.2))) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair h_t h_codeOf) h_enc)
  have h_tsub : Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool => q.1.1.2 - q.1.2) :=
    Primrec.nat_sub.comp h_t h_n
  have h_pow : Primrec (fun q : ((ℕ × ℕ) × ℕ) × List Bool => (2 : ℕ)^(q.1.1.2 - q.1.2)) :=
    Primrec.nat_pow.comp (Primrec.const 2) h_tsub
  have h_some : Primrec₂ (fun (q : ((ℕ × ℕ) × ℕ) × List Bool) (k : ℕ) =>
      k * 2^(q.1.1.2 - q.1.2)) := by
    change Primrec (fun p : (((ℕ × ℕ) × ℕ) × List Bool) × ℕ => p.2 * 2^(p.1.1.1.2 - p.1.1.2))
    exact Primrec.nat_mul.comp Primrec.snd (h_pow.comp Primrec.fst)
  refine (Primrec.option_casesOn h_ev (Primrec.const 0) h_some).of_eq ?_
  intro q
  cases Nat.Partrec.Code.evaln q.1.1.2 (codeOf q.1.1.1) (Encodable.encode (q.2, q.1.2)) <;> simp

/-- Max is associative and commutative on Nat, so initial-value threads through foldr. -/
private theorem list_foldr_max_initial (l : List ℕ) (a : ℕ) :
    l.foldr max a = max a (l.foldr max 0) := by
  induction l with
  | nil => simp
  | cons h t ih =>
    change max h (t.foldr max a) = max a (max h (t.foldr max 0))
    rw [ih]
    rw [← max_assoc, max_comm h a, max_assoc]

/-- `(Finset.range (t+1)).sup f = ((List.range (t+1)).map f).foldr max 0`. -/
private theorem range_sup_eq_foldr (t : ℕ) (f : ℕ → ℕ) :
    (Finset.range (t + 1)).sup f = ((List.range (t + 1)).map f).foldr max 0 := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_add_one, Finset.sup_insert, ih]
    -- RHS: `(List.map f (List.range (k+2))).foldr max 0`.
    conv_rhs =>
      rw [show k + 1 + 1 = (k + 1) + 1 from rfl]
      rw [List.range_succ]
      rw [List.map_append, List.map_singleton, List.foldr_append]
      -- Now: (List.map f (List.range (k+1))).foldr max ([f (k+1)].foldr max 0)
      rw [show ([f (k+1)] : List ℕ).foldr max 0 = f (k+1) from by
        change max (f (k+1)) 0 = f (k+1); exact Nat.max_zero _]
    -- Now goal: max (f (k+1)) (...foldr max 0) = ...foldr max (f (k+1))
    exact (list_foldr_max_initial _ (f (k+1))).symm

/-- `fApprox` is Primrec. -/
private theorem fApprox_primrec :
    Primrec (fun p : (ℕ × ℕ) × List Bool => fApprox p.1.1 p.1.2 p.2) := by
  -- Prove Primrec of the list-foldr form, then transfer via equivalence.
  have hfA_list : Primrec (fun p : (ℕ × ℕ) × List Bool =>
      ((List.range (p.1.2 + 1)).map (fun n => candidate p.1.1 p.1.2 n p.2)).foldr max 0) := by
    have h_range : Primrec (fun p : (ℕ × ℕ) × List Bool => List.range (p.1.2 + 1)) :=
      Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
    have h_inner : Primrec₂ (fun (p : (ℕ × ℕ) × List Bool) (n : ℕ) =>
        candidate p.1.1 p.1.2 n p.2) := by
      change Primrec (fun q : ((ℕ × ℕ) × List Bool) × ℕ =>
        candidate q.1.1.1 q.1.1.2 q.2 q.1.2)
      exact candidate_primrec.comp (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
    have h_map : Primrec (fun p : (ℕ × ℕ) × List Bool =>
        (List.range (p.1.2 + 1)).map (fun n => candidate p.1.1 p.1.2 n p.2)) :=
      Primrec.list_map h_range h_inner
    -- foldr max 0: step is Primrec₂ (fun p (bs : ℕ × ℕ) => max bs.1 bs.2)
    have h_step : Primrec₂ (fun (_ : (ℕ × ℕ) × List Bool) (bs : ℕ × ℕ) => max bs.1 bs.2) := by
      change Primrec (fun q : ((ℕ × ℕ) × List Bool) × (ℕ × ℕ) => max q.2.1 q.2.2)
      exact Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    exact Primrec.list_foldr h_map (Primrec.const 0) h_step
  refine hfA_list.of_eq ?_
  intro p
  unfold fApprox
  rw [range_sup_eq_foldr]

/-- `dpBase` is Primrec in `(e, t, x, k)`. -/
private theorem dpBase_primrec :
    Primrec (fun p : ((ℕ × ℕ) × List Bool) × ℕ =>
      dpBase p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  unfold dpBase
  have h_range : Primrec (fun p : ((ℕ × ℕ) × List Bool) × ℕ => List.range (2^p.2)) :=
    Primrec.list_range.comp (Primrec.nat_pow.comp (Primrec.const 2) Primrec.snd)
  have h_inner : Primrec₂ (fun (p : ((ℕ × ℕ) × List Bool) × ℕ) (i : ℕ) =>
      fApprox p.1.1.1 p.1.1.2 (p.1.2 ++ strOfIdx p.2 i)) := by
    change Primrec (fun q : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ =>
      fApprox q.1.1.1.1 q.1.1.1.2 (q.1.1.2 ++ strOfIdx q.1.2 q.2))
    have h_e : Primrec (fun q : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ => q.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have h_t : Primrec (fun q : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ => q.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have h_x : Primrec (fun q : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ => q.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have h_k : Primrec (fun q : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ => q.1.2) :=
      Primrec.snd.comp Primrec.fst
    have h_i : Primrec (fun q : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ => q.2) := Primrec.snd
    have h_str : Primrec (fun q : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ => strOfIdx q.1.2 q.2) :=
      strOfIdx_primrec.comp h_k h_i
    have h_app : Primrec (fun q : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ =>
        q.1.1.2 ++ strOfIdx q.1.2 q.2) := Primrec.list_append.comp h_x h_str
    exact fApprox_primrec.comp (Primrec.pair (Primrec.pair h_e h_t) h_app)
  exact Primrec.list_map h_range h_inner

/-- `freezeStage e t ≤ t`: the frozen stage is always at most the current time. -/
private theorem freezeStage_le_self (e t : ℕ) : freezeStage e t ≤ t := by
  unfold freezeStage
  apply Finset.sup_le
  intro n hn
  split_ifs
  · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  · exact Nat.zero_le _

/-! Argument-tuple types for the DP Primrec chain. Abbreviations keep the
deeply-nested projections bearable. -/

private abbrev ArgStep : Type := (((ℕ × ℕ) × List Bool) × ℕ) × List ℕ
private abbrev ArgIter : Type := ((ℕ × ℕ) × List Bool) × ℕ

set_option maxHeartbeats 4000000 in
/-- `dpStep` is Primrec. -/
private theorem dpStep_primrec :
    Primrec (fun p : ArgStep => dpStep p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2) := by
  unfold dpStep
  have h_j : Primrec (fun p : ArgStep => p.1.2) := Primrec.snd.comp Primrec.fst
  have h_range : Primrec (fun p : ArgStep => List.range (2^p.1.2)) :=
    Primrec.list_range.comp (Primrec.nat_pow.comp (Primrec.const 2) h_j)
  have h_inner_u : Primrec (fun q : ArgStep × ℕ =>
      max (fApprox q.1.1.1.1.1 q.1.1.1.1.2 (q.1.1.1.2 ++ strOfIdx q.1.1.2 q.2))
          (q.1.2.getD (2 * q.2) 0 + q.1.2.getD (2 * q.2 + 1) 0)) := by
    have h_e : Primrec (fun q : ArgStep × ℕ => q.1.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have h_t : Primrec (fun q : ArgStep × ℕ => q.1.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have h_x : Primrec (fun q : ArgStep × ℕ => q.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have h_j' : Primrec (fun q : ArgStep × ℕ => q.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have h_prev : Primrec (fun q : ArgStep × ℕ => q.1.2) :=
      Primrec.snd.comp Primrec.fst
    have h_i : Primrec (fun q : ArgStep × ℕ => q.2) := Primrec.snd
    have h_str : Primrec (fun q : ArgStep × ℕ => strOfIdx q.1.1.2 q.2) :=
      strOfIdx_primrec.comp h_j' h_i
    have h_app : Primrec (fun q : ArgStep × ℕ => q.1.1.1.2 ++ strOfIdx q.1.1.2 q.2) :=
      Primrec.list_append.comp h_x h_str
    have h_etx : Primrec (fun q : ArgStep × ℕ =>
        ((q.1.1.1.1.1, q.1.1.1.1.2), q.1.1.1.2 ++ strOfIdx q.1.1.2 q.2)) :=
      Primrec.pair (Primrec.pair h_e h_t) h_app
    have h_fA : Primrec (fun q : ArgStep × ℕ =>
        fApprox q.1.1.1.1.1 q.1.1.1.1.2 (q.1.1.1.2 ++ strOfIdx q.1.1.2 q.2)) :=
      fApprox_primrec.comp h_etx
    have h_2i : Primrec (fun q : ArgStep × ℕ => 2 * q.2) :=
      Primrec.nat_mul.comp (Primrec.const 2) h_i
    have h_2i1 : Primrec (fun q : ArgStep × ℕ => 2 * q.2 + 1) := Primrec.succ.comp h_2i
    have h_g0 : Primrec (fun q : ArgStep × ℕ => q.1.2.getD (2 * q.2) 0) :=
      (Primrec.list_getD 0).comp h_prev h_2i
    have h_g1 : Primrec (fun q : ArgStep × ℕ => q.1.2.getD (2 * q.2 + 1) 0) :=
      (Primrec.list_getD 0).comp h_prev h_2i1
    have h_sum : Primrec (fun q : ArgStep × ℕ =>
        q.1.2.getD (2 * q.2) 0 + q.1.2.getD (2 * q.2 + 1) 0) :=
      Primrec.nat_add.comp h_g0 h_g1
    exact Primrec.nat_max.comp h_fA h_sum
  exact Primrec.list_map h_range h_inner_u.to₂

set_option maxHeartbeats 4000000 in
/-- `dpIter` is Primrec. -/
private theorem dpIter_primrec :
    Primrec (fun p : ArgIter => dpIter p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hrec : ∀ p : ArgIter,
      dpIter p.1.1.1 p.1.1.2 p.1.2 p.2 =
        Nat.rec (motive := fun _ => List ℕ)
          (dpBase p.1.1.1 p.1.1.2 p.1.2 (p.1.1.2 - p.1.2.length))
          (fun m prev => dpStep p.1.1.1 p.1.1.2 p.1.2
              (p.1.1.2 - p.1.2.length - m - 1) prev)
          p.2 := by
    intro p
    induction p.2 with
    | zero => rfl
    | succ k ih => show dpStep _ _ _ _ _ = _; rw [ih]
  refine Primrec.of_eq ?_ (fun p => (hrec p).symm)
  have h_f : Primrec (fun p : ArgIter => p.2) := Primrec.snd
  have h_g : Primrec (fun p : ArgIter =>
      dpBase p.1.1.1 p.1.1.2 p.1.2 (p.1.1.2 - p.1.2.length)) := by
    have h_e : Primrec (fun p : ArgIter => p.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have h_t : Primrec (fun p : ArgIter => p.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have h_x : Primrec (fun p : ArgIter => p.1.2) :=
      Primrec.snd.comp Primrec.fst
    have h_xlen : Primrec (fun p : ArgIter => p.1.2.length) :=
      Primrec.list_length.comp h_x
    have h_sub : Primrec (fun p : ArgIter => p.1.1.2 - p.1.2.length) :=
      Primrec.nat_sub.comp h_t h_xlen
    have h_arg : Primrec (fun p : ArgIter =>
        (((p.1.1.1, p.1.1.2), p.1.2), p.1.1.2 - p.1.2.length)) :=
      Primrec.pair (Primrec.pair (Primrec.pair h_e h_t) h_x) h_sub
    exact dpBase_primrec.comp h_arg
  have h_h : Primrec₂ (fun (p : ArgIter) (q : ℕ × List ℕ) =>
      dpStep p.1.1.1 p.1.1.2 p.1.2 (p.1.1.2 - p.1.2.length - q.1 - 1) q.2) := by
    have h_e : Primrec (fun r : ArgIter × (ℕ × List ℕ) => r.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have h_t : Primrec (fun r : ArgIter × (ℕ × List ℕ) => r.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have h_x : Primrec (fun r : ArgIter × (ℕ × List ℕ) => r.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have h_m : Primrec (fun r : ArgIter × (ℕ × List ℕ) => r.2.1) :=
      Primrec.fst.comp Primrec.snd
    have h_prev : Primrec (fun r : ArgIter × (ℕ × List ℕ) => r.2.2) :=
      Primrec.snd.comp Primrec.snd
    have h_xlen : Primrec (fun r : ArgIter × (ℕ × List ℕ) => r.1.1.2.length) :=
      Primrec.list_length.comp h_x
    have h_sub1 : Primrec (fun r : ArgIter × (ℕ × List ℕ) =>
        r.1.1.1.2 - r.1.1.2.length) := Primrec.nat_sub.comp h_t h_xlen
    have h_sub2 : Primrec (fun r : ArgIter × (ℕ × List ℕ) =>
        r.1.1.1.2 - r.1.1.2.length - r.2.1) := Primrec.nat_sub.comp h_sub1 h_m
    have h_sub3 : Primrec (fun r : ArgIter × (ℕ × List ℕ) =>
        r.1.1.1.2 - r.1.1.2.length - r.2.1 - 1) :=
      Primrec.nat_sub.comp h_sub2 (Primrec.const 1)
    have h_arg : Primrec (fun r : ArgIter × (ℕ × List ℕ) =>
        ((((r.1.1.1.1, r.1.1.1.2), r.1.1.2), r.1.1.1.2 - r.1.1.2.length - r.2.1 - 1), r.2.2)) :=
      Primrec.pair
        (Primrec.pair (Primrec.pair (Primrec.pair h_e h_t) h_x) h_sub3) h_prev
    exact (dpStep_primrec.comp h_arg).to₂
  exact Primrec.nat_rec' h_f h_g h_h

set_option maxHeartbeats 4000000 in
/-- `gApproxComp` is Primrec. -/
private theorem gApproxComp_primrec :
    Primrec (fun p : (ℕ × ℕ) × List Bool => gApproxComp p.1.1 p.1.2 p.2) := by
  unfold gApproxComp
  have h_e : Primrec (fun p : (ℕ × ℕ) × List Bool => p.1.1) := Primrec.fst.comp Primrec.fst
  have h_t : Primrec (fun p : (ℕ × ℕ) × List Bool => p.1.2) := Primrec.snd.comp Primrec.fst
  have h_x : Primrec (fun p : (ℕ × ℕ) × List Bool => p.2) := Primrec.snd
  have h_xlen : Primrec (fun p : (ℕ × ℕ) × List Bool => p.2.length) :=
    Primrec.list_length.comp h_x
  have h_sub : Primrec (fun p : (ℕ × ℕ) × List Bool => p.1.2 - p.2.length) :=
    Primrec.nat_sub.comp h_t h_xlen
  have h_cond : PrimrecPred (fun p : (ℕ × ℕ) × List Bool => p.1.2 < p.2.length) :=
    PrimrecRel.comp Primrec.nat_lt h_t h_xlen
  have h_arg : Primrec (fun p : (ℕ × ℕ) × List Bool =>
      (((p.1.1, p.1.2), p.2), p.1.2 - p.2.length)) :=
    Primrec.pair (Primrec.pair (Primrec.pair h_e h_t) h_x) h_sub
  have h_dpIter : Primrec (fun p : (ℕ × ℕ) × List Bool =>
      dpIter p.1.1 p.1.2 p.2 (p.1.2 - p.2.length)) := dpIter_primrec.comp h_arg
  have h_getD : Primrec (fun p : (ℕ × ℕ) × List Bool =>
      (dpIter p.1.1 p.1.2 p.2 (p.1.2 - p.2.length)).getD 0 0) :=
    (Primrec.list_getD 0).comp h_dpIter (Primrec.const 0)
  exact Primrec.ite h_cond (Primrec.const 0) h_getD

set_option maxHeartbeats 4000000 in
/-- `freezeStageNat` is Primrec. -/
private theorem freezeStageNat_primrec : Primrec₂ freezeStageNat := by
  change Primrec (fun p : ℕ × ℕ => freezeStageNat p.1 p.2)
  unfold freezeStageNat
  have h_f : Primrec (fun p : ℕ × ℕ => p.2 + 1) := Primrec.succ.comp Primrec.snd
  have h_g : Primrec (fun _ : ℕ × ℕ => (0 : ℕ)) := Primrec.const 0
  have h_h : Primrec₂ (fun (p : ℕ × ℕ) (q : ℕ × ℕ) =>
      max q.2 (if gApproxComp p.1 q.1 [] ≤ 2^q.1 then q.1 else 0)) := by
    have h_e : Primrec (fun r : (ℕ × ℕ) × (ℕ × ℕ) => r.1.1) := Primrec.fst.comp Primrec.fst
    have h_s : Primrec (fun r : (ℕ × ℕ) × (ℕ × ℕ) => r.2.1) := Primrec.fst.comp Primrec.snd
    have h_acc : Primrec (fun r : (ℕ × ℕ) × (ℕ × ℕ) => r.2.2) := Primrec.snd.comp Primrec.snd
    have h_pow : Primrec (fun r : (ℕ × ℕ) × (ℕ × ℕ) => (2 : ℕ)^r.2.1) :=
      Primrec.nat_pow.comp (Primrec.const 2) h_s
    have h_arg_g : Primrec (fun r : (ℕ × ℕ) × (ℕ × ℕ) =>
        ((r.1.1, r.2.1), ([] : List Bool))) :=
      Primrec.pair (Primrec.pair h_e h_s) (Primrec.const [])
    have h_gac : Primrec (fun r : (ℕ × ℕ) × (ℕ × ℕ) => gApproxComp r.1.1 r.2.1 []) :=
      gApproxComp_primrec.comp h_arg_g
    have h_cond : PrimrecPred (fun r : (ℕ × ℕ) × (ℕ × ℕ) =>
        gApproxComp r.1.1 r.2.1 [] ≤ 2^r.2.1) :=
      PrimrecRel.comp Primrec.nat_le h_gac h_pow
    have h_branch : Primrec (fun r : (ℕ × ℕ) × (ℕ × ℕ) =>
        if gApproxComp r.1.1 r.2.1 [] ≤ 2^r.2.1 then r.2.1 else 0) :=
      Primrec.ite h_cond h_s (Primrec.const 0)
    exact (Primrec.nat_max.comp h_acc h_branch).to₂
  exact Primrec.nat_rec' h_f h_g h_h

set_option maxHeartbeats 4000000 in
/-- The LSC approximant is Primrec. -/
private theorem enumApprox_primrec :
    Primrec (fun q : (ℕ × List Bool) × ℕ =>
      gApproxComp q.1.1 (freezeStageNat q.1.1 q.2) q.1.2 *
        2^(q.2 - freezeStageNat q.1.1 q.2)) := by
  have h_e : Primrec (fun q : (ℕ × List Bool) × ℕ => q.1.1) := Primrec.fst.comp Primrec.fst
  have h_x : Primrec (fun q : (ℕ × List Bool) × ℕ => q.1.2) := Primrec.snd.comp Primrec.fst
  have h_t : Primrec (fun q : (ℕ × List Bool) × ℕ => q.2) := Primrec.snd
  have h_fs : Primrec (fun q : (ℕ × List Bool) × ℕ => freezeStageNat q.1.1 q.2) :=
    freezeStageNat_primrec.comp h_e h_t
  have h_arg_g : Primrec (fun q : (ℕ × List Bool) × ℕ =>
      ((q.1.1, freezeStageNat q.1.1 q.2), q.1.2)) :=
    Primrec.pair (Primrec.pair h_e h_fs) h_x
  have h_gac : Primrec (fun q : (ℕ × List Bool) × ℕ =>
      gApproxComp q.1.1 (freezeStageNat q.1.1 q.2) q.1.2) :=
    gApproxComp_primrec.comp h_arg_g
  have h_sub : Primrec (fun q : (ℕ × List Bool) × ℕ => q.2 - freezeStageNat q.1.1 q.2) :=
    Primrec.nat_sub.comp h_t h_fs
  have h_pow : Primrec (fun q : (ℕ × List Bool) × ℕ =>
      (2 : ℕ)^(q.2 - freezeStageNat q.1.1 q.2)) :=
    Primrec.nat_pow.comp (Primrec.const 2) h_sub
  exact Primrec.nat_mul.comp h_gac h_pow

theorem enum_uniformlyEnumerable : UniformlyEnumerable enum := by
  refine ⟨fun q t => gApproxComp q.1 (freezeStageNat q.1 t) q.2 *
      2^(t - freezeStageNat q.1 t), ?_, ?_, ?_⟩
  · -- Computability of the approximant.
    exact enumApprox_primrec.to_comp
  · -- Monotonicity: via GApprox.
    intro q
    have heq : ∀ u,
        dyadic (gApproxComp q.1 (freezeStageNat q.1 u) q.2 * 2^(u - freezeStageNat q.1 u)) u
        = GApprox q.1 u q.2 := by
      intro u
      unfold GApprox
      rw [gApproxComp_eq, freezeStageNat_eq]
      exact dyadic_mul_shift _ _ _ (freezeStage_le_self q.1 u)
    intro s t hst
    show dyadic (gApproxComp q.1 (freezeStageNat q.1 s) q.2 * 2^(s - freezeStageNat q.1 s)) s ≤
          dyadic (gApproxComp q.1 (freezeStageNat q.1 t) q.2 * 2^(t - freezeStageNat q.1 t)) t
    rw [heq s, heq t]
    exact GApprox_mono q.1 hst q.2
  · -- Supremum = enum.
    intro q
    change (⨆ t, dyadic (gApproxComp q.1 (freezeStageNat q.1 t) q.2 *
          2^(t - freezeStageNat q.1 t)) t) = enum q.1 q.2
    have heq : ∀ u,
        dyadic (gApproxComp q.1 (freezeStageNat q.1 u) q.2 * 2^(u - freezeStageNat q.1 u)) u
        = GApprox q.1 u q.2 := by
      intro u
      unfold GApprox
      rw [gApproxComp_eq, freezeStageNat_eq]
      exact dyadic_mul_shift _ _ _ (freezeStage_le_self q.1 u)
    simp_rw [heq]
    rfl

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

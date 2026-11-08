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
  sorry

/-- (b) `fApprox` is dominated by `gApprox` pointwise at the same stage. -/
theorem fApprox_le_gApprox (e t : ℕ) (x : List Bool) :
    fApprox e t x ≤ gApprox e t x := by
  sorry

/-- (c) `gApprox` is monotone in `t`, comparing level-`t` vs level-`t+1` dyadic
readings. The numerator grows by *at least* a factor of 2. -/
theorem gApprox_mono_step (e t : ℕ) (x : List Bool) :
    2 * gApprox e t x ≤ gApprox e (t + 1) x := by
  sorry

/-- (d) Minimality: if a semimeasure `μ` dominates the level-`t` `fApprox`, it
dominates the level-`t` `gApprox`. Here "dominates at level `t`" is
`dyadic (· ) t ≤ μ x`. Used in completeness. -/
theorem gApprox_le_of_fApprox_le {e t : ℕ} (μ : Semimeasure)
    (hf : ∀ x, dyadic (fApprox e t x) t ≤ μ x) (x : List Bool) :
    dyadic (gApprox e t x) t ≤ μ x := by
  sorry

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

import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lower semicomputability and semimeasures

Building toward `thm:enums-of-ums=ums` ("HSI = SolInd", see
`hsi-solind-paper/arXiv version 1.tex`).

## Why dyadic approximants rather than `ℚ`

An earlier draft asked for a computable `α → ℕ → ℚ`. That cannot be
discharged. Mathlib's computability library has no arithmetic lemmas for `ℚ`
at all — nothing in `Computability/` so much as mentions `Rat`, there is no
`Computable.add`, and the only addition lemma is
`Primrec.nat_add : Primrec₂ ((· + ·) : ℕ → ℕ → ℕ)`. `Primcodable ℚ` exists
only via the opaque `ofDenumerable` bijection, which supplies an encoding but
no primitive-recursive arithmetic through it.

So approximants here are dyadic rationals `k / 2 ^ n`, carried as a plain `ℕ`
numerator with the sequence index doubling as the exponent. Approximant
addition is then literally `ℕ` addition. This is also the standard
presentation of enumerability in AIT, so nothing is given up.

## Why `ℝ≥0∞` and `⨆` rather than `ℝ` and `Tendsto`

Semimeasures are non-negative and want `tsum`, so `ℝ≥0∞` is the natural value
type. It is also a complete lattice, so "monotone approximation from below"
is expressible directly as a supremum — no topology, and no side conditions
about `∞` of the kind `ENNReal`'s limit lemmas carry.
-/

open ENNReal

variable {α : Type*} [Primcodable α]

/-- The value of the `n`-th approximant: numerator `k` over `2 ^ n`. -/
noncomputable def dyadic (k n : ℕ) : ℝ≥0∞ := (k : ℝ≥0∞) / 2 ^ n

theorem dyadic_add (k l n : ℕ) : dyadic (k + l) n = dyadic k n + dyadic l n := by
  simp [dyadic, ENNReal.add_div]

/-- `f` is lower semicomputable: it is the supremum of a computable monotone
sequence of dyadic rationals. This is the standard AIT definition (cf. WSH
Def 8 / semimeasure enumerability), phrased directly rather than via a
computable-reals typeclass, since Mathlib has no integrated computable-reals
library to build on. -/
def LowerSemicomputable (f : α → ℝ≥0∞) : Prop :=
  ∃ φ : α → ℕ → ℕ,
    Computable (fun p : α × ℕ => φ p.1 p.2) ∧
    (∀ a, Monotone fun n => dyadic (φ a n) n) ∧
    (∀ a, ⨆ n, dyadic (φ a n) n = f a)

/-- Lower-semicomputable functions are closed under pointwise addition.

This is the fact "lsc survives addition, not subtraction" that the paper's
safe-peel construction depends on. Subtraction has no analogous theorem — an
approximation-from-below of `f` minus an approximation-from-below of `g` is
NOT an approximation from below of `f - g`, which is exactly why the naive
greedy weight-assignment approach in the thesis failed. -/
theorem LowerSemicomputable.add {f g : α → ℝ≥0∞}
    (hf : LowerSemicomputable f) (hg : LowerSemicomputable g) :
    LowerSemicomputable (fun a => f a + g a) := by
  obtain ⟨φ, hφ_comp, hφ_mono, hφ_sup⟩ := hf
  obtain ⟨ψ, hψ_comp, hψ_mono, hψ_sup⟩ := hg
  refine ⟨fun a n => φ a n + ψ a n, ?_, ?_, ?_⟩
  · exact Primrec.nat_add.to_comp.comp hφ_comp hψ_comp
  · intro a
    simp only [dyadic_add]
    exact (hφ_mono a).add (hψ_mono a)
  · intro a
    simp only [dyadic_add]
    rw [← ENNReal.iSup_add_iSup_of_monotone (hφ_mono a) (hψ_mono a), hφ_sup a, hψ_sup a]

/-- A positive lower-semicomputable value has a *positive dyadic* below it.

This is the paper's δ-step: "compute `w^{(ξ)}(i_c^{(ξ)})` from below to find some
positive rational `q ≤ w^{(ξ)}(i_c^{(ξ)})`". Only existence is needed, never a
procedure — which is why the non-constructivity the paper notes costs nothing
here. -/
theorem LowerSemicomputable.exists_pos_approx {f : α → ℝ≥0∞}
    (hf : LowerSemicomputable f) {a : α} (ha : 0 < f a) :
    ∃ k n : ℕ, 0 < dyadic k n ∧ dyadic k n ≤ f a := by
  obtain ⟨φ, _, _, hsup⟩ := hf
  rw [← hsup a, lt_iSup_iff] at ha
  obtain ⟨n, hn⟩ := ha
  exact ⟨φ a n, n, hn, hsup a ▸ le_iSup (fun m => dyadic (φ a m) m) n⟩

/-- A semimeasure on binary strings, in the cylinder/monotone-TM sense used in
the paper's Preliminaries: total mass at most one, and mass is not created
when extending a string (`μ x ≥ μ (x0) + μ (x1)`, with equality for a proper
measure). -/
structure Semimeasure where
  /-- The underlying mass function on binary strings. -/
  toFun : List Bool → ℝ≥0∞
  /-- Total mass is at most one. -/
  empty_le_one : toFun [] ≤ 1
  /-- Extending a string does not create mass. -/
  extend_le : ∀ x, toFun (x ++ [false]) + toFun (x ++ [true]) ≤ toFun x

namespace Semimeasure

instance : CoeFun Semimeasure (fun _ => List Bool → ℝ≥0∞) := ⟨toFun⟩

/-- Semimeasures are determined by their mass function. Needed throughout: the
spine theorem's "`ξ` appears in `ν` at index `i`" steps are equalities of
semimeasures, established pointwise. -/
@[ext]
theorem ext {μ ν : Semimeasure} (h : ∀ x, μ x = ν x) : μ = ν := by
  cases μ; cases ν; congr 1; exact funext h

/-- Mass is non-increasing along any single extension. -/
theorem le_of_extend (μ : Semimeasure) (x : List Bool) (b : Bool) :
    μ (x ++ [b]) ≤ μ x := by
  have h := μ.extend_le x
  cases b
  · exact le_trans le_self_add h
  · exact le_trans le_add_self h

/-- `μ` is *enumerable*: lower-semicomputable as a function on binary strings.
`WSH`'s class `ℳ` is the collection of these. -/
def Enumerable (μ : Semimeasure) : Prop := LowerSemicomputable μ.toFun

end Semimeasure

/-- A weight function for a mixture: lower-semicomputable, strictly positive on
every index, with total weight at most one. These are the `w^{(c)}` of
`thm:enums-of-ums=ums`. -/
structure Weights where
  /-- The weight assigned to each index. -/
  toFun : ℕ → ℝ≥0∞
  /-- Weights are lower-semicomputable. -/
  lsc : LowerSemicomputable toFun
  /-- Every index gets strictly positive weight. -/
  pos : ∀ i, 0 < toFun i
  /-- Total weight is at most one. -/
  tsum_le_one : ∑' i, toFun i ≤ 1

instance : CoeFun Weights (fun _ => ℕ → ℝ≥0∞) := ⟨Weights.toFun⟩

/-- The mixture of a family of semimeasures under a weight function. -/
noncomputable def mixtureFun (ν : ℕ → Semimeasure) (w : Weights) :
    List Bool → ℝ≥0∞ :=
  fun x => ∑' i, w i * ν i x

/-- A weighted mixture of semimeasures is itself a semimeasure. This is what
lets the paper treat `Ξ`, `ξ` and `P_Η` as objects of the same kind as their
components, and so is the first thing the spine theorem needs. -/
noncomputable def mixture (ν : ℕ → Semimeasure) (w : Weights) : Semimeasure where
  toFun := mixtureFun ν w
  empty_le_one := by
    refine le_trans (ENNReal.tsum_le_tsum fun i => ?_) w.tsum_le_one
    calc w i * ν i [] ≤ w i * 1 := by gcongr; exact (ν i).empty_le_one
      _ = w i := mul_one _
  extend_le := by
    intro x
    show mixtureFun ν w (x ++ [false]) + mixtureFun ν w (x ++ [true]) ≤ mixtureFun ν w x
    unfold mixtureFun
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [← mul_add]
    gcongr
    exact (ν i).extend_le x

@[simp]
theorem mixture_apply (ν : ℕ → Semimeasure) (w : Weights) (x : List Bool) :
    mixture ν w x = ∑' i, w i * ν i x := rfl

/-- Every weighted component is dominated by the mixture. This is the seed of
the paper's error bounds: `P_Η(X) > Η(U_μ) P_{U_μ}(X)` at `eq:hsi-error-bound`
is exactly this inequality. -/
theorem le_mixture (ν : ℕ → Semimeasure) (w : Weights) (i : ℕ) (x : List Bool) :
    w i * ν i x ≤ mixture ν w x :=
  ENNReal.le_tsum i

/-- `ξ` is a *universal mixture* (WSH Def 8): a mixture, with lower-semicomputable
weights, over an enumeration containing *every* enumerable semimeasure. -/
def IsUniversalMixture (ξ : Semimeasure) : Prop :=
  ∃ (ν : ℕ → Semimeasure) (w : Weights),
    (∀ i, (ν i).Enumerable) ∧
    (∀ μ : Semimeasure, μ.Enumerable → ∃ i, ν i = μ) ∧
    ξ = mixture ν w

/-- An enumeration in which every universal mixture appears. This is the
hypothesis on `{ν_i}` in `thm:enums-of-ums=ums` — note it is *weaker* than
containing every enumerable semimeasure. -/
def ContainsAllUniversalMixtures (ν : ℕ → Semimeasure) : Prop :=
  ∀ ξ : Semimeasure, IsUniversalMixture ξ → ∃ i, ν i = ξ

/-- The class `𝒞_ν` of `thm:enums-of-ums=ums`: everything obtainable from the
enumeration `ν` by some admissible weighting. -/
def MixtureClass (ν : ℕ → Semimeasure) : Set Semimeasure :=
  {c | ∃ w : Weights, c = mixture ν w}

/-- `Primrec₂` form of `Nat.Primrec.pow`, which Mathlib only states in the
raw `Nat.Primrec` form. -/
theorem Primrec.nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The approximant used for the geometric weights: `2 ^ n / 2 ^ (i+1)` in `ℕ`,
which is `0` until `n` reaches `i+1` and then holds the value `2 ^ -(i+1)`
exactly. Truncated `ℕ` division is doing the work of the `if`. -/
theorem dyadic_geometric (i n : ℕ) :
    dyadic (2 ^ n / 2 ^ (i + 1)) n = if i + 1 ≤ n then (2 : ℝ≥0∞)⁻¹ ^ (i + 1) else 0 := by
  split_ifs with h
  · rw [Nat.pow_div h (by norm_num)]
    have hsplit : n = (n - (i + 1)) + (i + 1) := by omega
    have h0 : ((2 : ℝ≥0∞) ^ (n - (i + 1))) ≠ 0 := by simp
    have ht : ((2 : ℝ≥0∞) ^ (n - (i + 1))) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
    rw [dyadic, ← ENNReal.inv_pow]
    rw [show ((2 ^ (n - (i + 1)) : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (n - (i + 1)) by push_cast; ring]
    rw [show ((2 : ℝ≥0∞) ^ n) = 2 ^ (n - (i + 1)) * 2 ^ (i + 1) by rw [← pow_add, ← hsplit]]
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), ← mul_assoc,
      ENNReal.mul_inv_cancel h0 ht, one_mul]
  · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)), dyadic]
    simp

/-- Geometric weights `w i = 2 ^ -(i+1)`. Nathan's construction: enumerate, then
weight the `i`-th item `2 ^ -i`. Enough for existence, which is all the spine
theorem needs. -/
noncomputable def geometricWeights : Weights where
  toFun := fun i => (2 : ℝ≥0∞)⁻¹ ^ (i + 1)
  lsc := by
    refine ⟨fun i n => 2 ^ n / 2 ^ (i + 1), ?_, ?_, ?_⟩
    · exact (Primrec.nat_div.comp
        (Primrec.nat_pow.comp (Primrec.const 2) Primrec.snd)
        (Primrec.nat_pow.comp (Primrec.const 2)
          (Primrec.succ.comp Primrec.fst))).to_comp
    · intro i m n hmn
      simp only [dyadic_geometric]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · omega
      · simp
      · exact le_rfl
    · intro i
      simp only [dyadic_geometric]
      refine le_antisymm (iSup_le fun n => ?_) ?_
      · split_ifs
        · exact le_rfl
        · simp
      · exact le_of_eq_of_le (by simp) (le_iSup (fun n => if i + 1 ≤ n then (2 : ℝ≥0∞)⁻¹ ^ (i + 1) else 0) (i + 1))
  pos := fun i => pos_iff_ne_zero.mpr (by simp)
  tsum_le_one := by
    rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
    rw [ENNReal.inv_mul_cancel (by norm_num) (by finiteness)]

/-- The external input the spine theorem needs, isolated in one place: an
effective enumeration of *all* enumerable semimeasures. This is Wood et al.'s
Lemma 6 territory, and is assumed rather than proved — building it means
building the machine mechanics this development deliberately avoids.

Keeping it a structure rather than an `axiom` means every result that depends
on it says so in its own statement, so what has actually been established stays
auditable. -/
structure WoodInterface where
  /-- The enumeration. -/
  enum : ℕ → Semimeasure
  /-- Every listed semimeasure is enumerable. -/
  enum_enumerable : ∀ i, (enum i).Enumerable
  /-- Every enumerable semimeasure is listed. -/
  enum_complete : ∀ μ : Semimeasure, μ.Enumerable → ∃ i, enum i = μ

/-- Universal mixtures exist. Given the enumeration, this is exactly Nathan's
argument: weight the `i`-th entry by `2 ^ -i`, which sums to `1`. -/
theorem WoodInterface.exists_universalMixture (W : WoodInterface) :
    ∃ ξ : Semimeasure, IsUniversalMixture ξ :=
  ⟨mixture W.enum geometricWeights,
    W.enum, geometricWeights, W.enum_enumerable, W.enum_complete, rfl⟩

/-- **The spine theorem**, `thm:enums-of-ums=ums`: for any enumeration of
enumerable semimeasures containing every universal mixture, the class of
mixtures over it is exactly the class of universal mixtures.

Everything the paper's equality side rests on collapses out of this —
`cor:hsi-domain-equivalence`, `cor:um=umum=solind=hsi`, and so HSI = SolInd.

NOT YET PROVED. See the note below on what it needs. -/
theorem mixtureClass_eq_universalMixtures
    (ν : ℕ → Semimeasure)
    (hν_enum : ∀ i, (ν i).Enumerable)
    (hν_univ : ContainsAllUniversalMixtures ν) :
    MixtureClass ν = {ξ | IsUniversalMixture ξ} := by
  sorry

/-
TODO, roughly in dependency order.

NOTE ON SCOPE (2026-08-02): an earlier draft of this list had `UniversalTM`
(emulation sense, via Mathlib's TM2) as a step. That step is deleted.
Mathlib has Turing-machine definitions but no universal-machine construction,
and building a monotone UTM with the emulation property is a known-hard
formalisation project — it would consume the entire effort.

It is also unnecessary. `thm:enums-of-ums=ums` never mentions Turing
machines: it quantifies over enumerations of enumerable semimeasures and
lower-semicomputable weight functions. TMs enter the paper only through Wood
et al.'s Lemma 6 (TMs ↔ enumerable semimeasures), which is their theorem, not
ours. Take that correspondence as a hypothesis/interface and the machine
mechanics never arise.

1. Weight functions: `w : ℕ → ℝ≥0∞` lower-semicomputable, strictly positive,
   with `∑' i, w i ≤ 1`. Then `Mixture ν w := fun x => ∑' i, w i * ν i x`,
   and the fact that a mixture of semimeasures is a semimeasure.
2. `UniversalMixture` (WSH Def 8): a mixture over an enumeration containing
   every enumerable semimeasure.
3. The spine theorem `thm:enums-of-ums=ums`: index-chasing, the δ-split
   reweighting, and `tsum` bookkeeping. The proof is non-constructive — the
   positive rational `q` below `w^{(ξ)}(i_c^{(ξ)})` only needs to exist, which
   is free in classical Lean.
-/

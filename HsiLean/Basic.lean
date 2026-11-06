import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lower semicomputability and semimeasures

Building toward `thm:enums-of-ums=ums` ("HSI = SolInd", see
`hsi-solind-paper/arXiv version 1.tex`; current version:
`Documents\PIBBSS\hsi\alt2027-template\ALT format.tex`, theorem at L416–443).

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

/-- Halving a dyadic increments the exponent: `dyadic k n / 2 = dyadic k (n+1)`. -/
theorem dyadic_div_two (k n : ℕ) : dyadic k n / 2 = dyadic k (n + 1) := by
  unfold dyadic
  have h0 : (2 : ℝ≥0∞)^n ≠ 0 := by positivity
  have ht : (2 : ℝ≥0∞)^n ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  simp only [div_eq_mul_inv, pow_succ, mul_assoc]
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl ht)]

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

/-- `ν` is an *effective* enumeration of enumerable semimeasures: one computable
procedure approximates `ν i x` from below for every index `i` and string `x`
at once. This is the standard AIT meaning of "an enumeration of enumerable
semimeasures".

The pointwise version (`∀ i, (ν i).Enumerable`) is too weak: there are
uncountably many non-effective enumerations, and a mixture over one need not be
lower-semicomputable. The spine theorem's `⊇` direction needs the mixture `c`
over `ν` to be enumerable (so that it appears in `ξ`'s own enumeration), and
that requires this uniform version. (Nathan's decision, 2026-11-05, after the
2026-11-04 agent run.) -/
def UniformlyEnumerable (ν : ℕ → Semimeasure) : Prop :=
  LowerSemicomputable (fun p : ℕ × List Bool => ν p.1 p.2)

/-- `ξ` is a *universal mixture* (WSH Def 8): a mixture, with lower-semicomputable
weights, over an *effective* enumeration containing *every* enumerable
semimeasure. -/
def IsUniversalMixture (ξ : Semimeasure) : Prop :=
  ∃ (ν : ℕ → Semimeasure) (w : Weights),
    UniformlyEnumerable ν ∧
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
  /-- The listing is effective: uniformly lower-semicomputable in index and string. -/
  enum_enumerable : UniformlyEnumerable enum
  /-- Every enumerable semimeasure is listed. -/
  enum_complete : ∀ μ : Semimeasure, μ.Enumerable → ∃ i, enum i = μ

/-- Universal mixtures exist. Given the enumeration, this is exactly Nathan's
argument: weight the `i`-th entry by `2 ^ -i`, which sums to `1`. -/
theorem WoodInterface.exists_universalMixture (W : WoodInterface) :
    ∃ ξ : Semimeasure, IsUniversalMixture ξ :=
  ⟨mixture W.enum geometricWeights,
    W.enum, geometricWeights, W.enum_enumerable, W.enum_complete, rfl⟩

/-! ### LSC closure lemmas used by the spine theorem

These isolate the three computability facts the δ-construction needs:
* a mixture over a uniformly enumerable family is enumerable (so that `c` can
  appear in `ξ`'s own enumeration — the 2026-11-05 hinge);
* LSC is closed under scaling by a dyadic constant and under adding a
  dyadic bump at a single index (the δ-reweighting).

These three facts are standard effectivity closures; they are isolated here so
the mathematical structure of the spine theorem stays visible. -/

/-- The approximant function witnessing LSC of a mixture: at stage `k`, use the
`(k/2)`-level approximations of both the weights and the semimeasure family,
summing the first `k/2` terms, then lift from level `2*(k/2)` to level `k`. -/
private noncomputable def mixtureApprox
    (φ_w : ℕ → ℕ → ℕ) (φ_ν : ℕ × List Bool → ℕ → ℕ)
    (x : List Bool) (k : ℕ) : ℕ :=
  let m := k / 2
  let s := (List.range m).foldr (fun i acc => acc + φ_w i m * φ_ν (i, x) m) 0
  s * 2 ^ (k - 2 * m)

/-- Mixture over a uniformly enumerable family (with LSC weights) is enumerable.
Needed by the ⊇ direction: the witness mixture `c := mixture ν geometricWeights`
has to be enumerable so it appears in `ξ`'s own enumeration. -/
theorem UniformlyEnumerable.mixture_enumerable
    {ν : ℕ → Semimeasure} (hν : UniformlyEnumerable ν) (w : Weights) :
    (mixture ν w).Enumerable := by
  sorry

/-- Auxiliary: `dyadic (a * k) (b + n) = dyadic a b * dyadic k n`. -/
private theorem dyadic_mul_add (a b k n : ℕ) :
    dyadic (a * k) (b + n) = dyadic a b * dyadic k n := by
  simp only [dyadic, pow_add, Nat.cast_mul, div_eq_mul_inv]
  have hBN : ((2 : ℝ≥0∞) ^ b * (2 : ℝ≥0∞) ^ n)⁻¹ =
      ((2 : ℝ≥0∞) ^ b)⁻¹ * ((2 : ℝ≥0∞) ^ n)⁻¹ :=
    ENNReal.mul_inv (Or.inl (pow_ne_zero b (by norm_num)))
                    (Or.inl (ENNReal.pow_ne_top (by norm_num)))
  rw [hBN]; ac_rfl

/-- Auxiliary: `if b ≤ n then g (n - b) else 0` has the same iSup as `g`. -/
private theorem iSup_shift (b : ℕ) (g : ℕ → ℝ≥0∞) :
    ⨆ n, (if b ≤ n then g (n - b) else 0) = ⨆ k, g k := by
  apply le_antisymm
  · apply iSup_le; intro n
    split_ifs with h
    · exact le_iSup g (n - b)
    · exact bot_le
  · apply iSup_le; intro k
    have hbkb : b ≤ k + b := Nat.le_add_left b k
    have hkbb : k + b - b = k := by omega
    have key := le_iSup (fun n => if b ≤ n then g (n - b) else 0) (k + b)
    rw [if_pos hbkb, hkbb] at key
    exact key

/-- LSC on `ℕ → ℝ≥0∞` is closed under scaling by a dyadic constant.

Approximant: `fun i n => if b ≤ n then a * φ i (n - b) else 0`.
At level n with b ≤ n: `dyadic (a * φ i (n-b)) n = dyadic a b * dyadic (φ i (n-b)) (n-b)`. -/
theorem LowerSemicomputable.dyadic_mul {f : ℕ → ℝ≥0∞}
    (hf : LowerSemicomputable f) (a b : ℕ) :
    LowerSemicomputable (fun i => dyadic a b * f i) := by
  obtain ⟨φ, hφ_comp, hφ_mono, hφ_sup⟩ := hf
  refine ⟨fun i n => if b ≤ n then a * φ i (n - b) else 0, ?_, ?_, ?_⟩
  · -- Computability: standard Primrec/Computable construction.
    have h_cond : Computable (fun p : ℕ × ℕ => decide (b ≤ p.2)) :=
      (Primrec.nat_le.decide.comp (Primrec.const b) Primrec.snd).to_comp
    have h_phi : Computable (fun p : ℕ × ℕ => φ p.1 (p.2 - b)) :=
      hφ_comp.comp (Computable.pair Computable.fst
        (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const b)))
    have h_then : Computable (fun p : ℕ × ℕ => a * φ p.1 (p.2 - b)) :=
      Primrec.nat_mul.to_comp.comp (Computable.const a) h_phi
    exact (Computable.cond h_cond h_then (Computable.const 0)).of_eq
      fun p => by simp [Bool.cond_decide]
  · -- Monotonicity
    intro i m n hmn
    simp only
    by_cases hm : b ≤ m
    · have hn : b ≤ n := hm.trans hmn
      simp only [if_pos hm, if_pos hn]
      have hmn' : m - b ≤ n - b := Nat.sub_le_sub_right hmn b
      have key : ∀ k, b ≤ k → dyadic (a * φ i (k - b)) k =
          dyadic a b * dyadic (φ i (k - b)) (k - b) := fun k hk => by
        set km := k - b with hkm_def
        rw [show k = b + km from (Nat.add_sub_cancel' hk).symm, dyadic_mul_add]
      rw [key m hm, key n hn]
      gcongr
      exact hφ_mono i hmn'
    · by_cases hn : b ≤ n
      · simp only [if_neg hm, if_pos hn]
        simp [dyadic]
      · simp only [if_neg hm, if_neg hn]
        simp [dyadic]
  · -- Supremum
    intro i
    have key : ∀ n, dyadic (if b ≤ n then a * φ i (n - b) else 0) n =
        if b ≤ n then dyadic a b * dyadic (φ i (n - b)) (n - b) else 0 := fun n => by
      by_cases h : b ≤ n
      · simp only [if_pos h]
        set nm := n - b with hnm_def
        rw [show n = b + nm from (Nat.add_sub_cancel' h).symm, dyadic_mul_add]
      · simp [if_neg h, dyadic]
    simp_rw [key]
    have factor : ∀ n, (if b ≤ n then dyadic a b * dyadic (φ i (n - b)) (n - b) else 0) =
                       dyadic a b * (if b ≤ n then dyadic (φ i (n - b)) (n - b) else 0) :=
      fun n => by split_ifs with h <;> simp [mul_zero]
    simp_rw [factor]
    rw [← ENNReal.mul_iSup]
    congr 1
    exact (iSup_shift b (fun k => dyadic (φ i k) k)).trans (hφ_sup i)

/-- Auxiliary: the constant indicator function `fun i => if i = i₀ then c else 0` is LSC. -/
private theorem lsc_indicator_const (i₀ a b : ℕ) :
    LowerSemicomputable (fun i => if i = i₀ then dyadic a b else 0) := by
  refine ⟨fun i n => if i = i₀ ∧ b ≤ n then a * 2^(n - b) else 0, ?_, ?_, ?_⟩
  · -- Computability: i = i₀ and b ≤ n are decidable; a * 2^(n-b) is Primrec.
    have h_eq : PrimrecPred (fun p : ℕ × ℕ => p.1 = i₀) :=
      (Primrec.eq.decide.comp Primrec.fst (Primrec.const i₀)).primrecPred
    have h_le : PrimrecPred (fun p : ℕ × ℕ => b ≤ p.2) :=
      (Primrec.nat_le.decide.comp (Primrec.const b) Primrec.snd).primrecPred
    have h_cond : Computable (fun p : ℕ × ℕ => decide (p.1 = i₀ ∧ b ≤ p.2)) :=
      (h_eq.and h_le).decide.to_comp
    have h_then : Computable (fun p : ℕ × ℕ => a * 2 ^ (p.2 - b)) :=
      Primrec.nat_mul.to_comp.comp (Computable.const a)
        (Primrec.nat_pow.to_comp.comp (Computable.const 2)
          (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const b)))
    exact (Computable.cond h_cond h_then (Computable.const 0)).of_eq
      fun p => by simp [Bool.cond_decide]
  · -- Monotonicity
    intro i m n hmn
    simp only
    by_cases hi : i = i₀
    · by_cases hm : b ≤ m
      · have hn : b ≤ n := hm.trans hmn
        simp only [if_pos (And.intro hi hm), if_pos (And.intro hi hn)]
        have hval : ∀ k, b ≤ k → dyadic (a * 2^(k - b)) k = dyadic a b := fun k hk => by
          set km := k - b with hkm_def
          rw [show k = b + km from (Nat.add_sub_cancel' hk).symm, dyadic_mul_add]
          have hne0 : (2 : ℝ≥0∞) ^ km ≠ 0 := pow_ne_zero km (by norm_num)
          have hnetop : (2 : ℝ≥0∞) ^ km ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
          simp only [dyadic, Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_self hne0 hnetop, mul_one]
        rw [hval m hm, hval n hn]
      · by_cases hn : b ≤ n
        · simp only [if_neg (show ¬(i = i₀ ∧ b ≤ m) from fun ⟨_, h⟩ => hm h),
                     if_pos (And.intro hi hn)]
          simp [dyadic]
        · simp only [if_neg (show ¬(i = i₀ ∧ b ≤ m) from fun ⟨_, h⟩ => hm h),
                     if_neg (show ¬(i = i₀ ∧ b ≤ n) from fun ⟨_, h⟩ => hn h)]
          simp [dyadic]
    · simp only [if_neg (show ¬(i = i₀ ∧ b ≤ m) from fun ⟨h, _⟩ => hi h),
                 if_neg (show ¬(i = i₀ ∧ b ≤ n) from fun ⟨h, _⟩ => hi h)]
      simp [dyadic]
  · -- Supremum
    intro i
    by_cases hi : i = i₀
    · simp only [hi, true_and, if_true]
      have hval : ∀ k, b ≤ k → dyadic (a * 2^(k-b)) k = dyadic a b := fun k hk => by
        set km := k - b with hkm_def
        rw [show k = b + km from (Nat.add_sub_cancel' hk).symm, dyadic_mul_add]
        have hne0 : (2 : ℝ≥0∞) ^ km ≠ 0 := pow_ne_zero km (by norm_num)
        have hnetop : (2 : ℝ≥0∞) ^ km ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
        simp only [dyadic, Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_self hne0 hnetop, mul_one]
      apply le_antisymm
      · apply iSup_le; intro n
        by_cases hbn : b ≤ n
        · simp only [if_pos hbn, hval n hbn, le_refl]
        · simp [if_neg hbn, dyadic]
      · apply le_iSup_of_le b
        simp only [if_true, hval b (le_refl b), le_refl]
    · simp only [if_neg hi]
      apply le_antisymm
      · apply iSup_le; intro n
        rw [if_neg (show ¬(i = i₀ ∧ b ≤ n) from fun ⟨h, _⟩ => hi h)]
        simp [dyadic]
      · exact bot_le

/-- LSC on `ℕ → ℝ≥0∞` is closed under adding a dyadic constant at a single index. -/
theorem LowerSemicomputable.add_indicator_dyadic {f : ℕ → ℝ≥0∞}
    (hf : LowerSemicomputable f) (i₀ a b : ℕ) :
    LowerSemicomputable (fun i => f i + (if i = i₀ then dyadic a b else 0)) :=
  hf.add (lsc_indicator_const i₀ a b)

/-- Nat subtraction becomes ENNReal subtraction of dyadics: `dyadic (p - q) n =
dyadic p n - dyadic q n`. Holds unconditionally: when `q > p`, both sides are 0
(Nat sub truncates the LHS to 0, ENNReal tsub truncates the RHS to 0). -/
private theorem dyadic_sub_nat (p q n : ℕ) :
    dyadic (p - q) n = dyadic p n - dyadic q n := by
  unfold dyadic
  rw [ENNReal.natCast_sub]
  exact ENNReal.sub_div (fun _ _ => by positivity)

/-- `dyadic (a * 2^(n-b)) n = dyadic a b` when `b ≤ n`. Factoring out the shared
power of 2 in the numerator and denominator. -/
private theorem dyadic_mul_shift (a b n : ℕ) (h : b ≤ n) :
    dyadic (a * 2^(n - b)) n = dyadic a b := by
  unfold dyadic
  push_cast
  have hpow_eq : (2 : ℝ≥0∞)^n = (2 : ℝ≥0∞)^b * (2 : ℝ≥0∞)^(n - b) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow_eq]
  have h1 : (2 : ℝ≥0∞) ^ (n - b) ≠ 0 := by positivity
  have h2 : (2 : ℝ≥0∞) ^ (n - b) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  exact ENNReal.mul_div_mul_right _ _ h1 h2

/-- LSC on `ℕ → ℝ≥0∞` is closed under subtracting a dyadic constant at a single
index, provided the function dominates the constant at that index.

Approximant (for i = i₀): zero when `n < b` (so the subtracted bump is resolved
at a finer resolution than the dyadic), else `φ i n - a·2^(n-b)` with Nat sub
(which truncates to 0 when φ doesn't yet dominate the bump). For `i ≠ i₀`, use
`φ i n` unchanged. -/
theorem LowerSemicomputable.sub_indicator_dyadic {f : ℕ → ℝ≥0∞}
    (hf : LowerSemicomputable f) (i₀ a b : ℕ) (h : dyadic a b ≤ f i₀) :
    LowerSemicomputable (fun i => f i - (if i = i₀ then dyadic a b else 0)) := by
  obtain ⟨φ, hφ_comp, hφ_mono, hφ_sup⟩ := hf
  refine ⟨fun i n =>
    if i = i₀ then
      (if b ≤ n then φ i n - a * 2^(n - b) else 0)
    else φ i n, ?_, ?_, ?_⟩
  · -- Computability
    have hcond_i : Computable (fun p : ℕ × ℕ => decide (p.1 = i₀)) :=
      (Primrec.eq.decide.comp Primrec.fst (Primrec.const i₀)).to_comp
    have hcond_n : Computable (fun p : ℕ × ℕ => decide (b ≤ p.2)) :=
      (Primrec.nat_le.decide.comp (Primrec.const b) Primrec.snd).to_comp
    have h_phi : Computable (fun p : ℕ × ℕ => φ p.1 p.2) := hφ_comp
    have h_sub : Computable (fun p : ℕ × ℕ => φ p.1 p.2 - a * 2^(p.2 - b)) :=
      Primrec.nat_sub.to_comp.comp h_phi
        (Primrec.nat_mul.to_comp.comp (Computable.const a)
          (Primrec.nat_pow.to_comp.comp (Computable.const 2)
            (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const b))))
    have h_then : Computable (fun p : ℕ × ℕ =>
        if b ≤ p.2 then φ p.1 p.2 - a * 2 ^ (p.2 - b) else 0) :=
      (Computable.cond hcond_n h_sub (Computable.const 0)).of_eq
        fun p => by simp
    exact (Computable.cond hcond_i h_then h_phi).of_eq fun p => by simp
  · -- Monotonicity
    intro i m n hmn
    simp only
    by_cases hi : i = i₀
    · rw [if_pos hi, if_pos hi]
      have lhs_eq : dyadic (if b ≤ m then φ i m - a * 2^(m - b) else 0) m
          = if b ≤ m then dyadic (φ i m) m - dyadic a b else 0 := by
        split_ifs with hbm
        · rw [dyadic_sub_nat, dyadic_mul_shift a b m hbm]
        · simp [dyadic]
      have rhs_eq : dyadic (if b ≤ n then φ i n - a * 2^(n - b) else 0) n
          = if b ≤ n then dyadic (φ i n) n - dyadic a b else 0 := by
        split_ifs with hbn
        · rw [dyadic_sub_nat, dyadic_mul_shift a b n hbn]
        · simp [dyadic]
      rw [lhs_eq, rhs_eq]
      split_ifs with hbm hbn hbn
      · exact tsub_le_tsub (hφ_mono i hmn) le_rfl
      · exact absurd (hbm.trans hmn) hbn
      · exact bot_le
      · exact le_refl 0
    · simp only [if_neg hi]
      exact hφ_mono i hmn
  · -- Supremum
    intro i
    simp only
    by_cases hi : i = i₀
    · -- i = i₀: rewrite i to i₀ in conclusion via hi
      rw [hi]
      -- goal: ⨆ n, dyadic (if i₀ = i₀ then ... else ...) n = f i₀ - dyadic a b
      conv_lhs =>
        rw [show (fun n => dyadic
            (if i₀ = i₀ then (if b ≤ n then φ i₀ n - a * 2^(n-b) else 0) else φ i₀ n) n) =
          (fun n => dyadic (if b ≤ n then φ i₀ n - a * 2^(n-b) else 0) n) from by
            funext; rw [if_pos rfl]]
      have key_eq : ∀ k, dyadic (if b ≤ k then φ i₀ k - a * 2^(k - b) else 0) k
          = if b ≤ k then dyadic (φ i₀ k) k - dyadic a b else 0 := fun k => by
        split_ifs with hbk
        · rw [dyadic_sub_nat, dyadic_mul_shift a b k hbk]
        · simp [dyadic]
      simp_rw [key_eq]
      apply le_antisymm
      · apply iSup_le; intro n
        split_ifs with hbn
        · have hφ_le : dyadic (φ i₀ n) n ≤ f i₀ :=
            (hφ_sup i₀) ▸ le_iSup (fun m => dyadic (φ i₀ m) m) n
          exact tsub_le_tsub hφ_le le_rfl
        · exact bot_le
      · rw [tsub_le_iff_right, ← hφ_sup i₀]
        apply iSup_le; intro n
        set m := max b n
        have hbm : b ≤ m := le_max_left _ _
        have hnm : n ≤ m := le_max_right _ _
        calc dyadic (φ i₀ n) n
            ≤ dyadic (φ i₀ m) m := hφ_mono i₀ hnm
          _ ≤ (dyadic (φ i₀ m) m - dyadic a b) + dyadic a b := by
                rw [tsub_add_eq_max]; exact le_max_left _ _
          _ = (if b ≤ m then dyadic (φ i₀ m) m - dyadic a b else 0) + dyadic a b := by
                rw [if_pos hbm]
          _ ≤ (⨆ k, if b ≤ k then dyadic (φ i₀ k) k - dyadic a b else 0) + dyadic a b := by
                gcongr
                exact le_iSup (fun k => if b ≤ k then dyadic (φ i₀ k) k - dyadic a b else 0) m
    · simp only [if_neg hi, tsub_zero]
      exact hφ_sup i

/-! ### δ-construction weight transformations

The spine theorem's ⊇ direction builds two auxiliary `Weights`:
* `wShift` builds `w^(ξ)'` — weights for the new UM `ξ'`.
* `wCombine` builds `w^(c)'` — weights for the final mixture over `ν`.
Separating these keeps the main theorem readable.

Note (2026-11-06, Nathan): δ is a *positive dyadic* rather than an abstract
`ℝ≥0∞`, so that a computable approximant can name it. `wShift` and `wCombine`
accept `(k_δ b_δ : ℕ)` with δ := `dyadic k_δ b_δ`; `wShiftFun`, `wCombineFun`
and `wShiftFun_recomp` stay on an abstract `δ` because they only state
pointwise algebra.
-/

/-- `dyadic k b + dyadic (2^b - k) b = 1` when `k ≤ 2^b`. The two halves of
`1 = k/2^b + (2^b - k)/2^b` as ENNReals. -/
private theorem dyadic_add_complement (k b : ℕ) (hk : k ≤ 2^b) :
    dyadic k b + dyadic (2^b - k) b = 1 := by
  unfold dyadic
  rw [← ENNReal.add_div, ← Nat.cast_add, Nat.add_sub_cancel' hk]
  push_cast
  exact ENNReal.div_self (by positivity) (ENNReal.pow_ne_top (by norm_num))

/-- `dyadic k b ≠ ⊤`. -/
private theorem dyadic_ne_top (k b : ℕ) : dyadic k b ≠ ⊤ := by
  unfold dyadic
  exact ENNReal.div_ne_top (ENNReal.natCast_ne_top k) (by positivity)

/-- `1 - dyadic k b = dyadic (2^b - k) b` when `k ≤ 2^b`. Converts the ⅰ-free
side of the `wCombine` indicator to a dyadic so the existing LSC indicator
lemma applies. -/
private theorem one_sub_dyadic (k b : ℕ) (hk : k ≤ 2^b) :
    (1 : ℝ≥0∞) - dyadic k b = dyadic (2^b - k) b := by
  have hadd := dyadic_add_complement k b hk
  have hne : dyadic k b ≠ ⊤ := dyadic_ne_top k b
  rw [← hadd, ENNReal.add_sub_cancel_left hne]

/-- `w^(ξ)' (j) = (w_ξ j - δ·[j = i_c]) / (1 - δ)`. -/
private noncomputable def wShiftFun
    (w_ξ : Weights) (i_c : ℕ) (δ : ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun j => (w_ξ j - (if j = i_c then δ else 0)) / (1 - δ)

/-- `w^(c)' (i) = δ · w_c(i) + (1-δ)·[i = i_ξ']`. -/
private noncomputable def wCombineFun
    (w_c : Weights) (i_ξ' : ℕ) (δ : ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun i => δ * w_c i + (if i = i_ξ' then 1 - δ else 0)

/-- Fundamental identity: `(1-δ)·w^(ξ)'(j) + δ·[j = i_c] = w_ξ(j)`.

This is what lets us expand `(1-δ) ξ' + δ (ν_ξ i_c) = mixture ν_ξ w_ξ`
pointwise, without any ENNReal subtraction surgery in the main proof. -/
theorem wShiftFun_recomp
    (w_ξ : Weights) (i_c : ℕ) {δ : ℝ≥0∞}
    (hδ_le : δ ≤ w_ξ i_c) (hδ_lt_one : δ < 1) (j : ℕ) :
    (1 - δ) * wShiftFun w_ξ i_c δ j
      + (if j = i_c then δ else 0) = w_ξ j := by
  unfold wShiftFun
  have h1sub_pos : 0 < 1 - δ := tsub_pos_of_lt hδ_lt_one
  have h1sub_ne_zero : 1 - δ ≠ 0 := h1sub_pos.ne'
  have h1sub_ne_top : 1 - δ ≠ ⊤ := ne_top_of_le_ne_top one_ne_top tsub_le_self
  split_ifs with hj
  · subst hj
    rw [ENNReal.mul_div_cancel h1sub_ne_zero h1sub_ne_top]
    exact tsub_add_cancel_of_le hδ_le
  · simp only [tsub_zero, add_zero]
    exact ENNReal.mul_div_cancel h1sub_ne_zero h1sub_ne_top

/-- `wShift` as a `Weights`. Takes `δ := dyadic k_δ b_δ` so that LSC's
approximant can name δ computably. -/
private noncomputable def wShift
    (w_ξ : Weights) (i_c k_δ b_δ : ℕ)
    (hδ_pos : 0 < dyadic k_δ b_δ) (hδ_lt : dyadic k_δ b_δ < w_ξ i_c)
    (hδ_lt_one : dyadic k_δ b_δ < 1) : Weights where
  toFun := wShiftFun w_ξ i_c (dyadic k_δ b_δ)
  lsc := by
    -- Function: j ↦ (w_ξ j - δ·[j=i_c]) / (1-δ), with δ = dyadic k_δ b_δ.
    -- Factor as: (w_ξ j - δ·[j=i_c]) is LSC by sub_indicator_dyadic.
    -- Then divide by the fixed positive dyadic (1-δ) = dyadic (2^b_δ - k_δ) b_δ:
    -- dividing by a positive rational of denominator 2^b and natural numerator
    -- is multiplication by 2^b (easy: dyadic_mul with b=0, a=2^b)
    -- then division by the natural numerator — this last step is a general
    -- LSC closure (f/d for positive natural d is LSC) that has not been
    -- formalised here.
    sorry
  pos := by
    intro j
    unfold wShiftFun
    have h1sub_pos : 0 < 1 - dyadic k_δ b_δ := tsub_pos_of_lt hδ_lt_one
    have h1sub_ne_top : 1 - dyadic k_δ b_δ ≠ ⊤ := ne_top_of_le_ne_top one_ne_top tsub_le_self
    rw [ENNReal.div_pos_iff]
    refine ⟨?_, h1sub_ne_top⟩
    split_ifs with hj
    · subst hj
      rw [Ne, tsub_eq_zero_iff_le]
      push_neg
      exact hδ_lt
    · simp only [tsub_zero]
      exact (w_ξ.pos j).ne'
  tsum_le_one := by
    -- ∑ wShiftFun j = (∑ (w_ξ j - δ·[j=i_c])) / (1-δ) ≤ 1 since
    -- ∑ (w_ξ j - δ·[j=i_c]) = (∑ w_ξ j) - δ ≤ 1 - δ.
    have h1sub_pos : 0 < 1 - dyadic k_δ b_δ := tsub_pos_of_lt hδ_lt_one
    have h1sub_ne_zero : 1 - dyadic k_δ b_δ ≠ 0 := h1sub_pos.ne'
    have h1sub_ne_top : 1 - dyadic k_δ b_δ ≠ ⊤ := ne_top_of_le_ne_top one_ne_top tsub_le_self
    have hbump_le : (fun j : ℕ => if j = i_c then dyadic k_δ b_δ else 0) ≤
        fun j => w_ξ j := by
      intro j
      show (if j = i_c then dyadic k_δ b_δ else 0) ≤ w_ξ j
      split_ifs with hj
      · subst hj; exact hδ_lt.le
      · exact bot_le
    have hbump_sum :
        (∑' j : ℕ, (if j = i_c then dyadic k_δ b_δ else 0)) = dyadic k_δ b_δ := by
      rw [tsum_eq_single i_c (fun j hj => by rw [if_neg hj])]
      simp
    have hbump_sum_ne_top :
        (∑' j : ℕ, (if j = i_c then dyadic k_δ b_δ else 0)) ≠ ⊤ := by
      rw [hbump_sum]
      exact ne_top_of_le_ne_top one_ne_top hδ_lt_one.le
    have hsum_eq : (∑' j, wShiftFun w_ξ i_c (dyadic k_δ b_δ) j)
        = (∑' j, (w_ξ j - (if j = i_c then dyadic k_δ b_δ else 0))) /
          (1 - dyadic k_δ b_δ) := by
      unfold wShiftFun
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
    rw [hsum_eq, ENNReal.div_le_iff h1sub_ne_zero h1sub_ne_top, one_mul]
    rw [ENNReal.tsum_sub hbump_sum_ne_top hbump_le, hbump_sum]
    exact tsub_le_tsub w_ξ.tsum_le_one le_rfl

/-- `wCombine` as a `Weights`. Also takes dyadic `δ = dyadic k_δ b_δ`. LSC is
discharged by the existing `dyadic_mul` and `lsc_indicator_const` lemmas via
`one_sub_dyadic`. -/
private noncomputable def wCombine
    (w_c : Weights) (i_ξ' k_δ b_δ : ℕ)
    (hδ_pos : 0 < dyadic k_δ b_δ) (hδ_lt_one : dyadic k_δ b_δ < 1) : Weights where
  toFun := wCombineFun w_c i_ξ' (dyadic k_δ b_δ)
  lsc := by
    -- δ·w_c + (1-δ)·[·=i_ξ']. The first term is LSC by dyadic_mul applied to
    -- w_c; the second is LSC because `1 - dyadic k_δ b_δ = dyadic (2^b_δ - k_δ) b_δ`
    -- (`one_sub_dyadic`) so `lsc_indicator_const` applies. Add them.
    have hk : k_δ ≤ 2^b_δ := by
      have hlt : (k_δ : ℝ≥0∞) < (2 : ℝ≥0∞)^b_δ := by
        have h2b_pos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)^b_δ := by positivity
        have h2b_ne_top : (2 : ℝ≥0∞)^b_δ ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
        have := hδ_lt_one
        unfold dyadic at this
        rwa [ENNReal.div_lt_iff (Or.inl h2b_pos.ne') (Or.inl h2b_ne_top), one_mul] at this
      have hlt' : (k_δ : ℝ≥0∞) < ((2^b_δ : ℕ) : ℝ≥0∞) := by push_cast; exact hlt
      exact_mod_cast hlt'.le
    have h_eq : (fun i => if i = i_ξ' then (1 : ℝ≥0∞) - dyadic k_δ b_δ else 0) =
                (fun i => if i = i_ξ' then dyadic (2^b_δ - k_δ) b_δ else 0) := by
      funext i; split_ifs <;> simp [one_sub_dyadic k_δ b_δ hk]
    unfold wCombineFun
    show LowerSemicomputable
        (fun i => dyadic k_δ b_δ * w_c i + (if i = i_ξ' then (1 : ℝ≥0∞) - dyadic k_δ b_δ else 0))
    rw [show (fun i => dyadic k_δ b_δ * w_c i + (if i = i_ξ' then (1 : ℝ≥0∞) - dyadic k_δ b_δ else 0)) =
            (fun i => dyadic k_δ b_δ * w_c i +
              (if i = i_ξ' then dyadic (2^b_δ - k_δ) b_δ else 0)) by
      funext i; rw [show (if i = i_ξ' then (1 : ℝ≥0∞) - dyadic k_δ b_δ else 0) =
              (if i = i_ξ' then dyadic (2^b_δ - k_δ) b_δ else 0) from by
          split_ifs <;> simp [one_sub_dyadic k_δ b_δ hk]]]
    exact (w_c.lsc.dyadic_mul k_δ b_δ).add (lsc_indicator_const i_ξ' (2^b_δ - k_δ) b_δ)
  pos := by
    intro i
    unfold wCombineFun
    have h1sub_pos : 0 < 1 - dyadic k_δ b_δ := tsub_pos_of_lt hδ_lt_one
    have hterm_pos : 0 < dyadic k_δ b_δ * w_c i :=
      ENNReal.mul_pos hδ_pos.ne' (w_c.pos i).ne'
    split_ifs with hi
    · exact lt_of_lt_of_le hterm_pos le_self_add
    · rw [add_zero]; exact hterm_pos
  tsum_le_one := by
    -- ∑' i, (δ·w_c i + [i=i_ξ']·(1-δ)) = δ·∑ w_c + (1-δ) ≤ δ + (1-δ) = 1.
    unfold wCombineFun
    have h1sub_ne_top : 1 - dyadic k_δ b_δ ≠ ⊤ :=
      ne_top_of_le_ne_top one_ne_top tsub_le_self
    rw [ENNReal.tsum_add]
    rw [ENNReal.tsum_mul_left]
    rw [show (∑' i : ℕ, (if i = i_ξ' then 1 - dyadic k_δ b_δ else 0)) =
         1 - dyadic k_δ b_δ by
      rw [tsum_eq_single i_ξ' (fun j hj => by rw [if_neg hj])]; simp]
    calc dyadic k_δ b_δ * (∑' i, w_c i) + (1 - dyadic k_δ b_δ)
        ≤ dyadic k_δ b_δ * 1 + (1 - dyadic k_δ b_δ) := by gcongr; exact w_c.tsum_le_one
      _ = dyadic k_δ b_δ + (1 - dyadic k_δ b_δ) := by rw [mul_one]
      _ = 1 := by
            rw [add_tsub_cancel_of_le hδ_lt_one.le]

/-- **The spine theorem**, `thm:enums-of-ums=ums`: for any effective enumeration
of enumerable semimeasures containing every universal mixture, the class of
mixtures over it is exactly the class of universal mixtures.

Proof structure (paper's own, `ALT format.tex` L416–443):

* ⊇ direction (δ-construction, lines 430–439): the mixture
  `c := mixture ν geometricWeights` is enumerable (uniform enumerability of `ν`
  + LSC weights), so `c` appears in `ξ`'s own enumeration at some index `i_c`.
  Get a dyadic `δ` with `0 < δ < w_ξ(i_c)`. Build `ξ'` by shifting `δ` off
  `w_ξ(i_c)` and rescaling by `(1-δ)⁻¹`; `ξ'` is a UM and so lives in `ν` at
  some `i_ξ'`. Then the weight `w'(i) = δ w_c(i) + (1-δ)·[i = i_ξ']` over `ν`
  gives back `ξ`. The pointwise verification uses only
  `(1-δ) w^(ξ)'(j) + δ·[j = i_c] = w_ξ(j)` (`wShiftFun_recomp`), no ENNReal
  subtraction.

* ⊆ direction (interleaving, lines 425–428): given `c ∈ 𝒞_ν`, interleave `ν`
  with some UM `ξ`'s enumeration, assigning each `ν_i` its weight in `w^(c)`
  and each `ξ`-enumerant its weight in `w^(ξ)` scaled by `w^(c)(i_ξ^(ν))`. The
  seeding requires some UM to exist, which is not derivable from the current
  hypotheses — hence this direction is left for a follow-on commit.
-/
theorem mixtureClass_eq_universalMixtures
    (ν : ℕ → Semimeasure)
    -- Universal mixtures exist (Wood et al.; the paper takes it for granted). Without it the
    -- statement is false: `hν_univ` would be vacuous while `MixtureClass ν` is non-empty.
    -- (Nathan's decision, 2026-11-05, after the 2026-11-05 agent run.)
    (W : WoodInterface)
    (hν_enum : UniformlyEnumerable ν)
    (hν_univ : ContainsAllUniversalMixtures ν) :
    MixtureClass ν = {ξ | IsUniversalMixture ξ} := by
  apply Set.eq_of_subset_of_subset
  · -- ⊆: any mixture over ν is a UM.
    -- The paper's interleaving construction (ALT format.tex L425–428): take
    -- any UM ξ, locate it in ν at index `i_ξ`, build `ν'` that alternates
    -- `ν` (skipping index `i_ξ`) with `ν_ξ` (ξ's own enumeration), and
    -- assign `w'` so that `mixture ν' w' = mixture ν w_c`. `ν'` contains
    -- every enumerable semimeasure because `ν_ξ` does; the resulting mixture
    -- is therefore a UM.
    -- The construction NEEDS a seed UM `ξ`. From the current hypotheses
    -- this is not derivable: `ContainsAllUniversalMixtures ν` is vacuous
    -- when `{ξ | IsUniversalMixture ξ}` is empty. Wood et al.'s Lemma 6
    -- (there is an enumeration of all enumerable semimeasures) supplies
    -- this externally; in Lean that lemma is a `WoodInterface` or an
    -- explicit `∃ ξ, IsUniversalMixture ξ` hypothesis, neither of which is
    -- in the current signature. See RUN-REPORT for the fix needed.
    rintro c ⟨w_c, rfl⟩
    sorry
  · -- ⊇: any UM is a mixture over ν. The paper's δ-construction.
    rintro ξ ⟨ν_ξ, w_ξ, hν_ξ_enum, hν_ξ_complete, rfl⟩
    -- c := mixture ν geometricWeights; enumerable.
    have hc_enum : (mixture ν geometricWeights).Enumerable :=
      hν_enum.mixture_enumerable geometricWeights
    -- c appears in ν_ξ at some index i_c.
    obtain ⟨i_c, hi_c⟩ := hν_ξ_complete _ hc_enum
    -- Positive dyadic q ≤ w_ξ i_c from LSC of w_ξ.
    obtain ⟨k_q, n_q, hq_pos, hq_le⟩ :=
      LowerSemicomputable.exists_pos_approx w_ξ.lsc (w_ξ.pos i_c)
    -- q ≤ w_ξ i_c ≤ 1
    have hq_le_one : dyadic k_q n_q ≤ 1 :=
      hq_le.trans ((ENNReal.le_tsum i_c).trans w_ξ.tsum_le_one)
    -- δ := q/2, with 0 < δ < w_ξ i_c and δ < 1.
    have hq_ne_top : dyadic k_q n_q ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hq_le_one
    -- δ is the dyadic `dyadic k_q (n_q + 1)`, equal to `dyadic k_q n_q / 2` (half of q).
    set δ : ℝ≥0∞ := dyadic k_q (n_q + 1) with hδ_def
    have hδ_eq_half : δ = dyadic k_q n_q / 2 := by rw [hδ_def, ← dyadic_div_two]
    have hδ_pos : 0 < δ := by
      rw [hδ_eq_half]; exact ENNReal.div_pos hq_pos.ne' (by norm_num)
    have hδ_lt_q : δ < dyadic k_q n_q := by
      rw [hδ_eq_half]; exact ENNReal.half_lt_self hq_pos.ne' hq_ne_top
    have hδ_lt_wξ : δ < w_ξ i_c := lt_of_lt_of_le hδ_lt_q hq_le
    have hδ_le_wξ : δ ≤ w_ξ i_c := hδ_lt_wξ.le
    have hδ_lt_one : δ < 1 := lt_of_lt_of_le hδ_lt_q hq_le_one
    -- Build w_ξ' and ξ'.
    let w_ξ' : Weights := wShift w_ξ i_c k_q (n_q + 1) hδ_pos hδ_lt_wξ hδ_lt_one
    let ξ' : Semimeasure := mixture ν_ξ w_ξ'
    have hξ'_um : IsUniversalMixture ξ' :=
      ⟨ν_ξ, w_ξ', hν_ξ_enum, hν_ξ_complete, rfl⟩
    obtain ⟨i_ξ', hi_ξ'⟩ := hν_univ _ hξ'_um
    -- Build w' and verify equality.
    let w' : Weights := wCombine geometricWeights i_ξ' k_q (n_q + 1) hδ_pos hδ_lt_one
    refine ⟨w', ?_⟩
    apply Semimeasure.ext
    intro x
    -- Pointwise equality. Unfold both sides to `∑' i, ... * ν i x`.
    simp only [mixture_apply]
    -- Goal: ∑' j, w_ξ j * ν_ξ j x = ∑' i, w' i * ν i x
    -- Shared target form: δ·(mixture ν geom x) + (1-δ)·(ν i_ξ' x).
    -- LHS = (1-δ) * (∑ w_ξ' j * ν_ξ j x) + δ * ν_ξ i_c x
    --     = (1-δ) * ν i_ξ' x       + δ * (mixture ν geom x)
    -- using hi_ξ' and hi_c.
    -- RHS = δ * (mixture ν geom x) + (1-δ) * ν i_ξ' x directly.
    have hLHS : (∑' j, w_ξ j * ν_ξ j x)
        = (1 - δ) * ν i_ξ' x + δ * (∑' i, geometricWeights i * ν i x) := by
      calc (∑' j, w_ξ j * ν_ξ j x)
          = ∑' j, ((1 - δ) * wShiftFun w_ξ i_c δ j
                   + (if j = i_c then δ else 0)) * ν_ξ j x := by
            congr 1; funext j
            rw [wShiftFun_recomp w_ξ i_c hδ_le_wξ hδ_lt_one]
        _ = (∑' j, (1 - δ) * wShiftFun w_ξ i_c δ j * ν_ξ j x)
            + ∑' j, (if j = i_c then δ else 0) * ν_ξ j x := by
            rw [← ENNReal.tsum_add]
            congr 1; funext j; rw [add_mul]
        _ = (1 - δ) * (∑' j, wShiftFun w_ξ i_c δ j * ν_ξ j x)
            + δ * ν_ξ i_c x := by
            congr 1
            · rw [← ENNReal.tsum_mul_left]
              congr 1; funext j; rw [mul_assoc]
            · rw [tsum_eq_single i_c (fun j hj => by rw [if_neg hj, zero_mul])]
              rw [if_pos rfl]
        _ = (1 - δ) * ν i_ξ' x + δ * (∑' i, geometricWeights i * ν i x) := by
            congr 1
            · rw [show (∑' j, wShiftFun w_ξ i_c δ j * ν_ξ j x) = ν i_ξ' x from by
                rw [hi_ξ']; rfl]
            · rw [show ν_ξ i_c x = (∑' i, geometricWeights i * ν i x) from by
                rw [hi_c]; rfl]
    have hRHS : (∑' i, w' i * ν i x)
        = δ * (∑' i, geometricWeights i * ν i x) + (1 - δ) * ν i_ξ' x := by
      calc (∑' i, w' i * ν i x)
          = ∑' i, (δ * geometricWeights i
                   + (if i = i_ξ' then 1 - δ else 0)) * ν i x := rfl
        _ = (∑' i, δ * geometricWeights i * ν i x)
            + ∑' i, (if i = i_ξ' then 1 - δ else 0) * ν i x := by
            rw [← ENNReal.tsum_add]
            congr 1; funext i; rw [add_mul]
        _ = δ * (∑' i, geometricWeights i * ν i x) + (1 - δ) * ν i_ξ' x := by
            congr 1
            · rw [← ENNReal.tsum_mul_left]
              congr 1; funext i; rw [mul_assoc]
            · rw [tsum_eq_single i_ξ' (fun j hj => by rw [if_neg hj, zero_mul])]
              rw [if_pos rfl]
    rw [hLHS, hRHS, add_comm]

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

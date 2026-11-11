-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.Wood

/-!
# Monotone machines, their Solomonoff semimeasures, and WSH Lemma 6

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-11. Not reviewed by Nathan.

Source: Wood, Sunehag & Hutter 2011 (arXiv 1111.3854), Def. `def:lambda_T` and Lemma
`lem:measures-TM` (Lemma 6); `paper/ALT format.tex` ~lines 97–115.

## The model (an INTERFACE, not a tape machine)

A monotone machine is modelled as a computably enumerable set of (program, output) pairs
that is *consistent*: if `(p, x)` and `(p', x')` are both in it and `p` is a prefix of `p'`,
then `x` and `x'` are comparable. A pair `(p, x)` reads "having read `p`, the machine has
written (at least) `x`". That this abstraction captures tape machines is NOT proved here.

`M.Produces q x` : some pair `(p, y)` has `p ⪯ q` and `x ⪯ y` ("`M(q) ⊒ x`").

`M.sm x` : the uniform measure of the programs producing `x`, defined by counting: the
fraction of the length-`n` strings `q` with `M.Produces q x`, in the limit `n → ∞`.
It is a semimeasure. NOTE `M.sm [] ` is the measure of the programs on which the machine has
any pair at all (possibly with empty output), which may be `< 1`.

`M.lam x` : WSH's `λ_T` / the paper's `P_M`: `1` at the empty string, `M.sm x` elsewhere.
-/

open ENNReal

namespace HsiLean.Monotone

/-- A (program, output) pair. -/
abbrev Pair : Type := List Bool × List Bool

/-- [UNAPPROVED STATEMENT] A monotone machine, abstractly: a computably enumerable,
consistent set of (program, output) pairs. -/
structure Machine where
  /-- The (program, output) pairs. -/
  pairs : Set Pair
  /-- The set of pairs is computably enumerable. -/
  ce : ∃ g : ℕ → Option Pair, Computable g ∧ ∀ a, a ∈ pairs ↔ ∃ n, g n = some a
  /-- Monotonicity: extending the program can only extend the output. -/
  consistent : ∀ a ∈ pairs, ∀ b ∈ pairs, a.1 <+: b.1 → (a.2 <+: b.2 ∨ b.2 <+: a.2)

/-- [UNAPPROVED STATEMENT] `M(q) ⊒ x`: on input `q` the machine's output extends `x`. -/
def Machine.Produces (M : Machine) (q x : List Bool) : Prop :=
  ∃ a ∈ M.pairs, a.1 <+: q ∧ x <+: a.2

/-- All binary strings of length `n`. -/
def strs : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (strs n).image (· ++ [false]) ∪ (strs n).image (· ++ [true])

open Classical in
/-- The number of length-`n` strings satisfying `P`. -/
noncomputable def cover (P : List Bool → Prop) (n : ℕ) : ℕ := ((strs n).filter P).card

/-- [UNAPPROVED STATEMENT] The uniform measure of the set of infinite strings having a
finite prefix in `P` (for `P` closed under extension), by counting. -/
noncomputable def meas (P : List Bool → Prop) : ℝ≥0∞ := ⨆ n, dyadic (cover P n) n

/-- [UNAPPROVED STATEMENT] The Solomonoff semimeasure of a machine, as a `Semimeasure`. -/
noncomputable def Machine.sm (M : Machine) : Semimeasure where
  toFun x := meas (M.Produces · x)
  empty_le_one := sorry
  extend_le := sorry

/-- [UNAPPROVED STATEMENT] WSH's `λ_T` / the paper's `P_M`: `1` on the empty string. -/
noncomputable def Machine.lam (M : Machine) (x : List Bool) : ℝ≥0∞ :=
  if x = [] then 1 else M.sm x

/-- [UNAPPROVED STATEMENT] An effective family of machines: one computable procedure
enumerates the pairs of every `V k`. -/
def UniformlyCE (V : ℕ → Machine) : Prop :=
  ∃ G : ℕ → ℕ → Option Pair, Computable₂ G ∧ ∀ k a, a ∈ (V k).pairs ↔ ∃ n, G k n = some a

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 (⇒), uniform version. -/
theorem sm_uniformlyEnumerable {V : ℕ → Machine} (hV : UniformlyCE V) :
    UniformlyEnumerable (fun k => (V k).sm) := sorry

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 (⇒): `λ_T` is enumerable. -/
theorem sm_enumerable (M : Machine) : M.sm.Enumerable := sorry

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 (⇐), Levin's construction, exact form. -/
theorem exists_machine_sm_eq (μ : Semimeasure) (hμ : μ.Enumerable) :
    ∃ M : Machine, M.sm = μ := sorry

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 as stated there. -/
theorem wsh_lemma6 (μ : Semimeasure) :
    μ.Enumerable ↔
      (∃ M : Machine, ∀ x, x ≠ [] → μ x = M.lam x) ∧
        LowerSemicomputable (fun _ : Unit => μ []) := sorry

/-- [UNAPPROVED STATEMENT] An effective enumeration of ALL monotone machines. -/
noncomputable def enumMachine : ℕ → Machine := sorry

/-- [UNAPPROVED STATEMENT] The enumeration is effective. -/
theorem enumMachine_uniformlyCE : UniformlyCE enumMachine := sorry

/-- [UNAPPROVED STATEMENT] Every machine is listed. -/
theorem enumMachine_complete (M : Machine) : ∃ e, enumMachine e = M := sorry

end HsiLean.Monotone

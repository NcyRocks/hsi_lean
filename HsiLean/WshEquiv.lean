-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.Levin

/-!
# Solomonoff priors of monotone UTMs = universal mixtures (WSH 2011, Theorem 14)

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-11. Not reviewed by Nathan.

Source: Wood, Sunehag & Hutter 2011 (arXiv 1111.3854): Def. `def:UTM`, Lemma
`thm:UTM-is-mixture` (Lemma 10), Lemma `thm:mixture-is-UTM` (Lemma 13), Theorem
`thm:UTM-eq-mixture` (Theorem 14).
-/

open ENNReal

namespace HsiLean.Monotone

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

/-- [UNAPPROVED STATEMENT] WSH Lemma 10: the Solomonoff prior of a UTM is a universal
mixture, off the empty string. -/
theorem utm_is_universalMixture (U : Machine) (hU : IsUTM U) :
    ∃ ξ : Semimeasure, IsUniversalMixture ξ ∧ ∀ x, x ≠ [] → U.lam x = ξ x := sorry

/-- [UNAPPROVED STATEMENT] WSH Lemma 13: every universal mixture is the Solomonoff prior
of some UTM, off the empty string. -/
theorem universalMixture_is_utm (ξ : Semimeasure) (hξ : IsUniversalMixture ξ) :
    ∃ U : Machine, IsUTM U ∧ ∀ x, x ≠ [] → U.lam x = ξ x := sorry

/-- [UNAPPROVED STATEMENT] WSH Theorem 14: the class of Solomonoff priors of UTMs equals the
class of universal mixtures, as functions on the non-empty strings. -/
theorem solomonoff_eq_universalMixtures :
    {f : {x : List Bool // x ≠ []} → ℝ≥0∞ | ∃ U : Machine, IsUTM U ∧ f = fun x => U.lam x.1} =
      {f | ∃ ξ : Semimeasure, IsUniversalMixture ξ ∧ f = fun x => ξ x.1} := sorry

end HsiLean.Monotone

-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.MonotoneCE

/-!
# WSH Lemma 6 (⇐): Levin's construction

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-11. Not reviewed by Nathan.

Every enumerable semimeasure is the Solomonoff semimeasure of a monotone machine.
WSH give no proof (they cite Li & Vitányi Thm 4.5.2); the proof here is a reconstruction.
-/

open ENNReal

namespace HsiLean.Monotone

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 (⇐), Levin's construction, exact form. -/
theorem exists_machine_sm_eq (μ : Semimeasure) (hμ : μ.Enumerable) :
    ∃ M : Machine, M.sm = μ := sorry

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 as stated there. -/
theorem wsh_lemma6 (μ : Semimeasure) :
    μ.Enumerable ↔
      (∃ M : Machine, ∀ x, x ≠ [] → μ x = M.lam x) ∧
        LowerSemicomputable (fun _ : Unit => μ []) := sorry

end HsiLean.Monotone

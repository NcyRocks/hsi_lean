-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.MonotoneCE

/-!
# WSH Lemma 6 (⇐): Levin's construction

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-11. Not reviewed by Nathan.

Every enumerable semimeasure is the Solomonoff semimeasure of a monotone machine.
WSH give no proof (they cite Li & Vitányi Thm 4.5.2); the proof here is a reconstruction.

## Outline

Take staged approximants `N t x` of `μ` (`Wood.exists_stageApprox`): numerators at level `t`,
a semimeasure at every stage, at least doubling from stage to stage, with supremum `μ`.
Below, output strings are stored REVERSED (`r = x.reverse`, so the children of `r` are
`false :: r` and `true :: r`) and `K t r = N t r.reverse`.

At level `t` the mass of `r` is the integer interval `[0, K t r)`, ordered by time of
arrival: a point `u` that is there at level `t` becomes the points `2u, 2u+1` at level
`t+1`, and the points that are new at level `t+1` are appended after them.

* `pc K t b r u` ("parent coordinate") embeds the mass of the child `b :: r` into the mass of
  `r`: old points keep their place (`2 * pc … (u/2) + u%2`); the points of `false :: r`
  that are new at level `t+1` are put directly after everything allocated at level `t`
  (`2 * K t (true :: r) + u`), and the new points of `true :: r` directly after those
  (`K (t+1) (false :: r) + u`). The two children get disjoint parts of the parent (`pc_inj`)
  because `K (t+1) (false :: r) + K (t+1) (true :: r) ≤ K (t+1) r`.
* `emb K t r u` composes `pc` down to the root, giving a number `< 2^t`, i.e. a program of
  length `t`. `Reg K t r` is its image.
* The machine has the pairs `(q, x)` with `val q ∈ Reg K |q| x.reverse`. It is consistent
  because regions of incomparable strings are disjoint, and exactly `K n x.reverse` programs
  of length `n` produce `x`, so `sm x = sup_n K n x.reverse / 2^n = μ x`.
-/

open ENNReal

namespace HsiLean.Monotone

open HsiLean.Wood

/-! ### Staged approximants on reversed strings -/

/-- The properties of staged approximants (on reversed strings) used by the construction. -/
structure Staged (K : ℕ → List Bool → ℕ) : Prop where
  root : ∀ t, K t [] ≤ 2 ^ t
  ext : ∀ t r, K t (false :: r) + K t (true :: r) ≤ K t r
  dbl : ∀ t r, 2 * K t r ≤ K (t + 1) r

/-- Parent coordinate: where the point `u` of `b :: r` sits inside `r`, at level `t`. -/
def pc (K : ℕ → List Bool → ℕ) : ℕ → Bool → List Bool → ℕ → ℕ
  | 0, b, r, u => if b then K 0 (false :: r) + u else u
  | t + 1, b, r, u =>
    if u < 2 * K t (b :: r) then 2 * pc K t b r (u / 2) + u % 2
    else if b then K (t + 1) (false :: r) + u else 2 * K t (true :: r) + u

theorem pc_lt {K : ℕ → List Bool → ℕ} (h : Staged K) :
    ∀ t b r u, u < K t (b :: r) → pc K t b r u < K t (false :: r) + K t (true :: r) := by
  intro t
  induction t with
  | zero =>
    intro b r u hu
    cases b <;> simp only [pc, Bool.false_eq_true, ↓reduceIte] <;> omega
  | succ t ih =>
    intro b r u hu
    have df := h.dbl t (false :: r)
    have dt := h.dbl t (true :: r)
    have i1 := ih false r (u / 2)
    have i2 := ih true r (u / 2)
    cases b <;> simp only [pc, Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega

theorem pc_inj {K : ℕ → List Bool → ℕ} (h : Staged K) :
    ∀ t b b' r u u', u < K t (b :: r) → u' < K t (b' :: r) →
      pc K t b r u = pc K t b' r u' → b = b' ∧ u = u' := by
  intro t
  induction t with
  | zero =>
    intro b b' r u u' hu hu' he
    cases b <;> cases b' <;> simp only [pc, Bool.false_eq_true, ↓reduceIte] at he
    · exact ⟨rfl, he⟩
    · omega
    · omega
    · exact ⟨rfl, by omega⟩
  | succ t ih =>
    intro b b' r u u' hu hu' he
    have df := h.dbl t (false :: r)
    have dt := h.dbl t (true :: r)
    have l1 := pc_lt h t false r (u / 2)
    have l2 := pc_lt h t true r (u / 2)
    have l3 := pc_lt h t false r (u' / 2)
    have l4 := pc_lt h t true r (u' / 2)
    by_cases h1 : u < 2 * K t (b :: r) <;> by_cases h2 : u' < 2 * K t (b' :: r) <;>
      simp only [pc, h1, h2, ↓reduceIte] at he
    · obtain ⟨hb, hu2⟩ := ih b b' r (u / 2) (u' / 2) (by omega) (by omega) (by omega)
      exact ⟨hb, by omega⟩
    all_goals
      cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte] at he <;>
        first
        | exact ⟨rfl, by omega⟩
        | omega

theorem pc_succ (K : ℕ → List Bool → ℕ) (t : ℕ) (b : Bool) (r : List Bool) (u c : ℕ)
    (hu : u < K t (b :: r)) (hc : c < 2) :
    pc K (t + 1) b r (2 * u + c) = 2 * pc K t b r u + c := by
  have e1 : (2 * u + c) / 2 = u := by omega
  have e2 : (2 * u + c) % 2 = c := by omega
  simp only [pc]
  rw [if_pos (by omega), e1, e2]

/-- The embedding of the level-`t` mass of `r` into the programs of length `t` (as numbers). -/
def emb (K : ℕ → List Bool → ℕ) (t : ℕ) : List Bool → ℕ → ℕ
  | [], u => u
  | b :: r, u => emb K t r (pc K t b r u)

theorem emb_lt {K : ℕ → List Bool → ℕ} (h : Staged K) (t : ℕ) :
    ∀ r u, u < K t r → emb K t r u < 2 ^ t := by
  intro r
  induction r with
  | nil => intro u hu; exact lt_of_lt_of_le hu (h.root t)
  | cons b r ih =>
    intro u hu
    exact ih _ (lt_of_lt_of_le (pc_lt h t b r u hu) (h.ext t r))

theorem emb_succ {K : ℕ → List Bool → ℕ} (h : Staged K) (t : ℕ) :
    ∀ r u c, u < K t r → c < 2 → emb K (t + 1) r (2 * u + c) = 2 * emb K t r u + c := by
  intro r
  induction r with
  | nil => intro u c _ _; rfl
  | cons b r ih =>
    intro u c hu hc
    change emb K (t + 1) r (pc K (t + 1) b r (2 * u + c)) = 2 * emb K t r (pc K t b r u) + c
    rw [pc_succ K t b r u c hu hc]
    exact ih _ c (lt_of_lt_of_le (pc_lt h t b r u hu) (h.ext t r)) hc

theorem emb_inj {K : ℕ → List Bool → ℕ} (h : Staged K) (t : ℕ) :
    ∀ r u u', u < K t r → u' < K t r → emb K t r u = emb K t r u' → u = u' := by
  intro r
  induction r with
  | nil => intro u u' _ _ he; exact he
  | cons b r ih =>
    intro u u' hu hu' he
    exact (pc_inj h t b b r u u' hu hu'
      (ih _ _ (lt_of_lt_of_le (pc_lt h t b r u hu) (h.ext t r))
        (lt_of_lt_of_le (pc_lt h t b r u' hu') (h.ext t r)) he)).2

/-- The region of `r` at level `t`: the programs (as numbers) allocated to `r`. -/
def Reg (K : ℕ → List Bool → ℕ) (t : ℕ) (r : List Bool) (v : ℕ) : Prop :=
  ∃ u, u < K t r ∧ emb K t r u = v

theorem reg_cons {K : ℕ → List Bool → ℕ} (h : Staged K) {t : ℕ} {b : Bool} {r : List Bool}
    {v : ℕ} : Reg K t (b :: r) v → Reg K t r v := by
  rintro ⟨u, hu, he⟩
  exact ⟨pc K t b r u, lt_of_lt_of_le (pc_lt h t b r u hu) (h.ext t r), he⟩

theorem reg_append {K : ℕ → List Bool → ℕ} (h : Staged K) {t : ℕ} {r : List Bool} {v : ℕ} :
    ∀ s : List Bool, Reg K t (s ++ r) v → Reg K t r v := by
  intro s
  induction s with
  | nil => exact id
  | cons b s ih => exact fun hr => ih (reg_cons h hr)

theorem reg_disjoint {K : ℕ → List Bool → ℕ} (h : Staged K) {t : ℕ} {b b' : Bool}
    {r : List Bool} {v : ℕ} : Reg K t (b :: r) v → Reg K t (b' :: r) v → b = b' := by
  rintro ⟨u, hu, he⟩ ⟨u', hu', he'⟩
  have := emb_inj h t r _ _ (lt_of_lt_of_le (pc_lt h t b r u hu) (h.ext t r))
    (lt_of_lt_of_le (pc_lt h t b' r u' hu') (h.ext t r)) (he.trans he'.symm)
  exact (pc_inj h t b b' r u u' hu hu' this).1

theorem reg_eq_of_length {K : ℕ → List Bool → ℕ} (h : Staged K) {t : ℕ} {v : ℕ} :
    ∀ r r' : List Bool, r.length = r'.length → Reg K t r v → Reg K t r' v → r = r' := by
  intro r
  induction r with
  | nil =>
    intro r' hl _ _
    exact (List.length_eq_zero_iff.mp hl.symm).symm
  | cons b r ih =>
    intro r' hl h1 h2
    cases r' with
    | nil => simp at hl
    | cons b' r' =>
      have hr : r = r' := ih r' (by simpa using hl) (reg_cons h h1) (reg_cons h h2)
      subst hr
      have hb := reg_disjoint h h1 h2
      subst hb
      rfl

theorem reg_suffix {K : ℕ → List Bool → ℕ} (h : Staged K) {t : ℕ} {v : ℕ} {r r' : List Bool}
    (hl : r.length ≤ r'.length) (h1 : Reg K t r v) (h2 : Reg K t r' v) : r <:+ r' := by
  have h2' : Reg K t (r'.drop (r'.length - r.length)) v :=
    reg_append h (r'.take (r'.length - r.length)) (by rwa [List.take_append_drop])
  have := reg_eq_of_length h r (r'.drop (r'.length - r.length))
    (by rw [List.length_drop]; omega) h1 h2'
  rw [this]
  exact List.drop_suffix _ _

theorem reg_succ {K : ℕ → List Bool → ℕ} (h : Staged K) {t : ℕ} {r : List Bool} {v c : ℕ}
    (hr : Reg K t r v) (hc : c < 2) : Reg K (t + 1) r (2 * v + c) := by
  obtain ⟨u, hu, he⟩ := hr
  have := h.dbl t r
  exact ⟨2 * u + c, by omega, by rw [emb_succ h t r u c hu hc, he]⟩

theorem reg_val_append {K : ℕ → List Bool → ℕ} (h : Staged K) {r : List Bool} (q : List Bool) :
    ∀ s : List Bool, Reg K q.length r (val q) → Reg K (q ++ s).length r (val (q ++ s)) := by
  intro s
  induction s using List.reverseRecOn with
  | nil => intro hr; simpa using hr
  | append_singleton s b ih =>
    intro hr
    have hlen : (q ++ (s ++ [b])).length = (q ++ s).length + 1 := by simp; omega
    rw [hlen, ← List.append_assoc, val_concat]
    exact reg_succ h (ih hr) (by cases b <;> simp)

/-! ### Computability of the embedding -/

/-- One step of the search for the stage at which a point arrived. -/
def stepP (K : ℕ → List Bool → ℕ) (b : Bool) (r : List Bool) (st : ℕ × ℕ) : ℕ × ℕ :=
  if 0 < st.1 ∧ st.2 < 2 * K (st.1 - 1) (b :: r) then (st.1 - 1, st.2 / 2) else st

/-- The parent coordinate of a point that is new at level `s`. -/
def base (K : ℕ → List Bool → ℕ) (b : Bool) (r : List Bool) (s w : ℕ) : ℕ :=
  bif b then K s (false :: r) + w else (if s = 0 then 0 else 2 * K (s - 1) (true :: r)) + w

/-- Closed form of `pc`: go back to the stage of arrival, then shift. -/
def pcF (K : ℕ → List Bool → ℕ) (t : ℕ) (b : Bool) (r : List Bool) (u : ℕ) : ℕ :=
  base K b r ((stepP K b r)^[t] (t, u)).1 ((stepP K b r)^[t] (t, u)).2 *
      2 ^ (t - ((stepP K b r)^[t] (t, u)).1) +
    u % 2 ^ (t - ((stepP K b r)^[t] (t, u)).1)

theorem stepP_fst_le (K : ℕ → List Bool → ℕ) (b : Bool) (r : List Bool) :
    ∀ n s w, ((stepP K b r)^[n] (s, w)).1 ≤ s := by
  intro n
  induction n with
  | zero => intro s w; exact le_rfl
  | succ n ih =>
    intro s w
    rw [Function.iterate_succ_apply]
    unfold stepP
    split_ifs
    · exact (ih _ _).trans (Nat.sub_le _ _)
    · exact ih _ _

theorem pc_eq_pcF (K : ℕ → List Bool → ℕ) (b : Bool) (r : List Bool) :
    ∀ t u, pc K t b r u = pcF K t b r u := by
  intro t
  induction t with
  | zero =>
    intro u
    cases b <;> simp [pc, pcF, base, Nat.mod_one]
  | succ t ih =>
    intro u
    unfold pcF
    rw [Function.iterate_succ_apply]
    by_cases h1 : u < 2 * K t (b :: r)
    · have hstep : stepP K b r (t + 1, u) = (t, u / 2) := by
        unfold stepP
        rw [if_pos ⟨by omega, by simpa using h1⟩]
        rfl
      rw [hstep]
      have hle := stepP_fst_le K b r t t (u / 2)
      have hpc : pc K (t + 1) b r u = 2 * pc K t b r (u / 2) + u % 2 := by
        simp only [pc]
        rw [if_pos h1]
      rw [hpc, ih (u / 2)]
      unfold pcF
      generalize (stepP K b r)^[t] (t, u / 2) = f at hle ⊢
      have hd : t + 1 - f.1 = (t - f.1) + 1 := by omega
      rw [hd, pow_succ, Nat.mul_comm (2 ^ (t - f.1)) 2, Nat.mod_mul]
      ring
    · have hstep : stepP K b r (t + 1, u) = (t + 1, u) := by
        unfold stepP
        rw [if_neg]
        rintro ⟨_, h2⟩
        exact h1 (by simpa using h2)
      rw [hstep, Function.iterate_fixed hstep]
      simp only [pc]
      rw [if_neg h1]
      cases b <;> simp [base, Nat.mod_one]

section Computability

variable (K : ℕ → List Bool → ℕ) (hK : Primrec (fun p : ℕ × List Bool => K p.1 p.2))
include hK

theorem stepP_primrec :
    Primrec (fun p : (Bool × List Bool) × (ℕ × ℕ) => stepP K p.1.1 p.1.2 p.2) := by
  have s1 : Primrec (fun p : (Bool × List Bool) × (ℕ × ℕ) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have s2 : Primrec (fun p : (Bool × List Bool) × (ℕ × ℕ) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hcons : Primrec (fun p : (Bool × List Bool) × (ℕ × ℕ) => p.1.1 :: p.1.2) :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hs1 : Primrec (fun p : (Bool × List Bool) × (ℕ × ℕ) => p.2.1 - 1) :=
    Primrec.nat_sub.comp s1 (Primrec.const 1)
  have hKv : Primrec (fun p : (Bool × List Bool) × (ℕ × ℕ) => K (p.2.1 - 1) (p.1.1 :: p.1.2)) :=
    hK.comp (Primrec.pair hs1 hcons)
  have c1 : PrimrecPred (fun p : (Bool × List Bool) × (ℕ × ℕ) => 0 < p.2.1) :=
    PrimrecRel.comp Primrec.nat_lt (Primrec.const 0) s1
  have c2 : PrimrecPred (fun p : (Bool × List Bool) × (ℕ × ℕ) =>
      p.2.2 < 2 * K (p.2.1 - 1) (p.1.1 :: p.1.2)) :=
    PrimrecRel.comp Primrec.nat_lt s2 (Primrec.nat_mul.comp (Primrec.const 2) hKv)
  exact Primrec.ite (c1.and c2)
    (Primrec.pair hs1 (Primrec.nat_div.comp s2 (Primrec.const 2))) Primrec.snd

theorem pcF_primrec :
    Primrec (fun a : ℕ × Bool × List Bool × ℕ => pcF K a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have ht : Primrec (fun a : ℕ × Bool × List Bool × ℕ => a.1) := Primrec.fst
  have hb : Primrec (fun a : ℕ × Bool × List Bool × ℕ => a.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun a : ℕ × Bool × List Bool × ℕ => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hu : Primrec (fun a : ℕ × Bool × List Bool × ℕ => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ (fun (a : ℕ × Bool × List Bool × ℕ) (st : ℕ × ℕ) =>
      stepP K a.2.1 a.2.2.1 st) :=
    ((stepP_primrec K hK).comp (Primrec.pair
      (Primrec.pair (hb.comp Primrec.fst) (hr.comp Primrec.fst)) Primrec.snd)).to₂
  have it : Primrec (fun a : ℕ × Bool × List Bool × ℕ =>
      (stepP K a.2.1 a.2.2.1)^[a.1] (a.1, a.2.2.2)) :=
    Primrec.nat_iterate ht (Primrec.pair ht hu) hstep
  have f1 := Primrec.fst.comp it
  have f2 := Primrec.snd.comp it
  have hKf := hK.comp (Primrec.pair f1 (Primrec.list_cons.comp (Primrec.const false) hr))
  have hKt := hK.comp (Primrec.pair (Primrec.nat_sub.comp f1 (Primrec.const 1))
    (Primrec.list_cons.comp (Primrec.const true) hr))
  have hite := Primrec.ite (PrimrecRel.comp Primrec.eq f1 (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_mul.comp (Primrec.const 2) hKt)
  have hbase := Primrec.cond hb (Primrec.nat_add.comp hKf f2) (Primrec.nat_add.comp hite f2)
  have hpow := Primrec.nat_pow.comp (Primrec.const 2) (Primrec.nat_sub.comp ht f1)
  exact (Primrec.nat_add.comp (Primrec.nat_mul.comp hbase hpow)
    (Primrec.nat_mod.comp hu hpow)).of_eq fun a => rfl

theorem pc_primrec :
    Primrec (fun a : ℕ × Bool × List Bool × ℕ => pc K a.1 a.2.1 a.2.2.1 a.2.2.2) :=
  (pcF_primrec K hK).of_eq fun a => (pc_eq_pcF K a.2.1 a.2.2.1 a.1 a.2.2.2).symm

omit hK in
/-- One step of `emb`, as a state machine on (remaining string, coordinate). -/
def stepE (K : ℕ → List Bool → ℕ) (t : ℕ) : List Bool × ℕ → List Bool × ℕ
  | ([], u) => ([], u)
  | (b :: r, u) => (r, pc K t b r u)

omit hK in
theorem emb_eq_iter (t : ℕ) : ∀ r u, emb K t r u = ((stepE K t)^[r.length] (r, u)).2 := by
  intro r
  induction r with
  | nil => intro u; rfl
  | cons b r ih =>
    intro u
    rw [List.length_cons, Function.iterate_succ_apply]
    exact ih _

theorem stepE_primrec : Primrec (fun p : ℕ × (List Bool × ℕ) => stepE K p.1 p.2) := by
  have hh : Primrec₂ (fun (p : ℕ × (List Bool × ℕ)) (c : Bool × List Bool) =>
      (c.2, pc K p.1 c.1 c.2 p.2.2)) :=
    (Primrec.pair (Primrec.snd.comp Primrec.snd)
      ((pc_primrec K hK).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair (Primrec.snd.comp Primrec.snd)
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))))).to₂
  have h := Primrec.list_casesOn (f := fun p : ℕ × (List Bool × ℕ) => p.2.1)
    (g := fun p => p.2) (Primrec.fst.comp Primrec.snd) Primrec.snd hh
  exact h.of_eq fun p => by
    rcases p with ⟨t, ⟨_ | ⟨b, r⟩, u⟩⟩ <;> rfl

theorem emb_primrec :
    Primrec (fun a : ℕ × List Bool × ℕ => emb K a.1 a.2.1 a.2.2) := by
  have hstep : Primrec₂ (fun (a : ℕ × List Bool × ℕ) (st : List Bool × ℕ) =>
      stepE K a.1 st) :=
    ((stepE_primrec K hK).comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
  have it : Primrec (fun a : ℕ × List Bool × ℕ =>
      (stepE K a.1)^[a.2.1.length] (a.2.1, a.2.2)) :=
    Primrec.nat_iterate (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)) hstep
  exact (Primrec.snd.comp it).of_eq fun a => (emb_eq_iter K a.1 a.2.1 a.2.2).symm

omit hK in
/-- Decision procedure for membership of a pair in Levin's machine. -/
def regDec (K : ℕ → List Bool → ℕ) (a : Pair) : Bool :=
  bex (fun u => decide (emb K a.1.length a.2.reverse u = val a.1)) (K a.1.length a.2.reverse)

omit hK in
theorem regDec_iff (a : Pair) :
    regDec K a = true ↔ Reg K a.1.length a.2.reverse (val a.1) := by
  unfold regDec Reg
  rw [bex_iff]
  simp only [decide_eq_true_eq]

theorem regDec_computable : Computable (regDec K) := by
  have hlen : Primrec (fun p : Pair × ℕ => p.1.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)
  have hrev : Primrec (fun p : Pair × ℕ => p.1.2.reverse) :=
    Primrec.list_reverse.comp (Primrec.snd.comp Primrec.fst)
  have hembp : Primrec (fun p : Pair × ℕ => emb K p.1.1.length p.1.2.reverse p.2) :=
    (emb_primrec K hK).comp (Primrec.pair hlen (Primrec.pair hrev Primrec.snd))
  have hvalp : Primrec (fun p : Pair × ℕ => val p.1.1) :=
    val_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hf : Computable₂ (fun (a : Pair) (u : ℕ) =>
      decide (emb K a.1.length a.2.reverse u = val a.1)) :=
    ((PrimrecRel.comp Primrec.eq hembp hvalp).decide).to_comp.to₂
  have hg : Computable (fun a : Pair => K a.1.length a.2.reverse) :=
    (hK.comp (Primrec.pair (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_reverse.comp Primrec.snd))).to_comp
  exact computable_bex hf hg

end Computability

/-! ### Levin's machine -/

/-- Levin's machine for staged approximants `K`: the pairs `(q, x)` with `q` in the region
allocated to `x` at level `|q|`. -/
def levinMachine (K : ℕ → List Bool → ℕ) (h : Staged K)
    (hK : Primrec (fun p : ℕ × List Bool => K p.1 p.2)) : Machine where
  pairs := {a | Reg K a.1.length a.2.reverse (val a.1)}
  ce := by
    refine ⟨fun n => (Encodable.decode n : Option Pair).bind fun a =>
      bif regDec K a then some a else none, ?_, ?_⟩
    · exact Computable.option_bind Computable.decode
        (Computable.cond ((regDec_computable K hK).comp Computable.snd)
          (Computable.option_some.comp Computable.snd) (Computable.const none)).to₂
    · intro a
      constructor
      · intro ha
        refine ⟨Encodable.encode a, ?_⟩
        simp [(regDec_iff K a).mpr ha]
      · rintro ⟨n, hn⟩
        obtain ⟨a', _, h2⟩ := Option.bind_eq_some_iff.mp hn
        cases hd : regDec K a' <;> simp [hd] at h2
        subst h2
        exact (regDec_iff K a').mp hd
  consistent := by
    intro a ha b hb hab
    obtain ⟨s, hs⟩ := hab
    have ha' := reg_val_append h a.1 s ha
    rw [hs] at ha'
    rcases le_total a.2.length b.2.length with hl | hl
    · left
      exact List.reverse_suffix.mp (reg_suffix h (by simpa using hl) ha' hb)
    · right
      exact List.reverse_suffix.mp (reg_suffix h (by simpa using hl) hb ha')

theorem levin_produces_iff (K : ℕ → List Bool → ℕ) (h : Staged K)
    (hK : Primrec (fun p : ℕ × List Bool => K p.1 p.2)) (q x : List Bool) :
    (levinMachine K h hK).Produces q x ↔ Reg K q.length x.reverse (val q) := by
  constructor
  · rintro ⟨a, ha, ⟨s, hs⟩, ⟨y, hy⟩⟩
    have h1 := reg_val_append h a.1 s ha
    rw [hs, ← hy, List.reverse_append] at h1
    exact reg_append h _ h1
  · intro hr
    exact ⟨(q, x), hr, List.prefix_refl _, List.prefix_refl _⟩

theorem levin_cover (K : ℕ → List Bool → ℕ) (h : Staged K)
    (hK : Primrec (fun p : ℕ × List Bool => K p.1 p.2)) (x : List Bool) (n : ℕ) :
    cover ((levinMachine K h hK).Produces · x) n = K n x.reverse := by
  rw [cover_eq_card_range (R := Reg K n x.reverse) n
    (fun q hq => by rw [levin_produces_iff, hq])]
  have himg : ∀ inst : DecidablePred (Reg K n x.reverse),
      @Finset.filter _ (Reg K n x.reverse) inst (Finset.range (2 ^ n)) =
        (Finset.range (K n x.reverse)).image (emb K n x.reverse) := by
    intro inst
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Reg]
    constructor
    · rintro ⟨_, u, hu, he⟩
      exact ⟨u, hu, he⟩
    · rintro ⟨u, hu, he⟩
      exact ⟨he ▸ emb_lt h n _ u hu, u, hu, he⟩
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  intro u hu u' hu' he
  exact emb_inj h n _ u u' (by simpa using hu) (by simpa using hu') he

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 (⇐), Levin's construction, exact form: every
enumerable semimeasure is the Solomonoff semimeasure of a monotone machine (including at the
empty string, where `sm` is the measure of the programs on which the machine has any pair). -/
theorem exists_machine_sm_eq (μ : Semimeasure) (hμ : μ.Enumerable) :
    ∃ M : Machine, M.sm = μ := by
  obtain ⟨N, hNp, hroot, hext, hdbl, hsup⟩ := exists_stageApprox μ hμ
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → List Bool → ℕ, ∀ t r, K t r = N t r.reverse :=
    ⟨_, fun _ _ => rfl⟩
  have hS : Staged K :=
    ⟨fun t => by rw [hKdef]; exact hroot t,
      fun t r => by
        rw [hKdef, hKdef, hKdef, List.reverse_cons, List.reverse_cons]; exact hext t _,
      fun t r => by rw [hKdef, hKdef]; exact hdbl t _⟩
  have hKp : Primrec (fun p : ℕ × List Bool => K p.1 p.2) :=
    (hNp.comp (Primrec.pair Primrec.fst (Primrec.list_reverse.comp Primrec.snd))).of_eq
      fun p => (hKdef _ _).symm
  refine ⟨levinMachine K hS hKp, Semimeasure.ext fun x => ?_⟩
  rw [Machine.sm_apply, ← hsup x]
  unfold meas
  congr 1
  funext n
  rw [levin_cover K hS hKp x n, hKdef, List.reverse_reverse]

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 as stated there: a semimeasure is enumerable iff it
agrees with some `λ_T` off the empty string and its value at the empty string is lower
semicomputable. -/
theorem wsh_lemma6 (μ : Semimeasure) :
    μ.Enumerable ↔
      (∃ M : Machine, ∀ x, x ≠ [] → μ x = M.lam x) ∧
        LowerSemicomputable (fun _ : Unit => μ []) := by
  constructor
  · intro hμ
    obtain ⟨M, hM⟩ := exists_machine_sm_eq μ hμ
    refine ⟨⟨M, fun x hx => by rw [M.lam_of_ne hx, hM]⟩, ?_⟩
    exact LowerSemicomputable.comp' hμ (g := fun _ : Unit => ([] : List Bool))
      (Computable.const [])
  · rintro ⟨⟨M, hM⟩, φ0, c0, m0, s0⟩
    obtain ⟨φM, cM, mM, sM⟩ := sm_enumerable M
    refine ⟨fun x n => if x = [] then φ0 () n else φM x n, ?_, ?_, ?_⟩
    · have hc : Computable (fun p : List Bool × ℕ => decide (p.1 = [])) :=
        (PrimrecRel.comp Primrec.eq Primrec.fst (Primrec.const [])).decide.to_comp
      have h0 : Computable (fun p : List Bool × ℕ => φ0 () p.2) :=
        c0.comp (Computable.pair (Computable.const ()) Computable.snd)
      exact (Computable.cond hc h0 cM).of_eq fun p => by
        by_cases hp : p.1 = [] <;> simp [hp]
    · intro x
      by_cases hx : x = []
      · simp only [hx, ↓reduceIte]
        exact m0 ()
      · simp only [hx, ↓reduceIte]
        exact mM x
    · intro x
      by_cases hx : x = []
      · simp only [hx, ↓reduceIte]
        exact s0 ()
      · simp only [hx, ↓reduceIte]
        rw [hM x hx, M.lam_of_ne hx]
        exact sM x

end HsiLean.Monotone

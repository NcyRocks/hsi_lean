-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.Monotone

/-!
# WSH Lemma 6 (⇒), and an effective enumeration of all monotone machines

⚠️ UNAPPROVED. Statements and proofs: Claude (Fable 5.2), 2026-11-11. Not reviewed by Nathan.

* `sm_uniformlyEnumerable`, `sm_enumerable`: `λ_T` is lower semicomputable ("dovetail a search
  for programs with a lower approximation of the uniform measure": the stage-`t` approximant
  counts the length-`t` strings that extend a program among the first `t` enumerated pairs).
* `enumMachine`: an effective enumeration of ALL machines, from `Nat.Partrec.Code`, with a
  consistency freeze (a raw pair is kept only while the raw list so far is consistent).
-/

open ENNReal

namespace HsiLean.Monotone

open HsiLean.Wood

/-! ### Bounded search and counting, computably -/

/-- Number of `k < n` with `f k`. -/
def bcount (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bcount f n + (f n).toNat

/-- Whether some `k < n` has `f k`. -/
def bex (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => bex f n || f n

theorem bex_iff (f : ℕ → Bool) (n : ℕ) : bex f n = true ↔ ∃ k < n, f k = true := by
  induction n with
  | zero => simp [bex]
  | succ n ih =>
    simp only [bex, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact Or.inl ⟨k, hk, h⟩
      · exact Or.inr h

theorem bcount_eq (f : ℕ → Bool) (n : ℕ) :
    bcount f n = ((Finset.range n).filter (fun k => f k = true)).card := by
  induction n with
  | zero => simp [bcount]
  | succ n ih =>
    rw [bcount, ih, Finset.range_add_one, Finset.filter_insert]
    cases h : f n <;> simp [h]

variable {α : Type*} [Primcodable α]

theorem computable_bcount {f : α → ℕ → Bool} {g : α → ℕ} (hf : Computable₂ f)
    (hg : Computable g) : Computable (fun a => bcount (f a) (g a)) := by
  have hh : Computable₂ (fun (a : α) (p : ℕ × ℕ) => p.2 + (f a p.1).toNat) :=
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      ((Primrec.dom_bool Bool.toNat).to_comp.comp
        (hf.comp Computable.fst (Computable.fst.comp Computable.snd)))).to₂
  exact (Computable.nat_rec hg (Computable.const 0) hh).of_eq fun a => by
    induction g a <;> simp [bcount, *]

theorem computable_bex {f : α → ℕ → Bool} {g : α → ℕ} (hf : Computable₂ f)
    (hg : Computable g) : Computable (fun a => bex (f a) (g a)) := by
  have hh : Computable₂ (fun (a : α) (p : ℕ × Bool) => p.2 || f a p.1) :=
    (Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd)
        (hf.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  exact (Computable.nat_rec hg (Computable.const false) hh).of_eq fun a => by
    induction g a <;> simp [bex, *]

theorem LowerSemicomputable.comp' {β : Type*} [Primcodable β] {f : β → ℝ≥0∞}
    (hf : LowerSemicomputable f) {g : α → β} (hg : Computable g) :
    LowerSemicomputable (fun a => f (g a)) := by
  obtain ⟨φ, h1, h2, h3⟩ := hf
  exact ⟨fun a n => φ (g a) n,
    h1.comp (Computable.pair (hg.comp Computable.fst) Computable.snd),
    fun a => h2 (g a), fun a => h3 (g a)⟩

/-! ### Prefix tests on (length, value) codes -/

/-- (length, value) of a string. -/
def lv (x : List Bool) : ℕ × ℕ := (x.length, val x)

/-- Prefix test on (length, value) codes. -/
def preN (a b : ℕ × ℕ) : Bool := decide (a.1 ≤ b.1 ∧ b.2 / 2 ^ (b.1 - a.1) = a.2)

theorem preN_iff (p q : List Bool) : preN (lv p) (lv q) = true ↔ p <+: q := by
  unfold preN lv
  rw [decide_eq_true_eq, prefix_iff_val]

theorem val_primrec : Primrec val :=
  (Primrec.list_foldl (f := fun q : List Bool => q) (g := fun _ => 0)
    (h := fun _ (p : ℕ × Bool) => 2 * p.1 + p.2.toNat) Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd))
      ((Primrec.dom_bool Bool.toNat).comp (Primrec.snd.comp Primrec.snd))).to₂).of_eq
    fun _ => rfl

theorem lv_primrec : Primrec lv := Primrec.pair Primrec.list_length val_primrec

theorem preN_primrec : Primrec₂ preN := by
  have a1 : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) := Primrec.fst.comp Primrec.fst
  have a2 : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) := Primrec.snd.comp Primrec.fst
  have b1 : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) := Primrec.fst.comp Primrec.snd
  have b2 : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hle : PrimrecPred (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1 ≤ p.2.1) :=
    PrimrecRel.comp Primrec.nat_le a1 b1
  have hdiv : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2 / 2 ^ (p.2.1 - p.1.1)) :=
    Primrec.nat_div.comp b2 (Primrec.nat_pow.comp (Primrec.const 2) (Primrec.nat_sub.comp b1 a1))
  have heq : PrimrecPred (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2 / 2 ^ (p.2.1 - p.1.1) = p.1.2) :=
    PrimrecRel.comp Primrec.eq hdiv a2
  exact (hle.and heq).decide

/-! ### The stage approximant of `sm` -/

/-- Does pair `r.1` witness "`q ⊒ program` and `output ⊒ x`", where `r.2 = (x, lv q)`? -/
def hitT (r : Pair × (List Bool × (ℕ × ℕ))) : Bool :=
  preN (lv r.2.1) (lv r.1.2) && preN (lv r.1.1) r.2.2

/-- Same for an optional pair. -/
def hit (o : Option Pair) (x : List Bool) (t v : ℕ) : Bool :=
  (o.map fun a => hitT (a, x, t, v)).getD false

theorem hit_iff (o : Option Pair) (x q : List Bool) :
    hit o x q.length (val q) = true ↔ ∃ a, o = some a ∧ a.1 <+: q ∧ x <+: a.2 := by
  cases o with
  | none => simp [hit]
  | some a =>
    have : hit (some a) x q.length (val q) = (preN (lv x) (lv a.2) && preN (lv a.1) (lv q)) := rfl
    rw [this, Bool.and_eq_true, preN_iff, preN_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨a, rfl, h2, h1⟩
    · rintro ⟨a', h, h2, h1⟩; cases h; exact ⟨h1, h2⟩

theorem hitT_primrec : Primrec hitT := by
  have h1 : Primrec (fun r : Pair × (List Bool × (ℕ × ℕ)) => lv r.2.1) :=
    lv_primrec.comp (Primrec.fst.comp Primrec.snd)
  have h2 : Primrec (fun r : Pair × (List Bool × (ℕ × ℕ)) => lv r.1.2) :=
    lv_primrec.comp (Primrec.snd.comp Primrec.fst)
  have h3 : Primrec (fun r : Pair × (List Bool × (ℕ × ℕ)) => lv r.1.1) :=
    lv_primrec.comp (Primrec.fst.comp Primrec.fst)
  have h4 : Primrec (fun r : Pair × (List Bool × (ℕ × ℕ)) => r.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (preN_primrec.comp h1 h2) (preN_primrec.comp h3 h4)

/-- Stage-`t` approximant numerator: the number of length-`t` strings extending a program
among the first `t` enumerated pairs whose output extends `x`. -/
def approx (G : ℕ → Option Pair) (x : List Bool) (t : ℕ) : ℕ :=
  bcount (fun v => bex (fun j => hit (G j) x t v) t) (2 ^ t)

/-- Stage-`t` version of `Produces`. -/
def Stage (G : ℕ → Option Pair) (x : List Bool) (t : ℕ) (q : List Bool) : Prop :=
  ∃ j < t, ∃ a, G j = some a ∧ a.1 <+: q ∧ x <+: a.2

theorem approx_eq_cover (G : ℕ → Option Pair) (x : List Bool) (t : ℕ) :
    approx G x t = cover (Stage G x t) t := by
  classical
  have h : ∀ q : List Bool, q.length = t →
      (Stage G x t q ↔ bex (fun j => hit (G j) x t (val q)) t = true) := by
    intro q hq
    rw [bex_iff]
    subst hq
    exact exists_congr fun j => and_congr_right fun _ => (hit_iff _ _ _).symm
  rw [approx, bcount_eq,
    cover_eq_card_range (R := fun v => bex (fun j => hit (G j) x t v) t = true) t h]
  congr

theorem approx_computable {G : ℕ → ℕ → Option Pair} (hG : Computable₂ G) :
    Computable (fun p : (ℕ × List Bool) × ℕ => approx (G p.1.1) p.1.2 p.2) := by
  have hG' : Computable (fun s : (((ℕ × List Bool) × ℕ) × ℕ) × ℕ => G s.1.1.1.1 s.2) :=
    hG.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
      Computable.snd
  have hT : Computable₂ (fun (s : (((ℕ × List Bool) × ℕ) × ℕ) × ℕ) (a : Pair) =>
      hitT (a, s.1.1.1.2, s.1.1.2, s.1.2)) :=
    (hitT_primrec.to_comp.comp (Computable.pair Computable.snd
      (Computable.pair
        (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp
          (Computable.fst.comp Computable.fst))))
        (Computable.pair
          (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
          (Computable.snd.comp (Computable.fst.comp Computable.fst)))))).to₂
  have hhit : Computable₂ (fun (s : ((ℕ × List Bool) × ℕ) × ℕ) (j : ℕ) =>
      hit (G s.1.1.1 j) s.1.1.2 s.1.2 s.2) :=
    (Computable.option_getD (Computable.option_map hG' hT) (Computable.const false)).to₂
  have hbex : Computable₂ (fun (r : (ℕ × List Bool) × ℕ) (v : ℕ) =>
      bex (fun j => hit (G r.1.1 j) r.1.2 r.2 v) r.2) :=
    (computable_bex hhit (Computable.snd.comp Computable.fst)).to₂
  exact computable_bcount hbex
    (Primrec.nat_pow.to_comp.comp (Computable.const 2) Computable.snd)

theorem stage_spec (M : Machine) {g : ℕ → Option Pair}
    (hg : ∀ a, a ∈ M.pairs ↔ ∃ n, g n = some a) (x : List Bool) :
    Monotone (fun t => dyadic (approx g x t) t) ∧ ⨆ t, dyadic (approx g x t) t = M.sm x := by
  simp only [approx_eq_cover]
  refine meas_stage (P := fun q => M.Produces q x) (S := Stage g x) ?_ ?_ ?_
  · rintro t q b ⟨j, hj, a, ha, h1, h2⟩
    exact ⟨j, hj, a, ha, h1.trans (List.prefix_append q [b]), h2⟩
  · rintro s t hst q ⟨j, hj, h⟩
    exact ⟨j, by omega, h⟩
  · intro q
    constructor
    · rintro ⟨a, ha, h1, h2⟩
      obtain ⟨n, hn⟩ := (hg a).mp ha
      exact ⟨n + 1, n, by omega, a, hn, h1, h2⟩
    · rintro ⟨t, j, _, a, ha, h1, h2⟩
      exact ⟨a, (hg a).mpr ⟨j, ha⟩, h1, h2⟩

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 (⇒), uniform version: the Solomonoff semimeasures of
an effective family of machines are uniformly lower semicomputable. -/
theorem sm_uniformlyEnumerable {V : ℕ → Machine} (hV : UniformlyCE V) :
    UniformlyEnumerable (fun k => (V k).sm) := by
  obtain ⟨G, hG, hGp⟩ := hV
  refine ⟨fun p t => approx (G p.1) p.2 t, approx_computable hG, ?_, ?_⟩
  · intro p
    exact (stage_spec (V p.1) (hGp p.1) p.2).1
  · intro p
    exact (stage_spec (V p.1) (hGp p.1) p.2).2

/-- [UNAPPROVED STATEMENT] WSH Lemma 6 (⇒): `λ_T` is lower semicomputable. -/
theorem sm_enumerable (M : Machine) : M.sm.Enumerable := by
  obtain ⟨g, hg, hgp⟩ := M.ce
  have hV : UniformlyCE (fun _ => M) :=
    ⟨fun _ n => g n, hg.comp Computable.snd, fun _ a => hgp a⟩
  have h := LowerSemicomputable.comp' (sm_uniformlyEnumerable hV)
    (g := fun x : List Bool => ((0 : ℕ), x)) (Computable.pair (Computable.const 0) Computable.id)
  exact h

/-! ### An effective enumeration of all machines -/

/-- The raw pair enumerated by code `e` at index `n = ⟨steps, input⟩`. -/
noncomputable def rawPair (e n : ℕ) : Option Pair :=
  (Nat.Partrec.Code.evaln n.unpair.1 (codeOf e) n.unpair.2).bind
    fun v => (Encodable.decode v : Option Pair)

/-- Two pairs do not violate monotonicity (in the direction `a.1 ⪯ b.1`). -/
def cmpB (a b : Pair) : Bool :=
  !(preN (lv a.1) (lv b.1)) || (preN (lv a.2) (lv b.2) || preN (lv b.2) (lv a.2))

theorem cmpB_iff (a b : Pair) :
    cmpB a b = true ↔ (a.1 <+: b.1 → (a.2 <+: b.2 ∨ b.2 <+: a.2)) := by
  rw [← preN_iff, ← preN_iff, ← preN_iff]
  unfold cmpB
  cases preN (lv a.1) (lv b.1) <;> cases preN (lv a.2) (lv b.2) <;>
    cases preN (lv b.2) (lv a.2) <;> simp

/-- `cmpB` lifted to optional pairs (`true` if either is missing). -/
def okO (o o' : Option Pair) : Bool :=
  (o.bind fun a => o'.map fun b => cmpB a b).getD true

/-- The first `n + 1` raw pairs of code `e` are pairwise consistent. -/
noncomputable def good (e n : ℕ) : Bool :=
  !(bex (fun i => bex (fun j => !(okO (rawPair e i) (rawPair e j))) (n + 1)) (n + 1))

theorem good_iff (e n : ℕ) :
    good e n = true ↔ ∀ i ≤ n, ∀ j ≤ n, ∀ a b, rawPair e i = some a → rawPair e j = some b →
      a.1 <+: b.1 → (a.2 <+: b.2 ∨ b.2 <+: a.2) := by
  unfold good
  rw [Bool.not_eq_true', ← Bool.not_eq_true, bex_iff]
  simp only [bex_iff, not_exists, not_and, Bool.not_eq_true', Bool.not_eq_false]
  constructor
  · intro h i hi j hj a b ha hb
    have := h i (by omega) j (by omega)
    rw [ha, hb] at this
    exact (cmpB_iff a b).mp this
  · intro h i hi j hj
    cases ha : rawPair e i with
    | none => rfl
    | some a =>
      cases hb : rawPair e j with
      | none => rfl
      | some b => exact (cmpB_iff a b).mpr (h i (by omega) j (by omega) a b ha hb)

/-- The filtered enumerator: raw pairs, frozen at the first inconsistency. -/
noncomputable def enumG (e n : ℕ) : Option Pair := bif good e n then rawPair e n else none

theorem rawPair_primrec : Primrec₂ rawPair := by
  have h1 : Primrec (fun p : ℕ × ℕ => ((p.2.unpair.1, codeOf p.1), p.2.unpair.2)) :=
    Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.fst))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  exact Primrec.option_bind (Nat.Partrec.Code.primrec_evaln.comp h1)
    (Primrec.decode.comp Primrec.snd).to₂

theorem cmpB_primrec : Primrec₂ cmpB := by
  have a1 : Primrec (fun p : Pair × Pair => lv p.1.1) :=
    lv_primrec.comp (Primrec.fst.comp Primrec.fst)
  have a2 : Primrec (fun p : Pair × Pair => lv p.1.2) :=
    lv_primrec.comp (Primrec.snd.comp Primrec.fst)
  have b1 : Primrec (fun p : Pair × Pair => lv p.2.1) :=
    lv_primrec.comp (Primrec.fst.comp Primrec.snd)
  have b2 : Primrec (fun p : Pair × Pair => lv p.2.2) :=
    lv_primrec.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.or.comp (Primrec.not.comp (preN_primrec.comp a1 b1))
    (Primrec.or.comp (preN_primrec.comp a2 b2) (preN_primrec.comp b2 a2))

theorem okO_primrec : Primrec₂ okO := by
  have inner : Primrec₂ (fun (p : Option Pair × Option Pair) (a : Pair) =>
      p.2.map fun b => cmpB a b) :=
    (Primrec.option_map (Primrec.snd.comp Primrec.fst)
      (cmpB_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact Primrec.option_getD.comp (Primrec.option_bind Primrec.fst inner) (Primrec.const true)

theorem good_computable : Computable₂ good := by
  have hraw_i : Computable (fun s : ((ℕ × ℕ) × ℕ) × ℕ => rawPair s.1.1.1 s.1.2) :=
    rawPair_primrec.to_comp.comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst)
  have hraw_j : Computable (fun s : ((ℕ × ℕ) × ℕ) × ℕ => rawPair s.1.1.1 s.2) :=
    rawPair_primrec.to_comp.comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd
  have hin : Computable₂ (fun (s : (ℕ × ℕ) × ℕ) (j : ℕ) =>
      !(okO (rawPair s.1.1 s.2) (rawPair s.1.1 j))) :=
    (Primrec.not.to_comp.comp (okO_primrec.to_comp.comp hraw_i hraw_j)).to₂
  have hn1 : Computable (fun s : (ℕ × ℕ) × ℕ => s.1.2 + 1) :=
    Computable.succ.comp (Computable.snd.comp Computable.fst)
  have hmid : Computable₂ (fun (p : ℕ × ℕ) (i : ℕ) =>
      bex (fun j => !(okO (rawPair p.1 i) (rawPair p.1 j))) (p.2 + 1)) :=
    (computable_bex hin hn1).to₂
  exact Primrec.not.to_comp.comp
    (computable_bex hmid (Computable.succ.comp Computable.snd))

theorem enumG_computable : Computable₂ enumG :=
  Computable.cond good_computable rawPair_primrec.to_comp (Computable.const none)

theorem enumG_some {e n : ℕ} {a : Pair} (h : enumG e n = some a) :
    good e n = true ∧ rawPair e n = some a := by
  unfold enumG at h
  cases hg : good e n <;> simp [hg] at h
  exact ⟨rfl, h⟩

/-- [UNAPPROVED STATEMENT] An effective enumeration of ALL monotone machines: the `e`-th
machine has the pairs enumerated by the `e`-th partial recursive code, up to (excluding)
the first index at which the list so far stops being consistent. -/
noncomputable def enumMachine (e : ℕ) : Machine where
  pairs := {a | ∃ n, enumG e n = some a}
  ce := ⟨enumG e, enumG_computable.comp (Computable.const e) Computable.id, fun _ => Iff.rfl⟩
  consistent := by
    rintro a ⟨n, hn⟩ b ⟨m, hm⟩ hab
    obtain ⟨gn, rn⟩ := enumG_some hn
    obtain ⟨gm, rm⟩ := enumG_some hm
    rcases le_total n m with h | h
    · exact (good_iff e m).mp gm n h m le_rfl a b rn rm hab
    · exact (good_iff e n).mp gn n le_rfl m h a b rn rm hab

/-- [UNAPPROVED STATEMENT] The enumeration is effective. -/
theorem enumMachine_uniformlyCE : UniformlyCE enumMachine :=
  ⟨enumG, enumG_computable, fun _ _ => Iff.rfl⟩

/-- [UNAPPROVED STATEMENT] Every machine is listed. -/
theorem enumMachine_complete (M : Machine) : ∃ e, enumMachine e = M := by
  obtain ⟨g, hg, hgp⟩ := M.ce
  have hpart : Partrec (fun n : ℕ => (((g n).map Encodable.encode : Option ℕ) : Part ℕ)) :=
    Computable.ofOption (Computable.option_map hg (Computable.encode.comp Computable.snd).to₂)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hpart)
  refine ⟨Encodable.encode c, Machine.ext ?_⟩
  have hcodeOf : codeOf (Encodable.encode c) = c :=
    Denumerable.ofNat_encode (α := Nat.Partrec.Code) c
  set e := Encodable.encode c
  have hraw : ∀ n a, rawPair e n = some a → a ∈ M.pairs := by
    intro n a h
    unfold rawPair at h
    rw [hcodeOf] at h
    obtain ⟨v, hv, hd⟩ := Option.bind_eq_some_iff.mp h
    have hmem := Nat.Partrec.Code.evaln_sound hv
    rw [hc] at hmem
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp (Part.mem_coe.mp hmem)
    rw [Encodable.encodek] at hd
    cases hd
    exact (hgp _).mpr ⟨_, ha'⟩
  have hgood : ∀ n, good e n = true := fun n =>
    (good_iff e n).mpr fun i _ j _ a b ha hb =>
      M.consistent a (hraw i a ha) b (hraw j b hb)
  ext a
  constructor
  · rintro ⟨n, hn⟩
    exact hraw n a (enumG_some hn).2
  · intro ha
    obtain ⟨m, hm⟩ := (hgp a).mp ha
    have hmem : Encodable.encode a ∈ Nat.Partrec.Code.eval c m := by
      rw [hc]; exact Part.mem_coe.mpr (by simp [hm])
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    have hr : rawPair e (Nat.pair k m) = some a := by
      unfold rawPair
      simp only [Nat.unpair_pair, hcodeOf]
      rw [Option.mem_def.mp hk]
      exact Encodable.encodek a
    refine ⟨Nat.pair k m, ?_⟩
    unfold enumG
    rw [hgood, hr]
    rfl

end HsiLean.Monotone

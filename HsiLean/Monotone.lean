-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-11 and has NOT been reviewed by Nathan.
import HsiLean.Wood

/-!
# Monotone machines and their Solomonoff semimeasures

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
It is a semimeasure. NOTE `M.sm []` is the measure of the programs on which the machine has
any pair at all (possibly with empty output), which may be `< 1`.

`M.lam x` : WSH's `λ_T` / the paper's `P_M`: `1` at the empty string, `M.sm x` elsewhere.

This file: the model, `sm` is a semimeasure, the split of a measure along a prefix-free
code (`meas_prefixCode`), WSH Lemma 6 (⇒) (`sm_uniformlyEnumerable`), and an effective
enumeration of all machines (`enumMachine`). Lemma 6 (⇐) is in `Levin.lean`.
-/

open ENNReal

namespace HsiLean.Monotone

open HsiLean.Wood

/-! ### Bit strings as numbers -/

/-- Big-endian value of a bit string. -/
def val (q : List Bool) : ℕ := q.foldl (fun a b => 2 * a + b.toNat) 0

@[simp] theorem val_nil : val [] = 0 := rfl

theorem val_concat (q : List Bool) (b : Bool) : val (q ++ [b]) = 2 * val q + b.toNat := by
  simp [val, List.foldl_append]

theorem val_append (p s : List Bool) : val (p ++ s) = val p * 2 ^ s.length + val s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s b ih =>
    rw [← List.append_assoc, val_concat, ih, val_concat]
    simp [pow_succ]
    ring

theorem val_lt (q : List Bool) : val q < 2 ^ q.length := by
  induction q using List.reverseRecOn with
  | nil => simp
  | append_singleton q b ih =>
    rw [val_concat]
    have hb : b.toNat ≤ 1 := Bool.toNat_le b
    simp only [List.length_append, List.length_singleton, pow_succ]
    omega

theorem eq_nil_or_snoc (q : List Bool) : q = [] ∨ ∃ q' c, q = q' ++ [c] := by
  rcases List.eq_nil_or_concat q with h | ⟨q', c, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨q', c, by rw [h, List.concat_eq_append]⟩

theorem val_inj {p q : List Bool} (hl : p.length = q.length) (hv : val p = val q) : p = q := by
  induction p using List.reverseRecOn generalizing q with
  | nil =>
    simp at hl
    exact (List.length_eq_zero_iff.mp hl.symm).symm
  | append_singleton p b ih =>
    obtain ⟨q', c, rfl⟩ : ∃ q' c, q = q' ++ [c] := by
      rcases eq_nil_or_snoc q with rfl | h
      · simp at hl
      · exact h
    simp only [List.length_append, List.length_singleton, _root_.add_left_inj] at hl
    rw [val_concat, val_concat] at hv
    have hb : b = c := by
      cases b <;> cases c <;> simp at hv ⊢ <;> omega
    subst hb
    have : val p = val q' := by omega
    rw [ih hl this]

theorem exists_val_eq (n v : ℕ) (hv : v < 2 ^ n) : ∃ q : List Bool, q.length = n ∧ val q = v := by
  induction n generalizing v with
  | zero => exact ⟨[], rfl, by simp at hv; simp [hv]⟩
  | succ n ih =>
    obtain ⟨q, hq, hqv⟩ := ih (v / 2) (by rw [pow_succ] at hv; omega)
    refine ⟨q ++ [decide (v % 2 = 1)], by simp [hq], ?_⟩
    rw [val_concat, hqv]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h] <;> omega

theorem prefix_iff_val (p q : List Bool) :
    p <+: q ↔ p.length ≤ q.length ∧ val q / 2 ^ (q.length - p.length) = val p := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [val_append]
    simp only [List.length_append, Nat.add_sub_cancel_left]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (val_lt s),
      zero_add]
  · rintro ⟨hl, hv⟩
    obtain ⟨p', s, rfl, hlen⟩ : ∃ p' s, q = p' ++ s ∧ p'.length = p.length :=
      ⟨q.take p.length, q.drop p.length, (List.take_append_drop _ _).symm, by simp [hl]⟩
    simp only [List.length_append, hlen, Nat.add_sub_cancel_left] at hv
    rw [val_append, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (val_lt s), zero_add] at hv
    have := val_inj hlen hv
    subst this
    exact List.prefix_append _ _

/-! ### Counting strings -/

/-- All binary strings of length `n`. -/
def strs : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (strs n).image (· ++ [false]) ∪ (strs n).image (· ++ [true])

theorem mem_strs {n : ℕ} {q : List Bool} : q ∈ strs n ↔ q.length = n := by
  induction n generalizing q with
  | zero => simp [strs]
  | succ n ih =>
    simp only [strs, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> simp [ih.mp ha]
    · intro hq
      rcases eq_nil_or_snoc q with rfl | ⟨q', c, rfl⟩
      · simp at hq
      · simp only [List.length_append, List.length_singleton, _root_.add_left_inj] at hq
        cases c
        · exact Or.inl ⟨q', ih.mpr hq, rfl⟩
        · exact Or.inr ⟨q', ih.mpr hq, rfl⟩

open Classical in
/-- The number of length-`n` strings satisfying `P`. -/
noncomputable def cover (P : List Bool → Prop) (n : ℕ) : ℕ := ((strs n).filter P).card

theorem concat_injective (b : Bool) : Function.Injective (fun q : List Bool => q ++ [b]) :=
  List.append_left_injective [b]

open Classical in
theorem cover_succ (P : List Bool → Prop) (n : ℕ) :
    cover P (n + 1) = cover (fun q => P (q ++ [false])) n + cover (fun q => P (q ++ [true])) n := by
  unfold cover
  rw [strs, Finset.filter_union, Finset.filter_image, Finset.filter_image,
    Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (concat_injective false),
    Finset.card_image_of_injective _ (concat_injective true)]
  rw [Finset.disjoint_left]
  intro q h0 h1
  simp only [Finset.mem_image, Finset.mem_filter] at h0 h1
  obtain ⟨a, _, rfl⟩ := h0
  obtain ⟨b, _, hb⟩ := h1
  have := List.append_inj' hb rfl
  simp at this

open Classical in
theorem cover_mono {P Q : List Bool → Prop} (h : ∀ q, P q → Q q) (n : ℕ) :
    cover P n ≤ cover Q n :=
  Finset.card_le_card fun q hq => by
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, h q hq.2⟩

open Classical in
theorem cover_le (P : List Bool → Prop) (n : ℕ) : cover P n ≤ 2 ^ n := by
  induction n generalizing P with
  | zero => unfold cover; exact (Finset.card_filter_le _ _).trans (by simp [strs])
  | succ n ih =>
    rw [cover_succ, pow_succ]
    have := ih (fun q => P (q ++ [false]))
    have := ih (fun q => P (q ++ [true]))
    omega

theorem cover_true (n : ℕ) : cover (fun _ => True) n = 2 ^ n := by
  induction n with
  | zero => simp [cover, strs]
  | succ n ih => rw [cover_succ, ih, pow_succ]; omega

open Classical in
theorem cover_add_le {P Q R : List Bool → Prop} (hd : ∀ q, P q → Q q → False)
    (hP : ∀ q, P q → R q) (hQ : ∀ q, Q q → R q) (n : ℕ) :
    cover P n + cover Q n ≤ cover R n := by
  unfold cover
  rw [← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card fun q hq => ?_
    simp only [Finset.mem_union, Finset.mem_filter] at hq ⊢
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, hP q h2⟩
    · exact ⟨h1, hQ q h2⟩
  · rw [Finset.disjoint_left]
    intro q h0 h1
    simp only [Finset.mem_filter] at h0 h1
    exact hd q h0.2 h1.2

/-- `P` is closed under extending the string. -/
def UpClosed (P : List Bool → Prop) : Prop := ∀ q b, P q → P (q ++ [b])

theorem UpClosed.append {P : List Bool → Prop} (hP : UpClosed P) {q : List Bool} (hq : P q)
    (s : List Bool) : P (q ++ s) := by
  induction s using List.reverseRecOn with
  | nil => simpa using hq
  | append_singleton s b ih => rw [← List.append_assoc]; exact hP _ b ih

theorem cover_double_le {P : List Bool → Prop} (hP : UpClosed P) (n : ℕ) :
    2 * cover P n ≤ cover P (n + 1) := by
  rw [cover_succ]
  have := cover_mono (fun q hq => hP q false hq) n
  have := cover_mono (fun q hq => hP q true hq) n
  omega

/-- [UNAPPROVED STATEMENT] The uniform measure of the set of infinite strings having a
finite prefix in `P` (for `P` closed under extension), by counting. -/
noncomputable def meas (P : List Bool → Prop) : ℝ≥0∞ := ⨆ n, dyadic (cover P n) n

theorem dyadic_le_succ {a b : ℕ} (h : 2 * a ≤ b) (n : ℕ) : dyadic a n ≤ dyadic b (n + 1) := by
  rw [← dyadic_double_succ]
  exact dyadic_mono_num h

theorem dyadic_le_one {k n : ℕ} (h : k ≤ 2 ^ n) : dyadic k n ≤ 1 := by
  unfold dyadic
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  exact_mod_cast h

theorem cover_dyadic_mono {P : List Bool → Prop} (hP : UpClosed P) :
    Monotone (fun n => dyadic (cover P n) n) :=
  monotone_nat_of_le_succ fun n => dyadic_le_succ (cover_double_le hP n) n

theorem meas_le_one (P : List Bool → Prop) : meas P ≤ 1 :=
  iSup_le fun n => dyadic_le_one (cover_le P n)

theorem meas_true : meas (fun _ => True) = 1 := by
  refine le_antisymm (meas_le_one _) ?_
  refine le_trans ?_ (le_iSup _ 0)
  simp [cover_true, dyadic]

theorem meas_mono {P Q : List Bool → Prop} (h : ∀ q, P q → Q q) : meas P ≤ meas Q :=
  iSup_mono fun n => dyadic_mono_num (cover_mono h n)

theorem meas_add_le {P Q R : List Bool → Prop} (hPc : UpClosed P) (hQc : UpClosed Q)
    (hd : ∀ q, P q → Q q → False) (hP : ∀ q, P q → R q) (hQ : ∀ q, Q q → R q) :
    meas P + meas Q ≤ meas R := by
  unfold meas
  rw [ENNReal.iSup_add_iSup_of_monotone (cover_dyadic_mono hPc) (cover_dyadic_mono hQc)]
  refine iSup_mono fun n => ?_
  rw [← dyadic_add]
  exact dyadic_mono_num (cover_add_le hd hP hQ n)

/-! ### Machines -/

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

theorem Machine.ext {M N : Machine} (h : M.pairs = N.pairs) : M = N := by
  cases M; cases N; simp only at h; subst h; rfl

/-- [UNAPPROVED STATEMENT] `M(q) ⊒ x`: on input `q` the machine's output extends `x`. -/
def Machine.Produces (M : Machine) (q x : List Bool) : Prop :=
  ∃ a ∈ M.pairs, a.1 <+: q ∧ x <+: a.2

theorem Machine.produces_upClosed (M : Machine) (x : List Bool) : UpClosed (M.Produces · x) := by
  rintro q b ⟨a, ha, h1, h2⟩
  exact ⟨a, ha, h1.trans (List.prefix_append q [b]), h2⟩

theorem Machine.produces_of_prefix (M : Machine) {q x y : List Bool} (hxy : x <+: y)
    (h : M.Produces q y) : M.Produces q x := by
  obtain ⟨a, ha, h1, h2⟩ := h
  exact ⟨a, ha, h1, hxy.trans h2⟩

theorem Machine.produces_disjoint (M : Machine) (q x : List Bool)
    (h0 : M.Produces q (x ++ [false])) (h1 : M.Produces q (x ++ [true])) : False := by
  obtain ⟨a, ha, ha1, ha2⟩ := h0
  obtain ⟨b, hb, hb1, hb2⟩ := h1
  have key : ∀ y : List Bool, x ++ [false] <+: y → x ++ [true] <+: y → False := by
    intro y h h'
    rcases List.prefix_or_prefix_of_prefix h h' with h3 | h3
    · have := h3.eq_of_length (by simp)
      simp at this
    · have := h3.eq_of_length (by simp)
      simp at this
  rcases List.prefix_or_prefix_of_prefix ha1 hb1 with h | h
  · rcases M.consistent a ha b hb h with h' | h'
    · exact key _ (ha2.trans h') hb2
    · exact key _ ha2 (hb2.trans h')
  · rcases M.consistent b hb a ha h with h' | h'
    · exact key _ ha2 (hb2.trans h')
    · exact key _ (ha2.trans h') hb2

/-- [UNAPPROVED STATEMENT] The Solomonoff semimeasure of a machine, as a `Semimeasure`. -/
noncomputable def Machine.sm (M : Machine) : Semimeasure where
  toFun x := meas (M.Produces · x)
  empty_le_one := meas_le_one _
  extend_le x :=
    meas_add_le (M.produces_upClosed _) (M.produces_upClosed _) (M.produces_disjoint · x)
      (fun _ h => M.produces_of_prefix (List.prefix_append x [false]) h)
      (fun _ h => M.produces_of_prefix (List.prefix_append x [true]) h)

theorem Machine.sm_apply (M : Machine) (x : List Bool) : M.sm x = meas (M.Produces · x) := rfl

/-- [UNAPPROVED STATEMENT] WSH's `λ_T` / the paper's `P_M`: `1` on the empty string. -/
noncomputable def Machine.lam (M : Machine) (x : List Bool) : ℝ≥0∞ :=
  if x = [] then 1 else M.sm x

theorem Machine.lam_of_ne (M : Machine) {x : List Bool} (hx : x ≠ []) : M.lam x = M.sm x := by
  simp [Machine.lam, hx]

/-- [UNAPPROVED STATEMENT] An effective family of machines: one computable procedure
enumerates the pairs of every `V k`. -/
def UniformlyCE (V : ℕ → Machine) : Prop :=
  ∃ G : ℕ → ℕ → Option Pair, Computable₂ G ∧ ∀ k a, a ∈ (V k).pairs ↔ ∃ n, G k n = some a

/-! ### Counting by numeric value, and measures of staged unions -/

open Classical in
theorem cover_eq_card_range {P : List Bool → Prop} {R : ℕ → Prop} (n : ℕ)
    (h : ∀ q : List Bool, q.length = n → (P q ↔ R (val q))) :
    cover P n = ((Finset.range (2 ^ n)).filter R).card := by
  unfold cover
  refine Finset.card_bij (fun q _ => val q) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, mem_strs] at hq
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hq.1 ▸ val_lt q, (h q hq.1).mp hq.2⟩
  · intro q hq q' hq' hv
    simp only [Finset.mem_filter, mem_strs] at hq hq'
    exact val_inj (hq.1.trans hq'.1.symm) hv
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    obtain ⟨q, hq, rfl⟩ := exists_val_eq n v hv.1
    exact ⟨q, by simp only [Finset.mem_filter, mem_strs]; exact ⟨hq, (h q hq).mpr hv.2⟩, rfl⟩

/-- If `P` is the increasing union of extension-closed stages `S t`, its measure is the
supremum of the level-`t` counts of the stage-`t` sets. -/
theorem meas_stage {P : List Bool → Prop} {S : ℕ → List Bool → Prop}
    (hS : ∀ t, UpClosed (S t)) (hmono : ∀ s t, s ≤ t → ∀ q, S s q → S t q)
    (hP : ∀ q, P q ↔ ∃ t, S t q) :
    Monotone (fun t => dyadic (cover (S t) t) t) ∧ ⨆ t, dyadic (cover (S t) t) t = meas P := by
  have hm : Monotone (fun t => dyadic (cover (S t) t) t) :=
    monotone_nat_of_le_succ fun t =>
      (dyadic_le_succ (cover_double_le (hS t) t) t).trans
        (dyadic_mono_num (cover_mono (hmono t (t + 1) (Nat.le_succ t)) (t + 1)))
  refine ⟨hm, le_antisymm (iSup_le fun t => ?_) (iSup_le fun n => ?_)⟩
  · exact (dyadic_mono_num (cover_mono (fun q hq => (hP q).mpr ⟨t, hq⟩) t)).trans
      (le_iSup (fun n => dyadic (cover P n) n) t)
  · classical
    let f : List Bool → ℕ := fun q => if h : P q then Classical.choose ((hP q).mp h) else 0
    let T := max ((strs n).sup f) n
    have h1 : cover P n ≤ cover (S T) n := by
      unfold cover
      refine Finset.card_le_card fun q hq => ?_
      simp only [Finset.mem_filter] at hq ⊢
      refine ⟨hq.1, ?_⟩
      have hc : S (f q) q := by
        simp only [f, dif_pos hq.2]
        exact Classical.choose_spec ((hP q).mp hq.2)
      exact hmono _ _ ((Finset.le_sup hq.1).trans (le_max_left _ _)) q hc
    calc dyadic (cover P n) n ≤ dyadic (cover (S T) n) n := dyadic_mono_num h1
      _ ≤ dyadic (cover (S T) T) T := cover_dyadic_mono (hS T) (le_max_right _ _)
      _ ≤ _ := le_iSup (fun t => dyadic (cover (S t) t) t) T

/-! ### Splitting a measure along a prefix-free code -/

/-- `q` is `p` followed by a string satisfying `P`. -/
def Shift (p : List Bool) (P : List Bool → Prop) (q : List Bool) : Prop :=
  ∃ s, q = p ++ s ∧ P s

theorem shift_upClosed (p : List Bool) {P : List Bool → Prop} (hP : UpClosed P) :
    UpClosed (Shift p P) := by
  rintro q b ⟨s, rfl, hs⟩
  exact ⟨s ++ [b], by simp, hP s b hs⟩

open Classical in
theorem cover_shift (p : List Bool) (P : List Bool → Prop) (m : ℕ) :
    cover (Shift p P) (p.length + m) = cover P m := by
  unfold cover
  have : (strs (p.length + m)).filter (Shift p P) = ((strs m).filter P).image (p ++ ·) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, mem_strs, Shift]
    constructor
    · rintro ⟨hl, s, rfl, hs⟩
      exact ⟨s, ⟨by simpa using hl, hs⟩, rfl⟩
    · rintro ⟨s, ⟨hl, hs⟩, rfl⟩
      exact ⟨by simp [hl], s, rfl, hs⟩
  rw [this, Finset.card_image_of_injective _ (List.append_right_injective p)]

open Classical in
theorem cover_shift_of_lt (p : List Bool) (P : List Bool → Prop) {n : ℕ} (h : n < p.length) :
    cover (Shift p P) n = 0 := by
  unfold cover
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro q hq ⟨s, rfl, _⟩
  rw [mem_strs] at hq
  simp at hq
  omega

theorem dyadic_add_exp (k a m : ℕ) : dyadic k (a + m) = (2⁻¹ : ℝ≥0∞) ^ a * dyadic k m := by
  unfold dyadic
  have h0 : (2 : ℝ≥0∞) ^ a ≠ 0 := by positivity
  have ht : (2 : ℝ≥0∞) ^ a ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [pow_add, ← ENNReal.inv_pow, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl h0) (Or.inl ht)]
  ring

/-- Prepending a fixed string `p` scales the measure by `2 ^ -|p|`. -/
theorem meas_shift (p : List Bool) (P : List Bool → Prop) :
    meas (Shift p P) = (2⁻¹ : ℝ≥0∞) ^ p.length * meas P := by
  unfold meas
  rw [ENNReal.mul_iSup]
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun m => ?_)
  · rcases lt_or_ge n p.length with h | h
    · rw [cover_shift_of_lt p P h]
      simp [dyadic]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [cover_shift, dyadic_add_exp]
      exact le_iSup (fun m => (2⁻¹ : ℝ≥0∞) ^ p.length * dyadic (cover P m) m) m
  · rw [← dyadic_add_exp, ← cover_shift p P m]
    exact le_iSup (fun n => dyadic (cover (Shift p P) n) n) (p.length + m)

theorem dyadic_finset_sum {ι : Type*} (F : Finset ι) (a : ι → ℕ) (n : ℕ) :
    ∑ k ∈ F, dyadic (a k) n = dyadic (∑ k ∈ F, a k) n := by
  unfold dyadic
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, Nat.cast_sum]

/-- [UNAPPROVED STATEMENT] The measure of a disjoint union of shifted sets along a
prefix-free code `I` is the `2 ^ -|I k|`-weighted sum of the measures. With `P k = True`
this is Kraft's inequality. -/
theorem meas_prefixCode (I : ℕ → List Bool) (hI : ∀ i j, I i <+: I j → i = j)
    (P : ℕ → List Bool → Prop) (hP : ∀ k, UpClosed (P k)) :
    meas (fun q => ∃ k, Shift (I k) (P k) q) =
      ∑' k, (2⁻¹ : ℝ≥0∞) ^ (I k).length * meas (P k) := by
  classical
  simp_rw [← meas_shift]
  have e1 : ∀ (R : List Bool → Prop) (n : ℕ),
      cover R n = ∑ q ∈ strs n, if R q then 1 else 0 := by
    intro R n
    unfold cover
    rw [Finset.card_filter]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    have key : (cover (fun q => ∃ k, Shift (I k) (P k) q) n : ℝ≥0∞) ≤
        ∑' k, (cover (Shift (I k) (P k)) n : ℝ≥0∞) := by
      simp_rw [e1, Nat.cast_sum]
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine Finset.sum_le_sum fun q _ => ?_
      split_ifs with h
      · obtain ⟨k, hk⟩ := h
        exact le_trans (by simp [hk]) (ENNReal.le_tsum k)
      · simp
    calc dyadic (cover (fun q => ∃ k, Shift (I k) (P k) q) n) n
        ≤ (∑' k, (cover (Shift (I k) (P k)) n : ℝ≥0∞)) / 2 ^ n :=
          ENNReal.div_le_div_right key _
      _ = ∑' k, dyadic (cover (Shift (I k) (P k)) n) n := by
          unfold dyadic
          simp only [div_eq_mul_inv]
          rw [ENNReal.tsum_mul_right]
      _ ≤ ∑' k, meas (Shift (I k) (P k)) :=
          ENNReal.tsum_le_tsum fun k =>
            le_iSup (fun n => dyadic (cover (Shift (I k) (P k)) n) n) n
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    have hm : ∀ k, Monotone (fun n => dyadic (cover (Shift (I k) (P k)) n) n) :=
      fun k => cover_dyadic_mono (shift_upClosed (I k) (hP k))
    change ∑ k ∈ F, (⨆ n, dyadic (cover (Shift (I k) (P k)) n) n) ≤ _
    rw [ENNReal.finsetSum_iSup_of_monotone hm]
    refine iSup_mono fun n => ?_
    rw [dyadic_finset_sum]
    refine dyadic_mono_num ?_
    simp_rw [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun q _ => ?_
    have uniq : ∀ k k', Shift (I k) (P k) q → Shift (I k') (P k') q → k = k' := by
      rintro k k' ⟨s, hs, _⟩ ⟨s', hs', _⟩
      have h1 : I k <+: q := hs ▸ List.prefix_append _ _
      have h2 : I k' <+: q := hs' ▸ List.prefix_append _ _
      rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
      · exact hI _ _ h
      · exact (hI _ _ h).symm
    by_cases hex : ∃ k ∈ F, Shift (I k) (P k) q
    · obtain ⟨k0, hk0, hq0⟩ := hex
      rw [Finset.sum_eq_single_of_mem k0 hk0
        (fun k _ hne => if_neg fun hk => hne (uniq k k0 hk hq0))]
      rw [if_pos hq0, if_pos ⟨k0, hq0⟩]
    · rw [Finset.sum_eq_zero fun k hk => if_neg fun h => hex ⟨k, hk, h⟩]
      exact Nat.zero_le _

end HsiLean.Monotone

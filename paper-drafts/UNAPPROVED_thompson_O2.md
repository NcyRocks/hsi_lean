⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-12 and has NOT been reviewed by Nathan.

# O2: does Thompson sampling's log loss on the optimal action vanish under a uniform gap?

Source question: `PIBBSS/notes/queue/rl-logloss-vs-solind-2026-11-11.md`, OPEN item (O2).
Lean: `HsiLean/ThompsonO2.lean` (what is and is not formalised is recorded there and in RUN-REPORT.md).

**Answer as far as this draft goes.**
- Deterministic class, deterministic optimal policies: **yes**. Finite class: the loss is even *summable*,
  `Σ_t E[ℓ_t] ≤ ln(1/w_μ) · H · N / q^H` (Theorem A). Countable class: `E[ℓ_t] → 0` (Theorem B), and by the
  note's Theorem 3 it is not summable in general.
- Stochastic class: I believe **yes** (`E[ℓ_t] → 0`), by the argument sketched in §4. SKETCH only.

## 1. Setting

As §0 of the note. Finite actions `A`, finite percepts `E`, reward `r : E → [0,1]`, discount `γ ∈ [0,1)`.
Values are normalised and geometrically discounted. I define them by value iteration, not as a supremum
over policies, because that is a structural recursion and needs no measure on infinite histories:

- `V^0_ν(h) = 0`, `V^{n+1}_ν(h) = max_a Σ_e ν(e|ha) [(1-γ) r(e) + γ V^n_ν(hae)]`;
- `V*_ν(h) = sup_n V^n_ν(h)` (increasing in `n`, bounded by 1);
- `Q*_ν(h,a) = Σ_e ν(e|ha) [(1-γ) r(e) + γ V*_ν(hae)]` (the note's definition of `Q*` from `V*`).

For environments that are measures this `V*` is the usual `sup_π V^π` (standard; not proved here, and
not needed: the theorems are about this `V*`).

- `a` is *optimal for ν at h* if `Q*_ν(h,b) ≤ Q*_ν(h,a)` for all `b`.
- Each class member `ν_i` has a deterministic designated policy `act_i : history → A` that is optimal for
  `ν_i` at **every** history. (So the note's degenerate class, one environment with two designated
  policies, is excluded whenever the optimal action is unique.)
- **Uniform gap `Δ > 0` for the truth `μ = ν_{i₀}`**: at every history `h` with `μ(h) > 0` and every
  `a ≠ act_{i₀}(h)`: `Q*_μ(h,a) + Δ ≤ Q*_μ(h, act_{i₀}(h))`. No gap is assumed for the other members.
- `π_T` is per-step Thompson sampling with the interventional posterior, as in `ThompsonLogLoss.lean`;
  `ℓ(h) = -ln π_T(act_{i₀}(h) | h)`; all expectations are under `P^{π_T}_μ`.

## 2. The deterministic case

*Deterministic* means every `ν_i(e|ha) ∈ {0,1}` (a member may be a semimeasure: it may "die"), and
`μ` gives probability 1 to exactly one percept `out(h,a)`. Then the posterior is the prior restricted
to the members not yet refuted, so a consistent member has posterior `≥ w_i`.

Fix `H` with `2γ^H < Δ`. For a deterministic policy `p` write `run_p^n(h)` for the history after
following `p` in `μ` for `n` steps from `h`, and `G_n(p,h) = Σ_{j<n} γ^j (1-γ) r_j` for the truncated
return along it.

**Lemma 1 (two values along a path).** Let `ν` be a deterministic semi-environment that gives
probability 1 to `μ`'s percept at each of the first `n` steps of `run_p(h)`. Then
(lower) `Q*_ν(h, p(h)) ≥ G_n(p,h)`; and (upper) if moreover `p` is optimal for `ν` at every history,
`Q*_ν(h, p(h)) ≤ G_n(p,h) + γ^n`.

*Proof.* Lower: `V^{n}_ν ≥` the `n`-step return of any fixed action sequence, by induction, and
`V* ≥ V^n`. Upper: `V*_ν(h') ≤ max_b Q*_ν(h',b) = Q*_ν(h',p(h'))`, since each `V^{n+1}_ν(h')` is a
maximum of quantities `≤ Q*_ν(h',b)`; unroll `n` times and bound the remainder by `V* ≤ 1`. ∎

**Lemma 2 (a disagreeing rival is refutable by play Thompson sampling actually tries).** Let `h` be a
`μ`-history and `act_i(h) ≠ act_{i₀}(h)`. Then `ν_i` gives probability 0 to `μ`'s percept at some
step `j < H` of `run_{act_i}(h)` or of `run_{act_{i₀}}(h)`.

*Proof.* Otherwise Lemma 1 applies to `ν_i` and to `μ` on both paths. With `a = act_i(h)`, `a* = act_{i₀}(h)`:
`Q*_{ν_i}(h,a) ≤ G_H(act_i,h) + γ^H ≤ Q*_μ(h,a) + γ^H ≤ Q*_μ(h,a*) - Δ + γ^H
 ≤ G_H(act_{i₀},h) + 2γ^H - Δ ≤ Q*_{ν_i}(h,a*) + 2γ^H - Δ < Q*_{ν_i}(h,a*)`,
contradicting the optimality of `a` for `ν_i`. (Steps: upper for `ν_i`; lower for `μ`; gap; upper for
`μ`; lower for `ν_i`.) ∎

This is where the gap is used, and why it must be uniform: `H` is fixed once.

**Theorem A (finite deterministic class: summable).** Let the prior be supported on a finite set `F`
of `N` members with `w_i ≥ q > 0` on `F`. Then for every `T`,
`Σ_{t<T} P(some unrefuted member disagrees with μ about the optimal action at h_t) ≤ H N / q^H`, and
`Σ_{t<T} E[ℓ_t] ≤ ln(1/w_μ) · H N / q^H`.

*Proof.* Let `N(h)` be the number of members of `F` not refuted by `h`; it never increases. At a
`μ`-history `h` where an unrefuted `i` disagrees, take the path and the *first* refuting step `j < H`
from Lemma 2. Until then the member whose policy defines the path (`i` or `i₀`) is unrefuted, so
Thompson sampling plays the path's next action with probability `≥ q` at each step, and follows the
path through step `j` with probability `≥ q^{j+1} ≥ q^H`; then `N` has dropped. So
`E[N(h_{t+H}) | h_t] ≤ N(h_t) - q^H · 1[bad(h_t)]`. Take expectations and telescope over `t` in
steps of `H`: `q^H Σ_{t<T} P(bad_t) ≤ Σ_{t<H} E N(h_t) ≤ H N`. Finally `ℓ_t = 0` when nobody
unrefuted disagrees, and `ℓ_t ≤ ln(1/w_μ)` always (the pointwise form of Theorem 5 for a
deterministic class). ∎

**Theorem B (countable deterministic class: in mean).** For any countable deterministic class,
`E[ℓ_t] → 0`.

*Proof.* Fix a finite `F ∋ i₀` and let `ε_F = Σ_{i∉F} w_i`. The proof of Theorem A bounds
`Σ_t P(bad^F_t)` (members of `F` only) by `H |F| / q_F^H`. At a `μ`-history where no unrefuted
member of `F` disagrees, the disagreeing posterior mass is at most `ε_F / ξ(h) ≤ ε_F / w_μ`, so
`ℓ(h) ≤ ln(1/w_μ) · 1[bad^F(h)] + ln(1/(1 - ε_F/w_μ))`. Hence `limsup_t E[ℓ_t] ≤ ln(1/(1-ε_F/w_μ))`,
which tends to 0 as `F` grows. ∎

**Not summable for countable classes.** The class of the note's Theorem 3 is deterministic and has a
uniform gap in `ν_0`; there every policy with `Σ_t P(mistake) < ∞` in `ν_0` fails in some `ν_n`. For
Thompson sampling in `ν_0` one can see directly that it explores at arbitrarily late times. So
Theorem B has no rate that depends only on `w_μ`, `Δ`, `γ`.

## 3. Vacuity checks

- The hypotheses are satisfiable with a strictly positive loss: two-armed bandit class, `ν_0` pays 1
  on arm 0 and `ν_1` on arm 1; `Q*(h, good) = 1`, `Q*(h, bad) = γ`, gap `1-γ`; `ℓ_1 = ln(1/w_μ) > 0`.
- Not a one-line corollary of Theorem 5 (which gives `E ℓ_t ≤ ln(1/w_μ)` only) nor of dominance
  `ξ ≥ w μ` (the same): the content is that every later disagreement is paid for by a refutation.
- Without the gap the proof fails at Lemma 2 only (`H` would have to depend on `h`).

## 4. The stochastic case — SKETCH, not formalised

Claim: for a countable class of measures (the truth `μ` with a uniform gap, designated policies
optimal and deterministic), `E[ℓ_t] → 0`.

1. *Tail.* `E_μ[Σ_{i∉F} w(i|h_t)] ≤ ε_F / w_μ`, because `E_μ[·] ≤ E_ξ[·]/w_μ` and the posterior mass of
   a set is a `ξ`-martingale. So it suffices to treat each fixed rival `ν`.
2. *Information budget.* Under the Bayes mixture the expected total information gain about the index
   is at most the prior entropy; block the time axis into `H`-step blocks and change measure to `μ`:
   `Σ_t E_μ[ w(ν|h_t) · TV_H(ν, μ | h_t)^2 ] < ∞`, where `TV_H` is the total variation between the
   `H`-step futures of `ν` and `μ` from `h_t` **under π_T** (Pinsker + chain rule). (For a countable
   class with infinite entropy, apply this to the class `F ∪ {rest lumped}`.)
3. *Disagreement forces on-policy divergence.* If `act_ν(h) ≠ act_μ(h)` then, by the stochastic
   version of Lemma 1 (simulation lemma) and the computation of Lemma 2, `ν` and `μ` differ by at
   least `(Δ - 2γ^H)/2` in total variation on the `H`-step future of one of the two policies
   `act_ν`, `act_μ`. Thompson sampling follows either with probability at least
   `(w(·|h) × path likelihood)^H`, so `TV_H(ν,μ|h) ≥ κ(w(ν|h), w(μ|h)) > 0`, with `κ` increasing
   in both weights (the low-likelihood paths are cut off at a threshold `η` and cost `|E|^H η`).
4. *Conclude.* From 2 and 3, `1[disagree] · w(ν|h_t)` → 0 in probability on `{w(μ|h_t) ≥ δ w_μ}`,
   whose complement has probability `≤ δ` (`posterior_uniform`). So the disagreeing mass → 0 in
   probability; `ℓ_t ≤ ln(1/w(μ|h_t))` is uniformly integrable (`1/w(μ|h_t)` is a supermartingale);
   so `E[ℓ_t] → 0`.

I have not checked step 3's constants or step 2 with semimeasures in the class. No summability is
expected here (stochastic bandits have logarithmic regret).

## 5. What I tried as counterexamples

- *μ's optimal action uninformative about the rival, the rival's action never played.* Fails: the
  rival's action is played with its posterior probability, which is bounded below while it survives
  (deterministic case) or is exactly the weight that multiplies the loss (stochastic case).
- *Rival and truth differ only far in the future.* The uniform gap caps how far: beyond `H` steps a
  difference is worth `< Δ/2`.
- *Infinitely many rivals, each refuted late (Theorem 3's class).* Kills summability, not the limit:
  the late rivals' total prior mass is a tail of a convergent sum.

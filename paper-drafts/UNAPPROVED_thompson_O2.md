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

## 4. The stochastic case — proof on paper (elementary; Lean status in RUN-REPORT.md)

**Theorem C.** Countable class of semi-environments `ν_i` (stochastic), prior `w`, deterministic
designated policies `act_i`, each optimal for its `ν_i` at every history; the truth `μ = ν_{i₀}` a
measure with `w_μ > 0` and a uniform gap `Δ > 0`. Then `E^{π_T}_μ[ℓ_t] → 0`.

Notation: `L_i(h)` is the likelihood of `h` under `ν_i`; `u_i(h) = w_i L_i(h)/ξ(h)` the posterior;
`v = u_{i₀}`. Fix `H ≥ 1` with `2γ^H < Δ`, `c = (Δ - 2γ^H)/2`, `d = c/|E|^H`.

**Step 1 (values along a policy).** For a deterministic policy `p` let `W^p_{ν,n}(h)` be the
`n`-step truncated return of `p` in `ν` from `h` (`W_0 = 0`, `W_{n+1}(h) = Σ_e ν(e|h,p(h))
[(1-γ)r(e) + γ W_n(h p(h) e)]`). Then `Q*_ν(h,p(h)) ≥ W^p_{ν,n}(h)`, and if `p` is optimal for `ν`
everywhere, `Q*_ν(h,p(h)) ≤ W^p_{ν,n}(h) + γ^n`. (Stochastic Lemma 1; same proof.)

**Step 2 (disagreement gives a path-level discrepancy).** At a `μ`-history `h` with
`act_i(h) ≠ act_μ(h)`, the chain of Lemma 2 gives
`[W^{act_i}_{ν_i,H} - W^{act_i}_{μ,H}](h) + [W^{act_μ}_{μ,H} - W^{act_μ}_{ν_i,H}](h) ≥ 2c`.
So one bracket is `≥ c`. Claim: if `α W^p_{ρ,n}(h) - β W^p_{σ,n}(h) ≥ c' > 0` then there is a
percept sequence `es` of length `≤ n` with `α ρ(es) - β σ(es) ≥ c'/|E|^n`, where `ρ(es)` is the
probability of `es` when `p` is followed from `h`. (Induction on `n`: some first percept `e`
carries `≥ c'/|E|` of the difference; it is a convex-type combination of `αρ(e) - βσ(e)` and of the
same expression one step later with `α' = αρ(e)`, `β' = βσ(e)`.) Hence there is a path `es`,
`|es| ≤ H`, along `p = act_k` for `k = i` or `k = i₀`, on which **the owner `k` of the policy
gives the path probability at least `d` more than the other one does**. Write `x, y` for the two
path probabilities; then `|√x - √y| ≥ d/2`.

**Step 3 (Thompson sampling follows that path).** `π_T(act_k(h')|h') ≥ u_k(h')`, and along the path
`u_k(h') ≥ u_k(h) · ν_k(prefix)` because `ξ` is non-increasing. So the action part of the path has
`π_T`-probability at least `(u_k(h) · ν_k(es))^{|es|} ≥ (u_k(h) d)^H`.

**Step 4 (the potential).** `Y_i(h) = √(L_i(h) L_μ(h))`. It is superharmonic for every action
(`Σ_e √(ν_i(e)μ(e)) ≤ 1`), so `A_t = Σ_{|h|=t} π_T-part(h) Y_i(h) = E_μ√(L_i/L_μ)(h_t)` is
non-increasing in `t`, and `≤ 1`. Over `n` steps from `h`,
`Y_i(h) - Σ_σ π-part(σ) Y_i(hσ) ≥ Y_i(h) Σ_σ π-part(σ) ½(√x_σ - √y_σ)²`
(equality for measures), and every term is `≥ 0`, so one path suffices:
`Y_i(h) - (S^H Y_i)(h) ≥ κ · Y_i(h) · min(u_i(h), v(h))^H` at every `h` where `i` disagrees, with
`κ = d^{H+2}/8`. Telescoping in steps of `H`:
`Σ_t Σ_{|h|=t} π-part(h) Y_i(h) min(u_i,v)^H 1[i disagrees at h] ≤ H/κ`.   (★)

**Step 5 (from (★) to the posterior mass of the disagreeing rival).** On `μ`-histories
`Y_i = L_μ √(w_μ u_i/(w_i v)) ≥ L_μ √(w_μ u_i / w_i)`. For thresholds `θ, δ > 0`:
`u_i 1[dis] ≤ θ + 1[v < δ] + 1[dis, u_i ≥ θ, v ≥ δ]`, the last indicator is at most
`Y_i min(u_i,v)^H 1[dis] / (L_μ √(w_μ θ/w_i) min(θ,δ)^H)`, and `P_μ(v(h_t) < δ) ≤ δ/w_μ` (Markov on
`ξ/L_μ`). So by (★) `limsup_t E_μ[u_i(h_t) 1[i disagrees at h_t]] ≤ θ + δ/w_μ` for all `θ, δ`: it is 0.

**Step 6 (the loss).** `π_T(a*|h) = 1 - q(h)` with `q` the posterior mass of the disagreeing
members, and `π_T(a*|h) ≥ v(h)`. For a finite `F`: `q ≤ Σ_{i∈F} u_i 1[dis_i] + Σ_{i∉F} u_i`, and
`E_μ Σ_{i∉F} u_i(h_t) ≤ ε_F/w_μ` (the partial mixture is superharmonic). On `{v ≥ δ}`:
`ℓ ≤ q · ln(1/δ)/(1-δ)`; on `{v < δ}`: `ℓ ≤ ln(1/v) ≤ 2√(1/v) ≤ 2√δ / v`, and
`E_μ[1/v] ≤ 1/w_μ`. So `limsup E[ℓ_t] ≤ (ln(1/δ)/(1-δ)) ε_F/w_μ + 2√δ/w_μ`; let `F ↑` then `δ ↓ 0`. ∎

No martingale convergence theorem and no merging-of-opinions theorem is used. No summability is
claimed (stochastic bandits have logarithmic regret), and (★) gives no rate for `E[ℓ_t]` because of
the thresholds.

## 5. What I tried as counterexamples

- *μ's optimal action uninformative about the rival, the rival's action never played.* Fails: the
  rival's action is played with its posterior probability, which is bounded below while it survives
  (deterministic case) or is exactly the weight that multiplies the loss (stochastic case).
- *Rival and truth differ only far in the future.* The uniform gap caps how far: beyond `H` steps a
  difference is worth `< Δ/2`.
- *Infinitely many rivals, each refuted late (Theorem 3's class).* Kills summability, not the limit:
  the late rivals' total prior mass is a tail of a convergent sum.

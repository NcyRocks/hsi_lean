-- ⚠️ UNAPPROVED: every statement in this file was drafted by Claude (Fable 5.2) on 2026-11-13 and has NOT been reviewed by Nathan.

# HSI out of distribution: what does training cost on a test item unlike the training data?

AI-derived (Claude Fable 5.2, 2026-11-13), unverified by Nathan. Every statement below is proven in
`HsiLean/HsiOOD.lean` (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only) unless
marked NOT FORMALISED. Source: `notes/queue/aram-hsi-optimality-2026-11-13.md`, §3.6 Proposition E
and §6 candidates 1–2. Sections 4 and the "attained" part of 2 are new in this run.

## 1. Setting

As in `Rate.lean`. Items are elements of any type. Item models $P_j$, $j\in\mathbb N$, with
$P_j(a)\le 1$; hyperprior weights $w_j\ge 0$, $\sum_j w_j\le 1$. For a dataset $X=(x_1,\dots,x_n)$:

- $P_j(X)=\prod_k P_j(x_k)$ (`lik`), $P_{\mathcal H}(X)=\sum_j w_j P_j(X)$ (`mixL`),
- trained HSI: $P_{\mathcal H}(y\mid X)=P_{\mathcal H}(X,y)/P_{\mathcal H}(X)$ (`pred`).

Fix a comparison member $j$ with $w_j>0$ ("fresh SolInd"). Logs are base 2.

- $\mathrm{excess}_j(X,y) := -\log P_{\mathcal H}(y\mid X) + \log P_j(y)$: trained HSI's log loss on
  the test item minus $j$'s (`excess`).
- $\mathrm{gain}_j(X) := -\log P_j(X) + \log P_{\mathcal H}(X)$: $j$'s log loss on the training data,
  item by item, minus HSI's (`trainGain`). Always $\ge \log w_j$ (`logb_le_trainGain`).

**Why a named member and not the untrained mixture.** In the abstract setting the untrained
mixture $\xi(y)=\sum_j w_jP_j(y)$ cannot serve as the comparison: the argument needs
$P_{\mathcal H}(X,y)\ge c\cdot\prod_k\xi(x_k)\cdot\xi(y)$, and a mixture of products does not
dominate a product of mixtures. For machines the two coincide (§5).

## 2. The upper bound (Proposition E) and when it is attained

**Theorem 1 (`ood_upper`).** For every dataset $X$ and test item $y$ with $P_j(X)P_j(y)>0$:
$$\mathrm{excess}_j(X,y)\ \le\ -\log w_j+\mathrm{gain}_j(X).$$
No assumption on where $X$ or $y$ come from.

*Proof.* $P_{\mathcal H}(X,y)\ge w_jP_j(X)P_j(y)$; divide by $P_{\mathcal H}(X)$, take $-\log$. ∎
(This is the pointwise bound `totalExcess_le` for the dataset $(X,y)$, rearranged by the chain rule.)

**Theorem 2 (`ood_upper_attained`).** If $j$ is the only member of positive weight with
$P(y)>0$, Theorem 1 holds with equality.

*Proof.* Then $P_{\mathcal H}(X,y)=w_jP_j(X)P_j(y)$ exactly. ∎

## 3. The lower bound: the penalty can be large

Train on $n$ copies of $a$, test on $b$. Assume no model gives $a$ and $b$ together more than
probability one (automatic if $a\ne b$ and $\sum_aP_j(a)\le1$), and a member $j_0$ with $w_{j_0}>0$
has $P_{j_0}(a)=1$.

**Theorem 3 (`pred_offDistribution_le`, `ood_lower`).**
$P_{\mathcal H}(b\mid a^n)\le \dfrac1{(n+1)\,w_{j_0}}$, and if $P_j(a),P_j(b)>0$:
$$\mathrm{excess}_j(a^n,b)\ \ge\ \log(n+1)-\big(-\log w_{j_0}-\log P_j(b)\big).$$

*Proof.* Numerator: $\sum_jw_jP_j(a)^nP_j(b)\le\sum_jw_j\max_{t+s\le1}t^ns\le\frac1{n+1}$, where
$(n+1)t^ns\le(1+t+\dots+t^n)s\le 1-t^{n+1}\le 1$ (done without subtraction in Lean: `geom_aux`).
Denominator: $P_{\mathcal H}(a^n)\ge w_{j_0}$. ∎

**Theorem 4 (`ood_linear`, `example_ood_linear`).** If moreover $j$ is the only member of positive
weight with $P(b)>0$, then $\mathrm{excess}_j(a^n,b)\ge n\cdot(-\log P_j(a))+\log w_{j_0}$: LINEAR in
$n$. Concretely, for the class {point mass on `true`, fair coin} with weights ½, ½:
$\mathrm{excess}\ge n-1$ bits.

## 4. A logarithmic upper bound when the class can hedge (new)

**Theorem 5 (`ood_upper_hedged`).** Let a member $i$ with $w_i>0$ satisfy $P_i\ge c\,P_k$ and
$P_i\ge d\,P_j$ pointwise, $0<c,d<\infty$. For $X$ with $P_k(X)>0$ and $y$ with $P_j(y)>0$:
$$\mathrm{excess}_j(X,y)\le-\log w_i+|X|\cdot(-\log c)-\log d+\mathrm{gain}_k(X).$$

**Corollary 6 (`ood_upper_hedged_log`).** With $c=\frac n{n+1}$, $d=\frac1{n+1}$, $n=|X|\ge1$:
$$\mathrm{excess}_j(X,y)\le\log(n+1)+\tfrac1{\ln2}-\log w_i+\mathrm{gain}_k(X).$$

*Proof.* Theorem 1's argument with $w_iP_i(X,y)\ge w_i\,c^nP_k(X)\,d\,P_j(y)$; and
$n\log\frac{n+1}n\le\frac1{\ln 2}$. ∎

**Corollary 7 (`ood_offDistribution_upper`).** In the setting of Theorem 3, if a member $i$ hedges
between $j_0$ and $j$ at rate $\frac1{n+1}$: $\mathrm{excess}_j(a^n,b)\le\log(n+1)+\frac1{\ln2}-\log w_i$.

**Reading.** $\mathrm{gain}_k(X)$ is how much HSI beat the single model $k$ on the training data.
So: *if one model explains the training data about as well as HSI does, a surprising test item
costs about $\log(n+1)$ bits plus the price of naming the hedge.* The class of all l.s.c.
semimeasures is closed under such mixtures, so a hedge always exists there; with a universal
hyperprior its price $-\log w_{i}$ should be about $K(k)+K(j)+K(n)$ — NOT FORMALISED (the library
has no $K$).

## 5. Headline and the machine level

**`hsi_ood`** collects Theorems 1, 2, 3 and Corollary 7 in one statement.

**`hsi_ood_machines`.** Let $V$ be an effective enumeration of monotone machines containing every
UTM, and $w$ l.s.c. positive weights with $\sum w\le1$. Then there are a UTM $U$ and an index $k$
with $V_k=U$ such that the untrained HSI prior $\sum_{k'}w_{k'}\lambda_{V_{k'}}$ equals $\lambda_U$
off $\epsilon$, and for every dataset $X$ of strings and test string $y$ (items read as
content-given-length) with $\lambda_U(X)\lambda_U(y)>0$:
$$-\log P_{\mathcal H}(y\mid X)+\log\lambda_U(y)\ \le\ -\log w_k+\mathrm{gain}_k(X).$$
Here "fresh SolInd" is literally the same prior, used without training.

## 6. Exchangeability (the note's §6 candidate 2)

- **`mixL_perm`, `pred_perm`.** $P_{\mathcal H}(X)$ and $P_{\mathcal H}(\cdot\mid X)$ do not depend
  on the order of $X$.
- **`card_mul_mixL_le_one`.** If $\sum_aP_j(a)\le1$ for all $j$: for any finite family $S$ of
  $n$-element sets of items, $\sum_{s\in S}n!\,P_{\mathcal H}(s)\le1$.
- **`exists_mixL_perm_le`.** Hence some $s\in S$ has $P_{\mathcal H}(\text{any ordering of }s)\le
  \frac1{n!\,|S|}$, whereas a predictor that knows the order rule can give one ordering of each set
  probability $\frac1{|S|}$: a gap of $\log n!$ bits.

*Proof of the counting bound.* For one model $f=P_j$: each $n$-set $s$ has $n!$ orderings, each an
injective tuple with product $\prod_{a\in s}f(a)$; different (set, ordering) pairs give different
tuples; and $\sum_{v\in\alpha^n}\prod_if(v_i)=(\sum_af(a))^n\le1$. ∎

## 7. What this says about the note

- No step of the note's proofs of Proposition E failed.
- The note's phrase "bounded by exactly what HSI gained in training" is correct as an upper bound,
  but its example does not show that the bound is tight: there the bound is linear in $n$ while
  the example gives $\log(n+1)-C$. The bound is attained (Theorem 2, Theorem 4) only in classes
  that cannot hedge; in classes that can, the penalty in the example is $\log(n+1)$ up to the
  price of the hedge (Theorem 3 + Corollary 7).
- "Training + test together lose at most $-\log w_j$ to $j$" is `totalExcess_le` at $(X,y)$; not
  restated.

## 8. Not done

- The note's Theorem B.3 in full (the chain $X_a=(a,a+1,\dots)$ and the machine $T_L$): only its
  counting core is formalised.
- The note's §6 candidate 3 (countable i.i.d. mixtures lose to Laplace; Theorem C).
- Any statement involving $K$ or a universal hyperprior.

# Atlas — Delegated-MSM IPA with a Preprocessed Generator Map

*Transparent prime-order dlog polynomial commitment, polylog proof, polylog verifier. Named for the giant precomputed map (the Kedlaya–Umans table) the verifier consults. See `2-genesis.md` for the successor that removes the table — and its galactic constants — entirely.*

**Abstract.** We specify a polynomial commitment scheme over an ordinary prime-order group in which both the proof size and the *online* verifier are $\mathrm{polylog}(n)$, using **no pairing, no unknown-order group, and no recursion**. The scheme is the Bulletproofs/IPA opening protocol, augmented by two ingredients: (1) the verifier's single linear-cost step — the folded-generator MSM $G_0 = \langle \mathbf{s}, \mathbf{G} \rangle$ — is a deterministic computation on public inputs, so it is *delegated* to the prover via a Fiat–Shamir'd sumcheck/GKR interactive proof with unconditional (information-theoretic) soundness; (2) the delegation bottoms out in one evaluation of the multilinear extension of the *fixed public* generator coordinates, which a one-time transparent Kedlaya–Umans preprocessing (size $n^{1+\varepsilon}$) answers in $\mathrm{polylog}$ online time. Only the discrete-log relation assumption is used, and only for Pedersen binding. The result is asymptotic, not a deployable system.

## Notation & setting

- $\mathbb{G}$: a group of prime order $q$ (e.g. an ordinary elliptic curve), written additively; scalar field $\mathbb{F} = \mathbb{F}_q$.
- $n = 2^k$; the committed vector is $\mathbf{a} \in \mathbb{F}^n$ (coefficients or evaluations of a polynomial).
- SRS: $\mathbf{G} = (G_1, \dots, G_n) \in \mathbb{G}^n$ and $U \in \mathbb{G}$, sampled transparently by hash-to-curve, $G_i = H(i)$.
- Commitment: Pedersen, $C = \langle \mathbf{a}, \mathbf{G} \rangle = \sum_i a_i G_i$ (one group element).
- Opening claim: $\hat{a}(z) = v$ where $\hat{a}$ is the polynomial/MLE determined by $\mathbf{a}$, i.e. $\langle \mathbf{a}, (z^i)_i \rangle = v$.
- Round challenges of the IPA: $x_1, \dots, x_k \in \mathbb{F}^\times$.

## The bottleneck

After the $k = \log_2 n$ folding rounds of Bulletproofs/IPA, the verifier's final check is

$$P_0 \stackrel{?}{=} a \cdot G_0 + (a \cdot b_0) \cdot U,$$

where $a \in \mathbb{F}$ is the fully-folded scalar and $\mathbf{s}$ is the **challenge tensor**

$$s_i = \prod_{j=1}^{k} x_j^{\pm 1} \qquad (\text{sign determined by bit } j \text{ of } i), \qquad \mathbf{s} = \bigotimes_{j=1}^{k} (x_j^{-1},\, x_j).$$

The two folded quantities behave very differently:

- $`b_0 = \langle \mathbf{s}, (z^i)_i \rangle`$ — **already succinct**: $\mathbf{s}$ is the coefficient vector of $`g(X) = \prod_{j=1}^{k} \big(x_j^{-1} + x_j X^{2^{j-1}}\big)`$, so

  $$b_0 = g(z) = \prod_{j=1}^{k} \big(x_j^{-1} + x_j z^{2^{j-1}}\big)$$

  costs $O(\log n)$ despite $\mathbf{s}$ having $n$ entries (Lean: `bSuccinct_eq_bLinear`).
- $G_0 = \langle \mathbf{s}, \mathbf{G} \rangle$ — an $n$-term MSM over the SRS. **This is the sole $\Theta(n)$ step** of the verifier; everything else is $O(\log n)$.

Crucially, $G_0$ involves no witness: $\mathbf{s}$ is derived from public (Fiat–Shamir) challenges and $\mathbf{G}$ is the fixed public SRS. Computing $G_0$ is *delegation of a public deterministic computation*, not an argument about hidden data.

## Protocol

### Setup (one-time, transparent, $n^{1+\varepsilon}$)

1. $\mathbf{G} \leftarrow (H(1), \dots, H(n))$, $U \leftarrow H(0)$ by hash-to-curve (public, deterministic).
2. Fix the uniform, $\log$-depth **MSM circuit** $\mathcal{C}$: on input $(x_1,\dots,x_k; \mathbf{G})$ it expands the tensor $\mathbf{s}$ internally and computes $\langle \mathbf{s}, \mathbf{G} \rangle$ as a binary addition tree of depth $\log n$ over double-and-add gates (arithmetized over the base field of $\mathbb{G}$).
3. Run **Kedlaya–Umans preprocessing** (KU'08 / BGKM'22: multivariate polynomial evaluation with preprocessing) on the MLE $\widetilde{G}$ of the coordinates of $\mathbf{G}$ — a *fixed public* polynomial. Output a data structure $D_{\mathbf{G}}$ of size $n^{1+\varepsilon}$, built in $n^{1+\varepsilon}$ time, that evaluates $\widetilde{G}$ at **any** point in $\mathrm{polylog}(n) \cdot \mathrm{polylog}(q)$.

All of setup is public and deterministic: anyone can recompute and check it; no trapdoor exists.

### Commit

$$\mathsf{Commit}(\mathbf{a}) = C = \langle \mathbf{a}, \mathbf{G} \rangle \in \mathbb{G}.$$

### Open (prover) — claim $\hat{a}(z) = v$

1. **BP transcript.** Run the standard $k$-round IPA folding, producing $L_j, R_j \in \mathbb{G}$ per round ($2\log n$ group elements) and the final scalar $a$. Challenges $x_j$ by Fiat–Shamir.
2. **Delegation certificate.** Let $Q$ be the claimed value of $G_0 = \langle \mathbf{s}, \mathbf{G} \rangle$. Produce a Fiat–Shamir'd **GKR/sumcheck certificate** that $\mathcal{C}(x_1,\dots,x_k;\mathbf{G}) = Q$. Sumcheck climbs the addition tree layer by layer; each round exploits the halving identity

   $$\sum_{p \,\in\, \{0,1\}\times\kappa} f(p) \;=\; \sum_{b \in \kappa} f(\mathsf{true}, b) \;+\; \sum_{b \in \kappa} f(\mathsf{false}, b)$$

   (field level `sum_split`; group level `msm_split`): the prover sends a low-degree univariate $p_r(X)$ restricting the current sum to its top variable, the verifier checks $p_r(0) + p_r(1) = \mathrm{claim}$ and issues a fresh challenge. Prover cost: linear field operations over the circuit — **no commitments, no FFTs, no verifier-in-circuit**.

Total proof: $O(\log n)$ group elements + $\mathrm{polylog}(n)$ field elements.

**Why nothing circular remains.** Every earlier attempt to shrink the MSM relocated the $\Theta(n)$ work (to a random point, to another commitment, to a pairing). Here the delegated claim, after $\mathrm{polylog}$ rounds, reduces to *one* evaluation of the MLE of the circuit input at a random point. The input is only:

1. the $k = \log n$ round challenges — tiny; the tensor expansion of $\mathbf{s}$ happens *inside* the circuit, while the verifier's own side needs only the proven product identity for $b_0$ above ($O(\log n)$);
2. the coordinates of $\mathbf{G}$ — a **fixed public polynomial**, answered by the preprocessed data structure $D_{\mathbf{G}}$ in $\mathrm{polylog}$.

The divide-and-conquer bottoms out in a *data structure*, not another proof — this is what replaces recursion.

### Verify (all costs online)

| # | Check | Cost |
|---|-------|------|
| 1 | Recompute FS challenges $x_1,\dots,x_k$ from the transcript | $O(\log n)$ hashes |
| 2 | $b_0 = \prod_{j=1}^{k}\big(x_j^{-1} + x_j z^{2^{j-1}}\big)$ | $O(\log n)$ field ops |
| 3 | Fold $P_0 = C' + \sum_j (x_j^2 L_j + x_j^{-2} R_j)$ | $O(\log n)$ group ops |
| 4 | Sumcheck rounds of the GKR certificate: per round check $p(0) + p(1) = \mathrm{claim}$, sample $r$, set new claim $\leftarrow p(r)$ (`sumcheck_round_complete`) | $O(1)$ per round, $\mathrm{polylog}$ total |
| 5 | Final delegated claim = one evaluation of the input MLE: (a) challenge side — the $k$ challenges are known, and the wiring reduces to the proven tensor identity of step 2; (b) generator side — query $D_{\mathbf{G}}$ for $\widetilde{G}$ at the random point | $O(\log n)$ + one KU query, $\mathrm{polylog}$ |
| 6 | Final IPA check $P_0 = a \cdot Q + (a \cdot b_0) \cdot U$ with $Q$ certified by 4–5 | $O(1)$ group ops |

**Total online verifier: $\mathrm{polylog}(n)$.**

## Security sketch

**Completeness.** BP completeness is standard. The honest round polynomial satisfies $p(0) + p(1) = \mathrm{claim}$ exactly (`sumcheck_round_complete`, from `sum_split`/`msm_split`), and the KU structure is deterministic, so the honest final claim always matches.

**Soundness.** Three independent pieces, only the first cryptographic:

1. *BP extraction* — knowledge soundness of the IPA under the **discrete-log relation assumption**; Pedersen binding *is* exactly this assumption (Lean: `pedersen_binding`, `schnorr_extract`).
2. *Delegation* — **unconditional**. A cheating round polynomial $p \neq p^{\mathrm{honest}}$ agrees with the honest one only at roots of $p - p^{\mathrm{honest}}$ (`disagreement_is_root`), of which there are at most $d = \max(\deg p, \deg p^{\mathrm{honest}})$ (`cheating_caught`), so a uniform challenge catches the lie except with probability

   $$\Pr[\text{round lie survives}] \;\le\; \frac{d}{|\mathbb{F}|},$$

   and a union bound over all $\mathrm{polylog}$ rounds gives total delegation soundness error $O(d \log n / |\mathbb{F}|)$ — negligible for cryptographic $q \approx 2^{256}$. This is an interactive proof, not an argument: **no new assumption enters** (Fiat–Shamir applied in the ROM, as already required for BP).
3. *KU data structure* — deterministic and publicly recomputable; its correctness is an algorithmic fact, not a security assumption.

**Machine-checked in Lean** (`lake build` green, no `sorry`, axioms only `propext`/`Classical.choice`/`Quot.sound`):

| Lemma | File | Role |
|---|---|---|
| `bSuccinct_eq_bLinear` | `SVector.lean` | $b_0$ product identity is $O(\log n)$ |
| `sum_split`, `msm_split` | `Delegation.lean` | the D&C halving step (field and group level) |
| `sumcheck_round_complete` | `Delegation.lean` | round-check completeness |
| `disagreement_is_root`, `cheating_caught` | `Delegation.lean` | round soundness (one-variable Schwartz–Zippel) |

Not formalized: the full GKR wiring layer and the end-to-end composition (see caveats).

## Costs

| Item | Cost |
|------|------|
| Setup | $n^{1+\varepsilon}$ time/space, one-time, public, deterministic (transparent) |
| Commitment | $1$ group element |
| Proof | $O(\log n)$ group elements $+$ $\mathrm{polylog}(n)$ field elements |
| Verifier (online) | $\mathrm{polylog}(n) \cdot \mathrm{polylog}(q)$ |
| Prover | $O(n \lambda)$ native field/group ops; no FFTs, no commitments beyond the Pedersen ones, no verifier-in-circuit |

## Honest caveats

- **Galactic constants.** KU-style preprocessing evaluation (Kedlaya–Umans 2008; Bhargava–Ghosh–Kumar–Mohapatra 2022) is an asymptotic result; the constants and the $n^{1+\varepsilon}$ table are impractical today. This spec is an **asymptotic answer** to the feasibility question, not an implementable system.
- **Composition is paper-grade work.** The end-to-end security proof (BP extraction $\circ$ Fiat–Shamir'd GKR $\circ$ KU input oracle) is not written out. The circuit-level details — double-and-add bit decomposition of the scalars, arithmetization of the curve group law, and $\mathrm{polylog}$-evaluability of the wiring MLEs of the uniform circuit — are standard GKR engineering, but standard-and-unformalized is not the same as proven.
- **Setup grows.** Transparent setup was $\Theta(n)$ (hashing out the SRS); preprocessing raises it to $n^{1+\varepsilon}$. It remains one-time, public, and deterministic, so transparency is preserved.
- **Model.** Non-interactivity of the delegation relies on Fiat–Shamir in the random-oracle model — the same heuristic Bulletproofs already needs, so no *additional* model assumption, but worth stating.

## Comparison

| Scheme | Proof size | Verifier (online) | Transparent | Assumptions | Recursion |
|---|---|---|---|---|---|
| Bulletproofs | $O(\log n)$ | $\Theta(n)$ | yes | dlog | no |
| Hyrax | $O(\sqrt{n})$ | $O(\sqrt{n})$ | yes | dlog | no |
| Dory | $O(\log n)$ | $O(\log n)$ | yes | SXDH (pairing) | no |
| DARK | $O(\log n)$ | $\mathrm{polylog}$ | yes | unknown-order group | no |
| Halo / Nova | $O(\log n)$ amortized | $O(\log n)$ per step $+$ one $\Theta(n)$ decider | yes | dlog | **yes** |
| **This work** | $O(\log n)$ grp $+$ polylog fld | $\mathrm{polylog}$ | yes | dlog only | no |

The previously "empty cell" — transparent, prime-order dlog, polylog proof, polylog verifier, non-recursive — is filled by moving outside the commitment-scheme toolbox: the verifier's one linear step is a public computation, delegated information-theoretically, and the divide-and-conquer bottoms out in a preprocessing data structure rather than another proof.

# Genesis — Delegated-MSM IPA with In-Circuit SRS Derivation

*Successor to Atlas (`1-atlas.md`). Named for how it works: the generators are grown from a seed inside the delegated circuit — the SRS is a program, not a table. This removes Atlas's Kedlaya–Umans preprocessing, and with it the galactic constants. See `3-prism.md` for the successor that drops the in-circuit curve arithmetic entirely — trading zero-preprocessing for a near-linear transparent RS encoding, and the $10^2$–$10^3\times$ prover for an $O(n)$-smul one.*

**Abstract.** Same target as Atlas: a polynomial commitment over an ordinary prime-order group with $\mathrm{polylog}(n)$ proof and *online* verifier — **no pairing, no unknown-order group, no recursion**. The single change: instead of feeding the delegated MSM circuit the $n$-sized generator table (whose input-MLE evaluation forced Atlas's $n^{1+\varepsilon}$ preprocessing), the circuit takes only the **seed** and derives the generators internally by hash-to-curve. The circuit input shrinks to $O(\log n)$ field elements, the final input-MLE check becomes trivial, and every component has implemented-system (GKR/Libra-grade) constants. Setup is: publish a seed.

## The one idea

Atlas's bottleneck was the delegation's terminal check: one evaluation of the MLE of the circuit *input*, which contained the coordinates of $\mathbf{G}$ — an $n$-sized table, incompressible if the generators were truly random. But binding never needed true randomness, only *pseudorandomness*: $G_i = \mathsf{HashToCurve}(\mathsf{seed}, i)$, the standard transparent Bulletproofs setup. The table has an $O(1)$-size description. So:

> **Feed the circuit the seed, not the generators.** Delegate the composed computation
> $$\mathcal{C}(\mathsf{seed}, x_1, \dots, x_k) : \quad \mathsf{seed} \xrightarrow{\ \mathsf{H2C}\ } G_1,\dots,G_n \xrightarrow{\ \otimes_j (x_j^{-1}, x_j)\ } \langle \mathbf{s}, \mathbf{G} \rangle = G_0 .$$

The input is now $\mathsf{seed} \| x_1 \dots x_k$ — $O(\log n)$ field elements — so the verifier evaluates the input MLE directly in $O(\log n)$. Nothing is preprocessed; nothing is galactic.

This does not contradict the digest lower bound (`no_lossy_digest_verifier`): that bound bites verifiers that *view* $\mathbf{G}$ through sublinear information, and truly random generators are incompressible. Here the verifier never views $\mathbf{G}$ at all — it verifies the *program that computes* $\mathbf{G}$, and pseudorandom generators have a constant-size program.

## What runs inside the circuit (all deterministic, uniform, shallow)

| Stage | Realization | Depth | Gate-level correctness (Lean) |
|---|---|---|---|
| Hash | algebraic hash (Poseidon over $\mathbb{F}_p$) | $O(\mathrm{polylog})$ | standard, low-degree gates |
| Point decompression | $\sqrt{a} = a^{(p+1)/4}$ for $p \equiv 3 \bmod 4$, by square-and-multiply — **no nondeterministic advice** (advice would be an $n$-sized input and reintroduce the circularity) | $O(\lambda)$ | `square_and_multiply_step`, `sqrt_exp_correct` |
| Tensor expansion $x \to \mathbf{s}$ | uniform product tree | $O(\log n)$ | tensor identity `bSuccinct_eq_bLinear`, `sCoeff_factors` |
| Scalar mults | double-and-add | $O(\lambda)$ | `double_and_add_step` |
| MSM | binary addition tree | $O(\log n)$ | `msm_split` |
| Delegation itself | sumcheck rounds over the tree | — | `sum_split`, `sumcheck_round_complete`, `disagreement_is_root`, `cheating_caught` |
| Seed-derivation reduction | certifying the composed circuit certifies the SRS claim | — | `genesis_reduction` |

## Protocol

**Setup (transparent):** publish $\mathsf{seed}$. That's all. ($\mathbf{G} = (\mathsf{H2C}(\mathsf{seed},i))_i$ and $U = \mathsf{H2C}(\mathsf{seed},0)$ are defined, not stored; anyone may materialize them.)

**Commit:** $C = \langle \mathbf{a}, \mathbf{G} \rangle$ — one group element. (The *prover* materializes $\mathbf{G}$ once, $O(n)$, as in any Bulletproofs implementation.)

**Open** (claim $\hat a(z) = v$):
1. Standard $k$-round IPA folding → $L_j, R_j$ ($2\log n$ group elements), final scalar $a$; challenges by Fiat–Shamir.
2. Claimed $Q$ for $G_0$, plus a Fiat–Shamir'd GKR/sumcheck certificate that $\mathcal{C}(\mathsf{seed}, x_1..x_k) = Q$ — $\mathrm{polylog}$ field elements.

**Verify** (all online):

| # | Check | Cost |
|---|---|---|
| 1 | FS challenges | $O(\log n)$ hashes |
| 2 | $b_0 = \prod_j (x_j^{-1} + x_j z^{2^{j-1}})$ | $O(\log n)$ field ops |
| 3 | Fold $P_0 = C' + \sum_j (x_j^2 L_j + x_j^{-2} R_j)$ | $O(\log n)$ group ops |
| 4 | Sumcheck rounds: $p_r(0)+p_r(1) = \mathrm{claim}$, new claim $\leftarrow p_r(r)$ | $O(1)$/round, $\mathrm{polylog}$ total |
| 5 | Final input-MLE evaluation at the random point — input is $\mathsf{seed}\|x_1..x_k$, i.e. $O(\log n)$ values | $O(\log n)$ **(this line replaced Atlas's KU query)** |
| 6 | $P_0 = a \cdot Q + (a b_0) \cdot U$ | $O(1)$ group ops |

## Security sketch

- **Completeness:** determinism of the derivation — the in-circuit $\mathbf{G}$ *is* the published SRS (`genesis_reduction`); honest round polynomials pass (`sumcheck_round_complete`); the sqrt chain outputs a correct root on quadratic residues (`sqrt_exp_correct` with $t = (p+1)/4$, $m = (p-1)/2$, where $a^m = 1$ is Euler's criterion).
- **Soundness:** (i) IPA extraction under the dlog-relation assumption for hash-derived generators — the same assumption Bulletproofs already makes (`pedersen_binding`); (ii) the certificate is an interactive *proof*: a lying round polynomial survives a random challenge w.p. $\le d/|\mathbb{F}|$ (`disagreement_is_root`, `cheating_caught`), union-bounded over $\mathrm{polylog}$ rounds — **unconditional**; (iii) Fiat–Shamir in the ROM (already required for BP).

## Costs

| Item | Atlas | **Genesis** |
|---|---|---|
| Setup | $n^{1+\varepsilon}$ table, galactic constants | **publish a seed** |
| Commitment | 1 group element | 1 group element |
| Proof | $O(\log n)$ grp + polylog fld | $O(\log n)$ grp + polylog fld |
| Verifier online | polylog + 1 KU query | **polylog, small constants** (sumcheck rounds + $O(\log n)$ hashes) |
| Prover | linear | linear: $\sim n \cdot O(\lambda)$ GKR gates at a few field ops each, no commitments/FFTs — est. $10^2$–$10^3 \times$ the raw MSM; zk-prover-grade, not galactic |

## Honest caveats

- **The two-field problem** (the main open engineering): curve arithmetic is over $\mathbb{F}_p$, scalars/tensor over $\mathbb{F}_q$. Either (a) non-native $\mathbb{F}_q$ arithmetic emulated inside the $\mathbb{F}_p$ GKR — tens-of-$\times$ constant blowup, deterministic, simplest; or (b) a linked $\mathbb{F}_q$-sumcheck + $\mathbb{F}_p$-GKR pair joined by bit-decomposition claims — leaner but with a fiddlier soundness argument. Engineering, not a conceptual barrier; where a paper-grade version spends its pages.
- **Composition proof:** end-to-end (BP extraction $\circ$ FS'd GKR) is not written out; wiring-MLE evaluability of the uniform circuit is standard GKR engineering, unformalized.
- **Prover overhead** is real ($10^2$–$10^3\times$ the raw MSM) even if no longer galactic; the certificate is per-opening.


## Implementation status (updated)

The scheme is **implemented end-to-end and benchmarked**; the spec above is realized by:

| artifact | contents |
|---|---|
| `../sage/3-genesis-e2e.sage` | full pipeline on Pallas (toy-hash derivation): layered-sumcheck GKR engine, in-circuit derivation + CT Tonelli–Shanks + RCB fold; verifier never touches the $n$ generators |
| `../sage/4-genesis-prod.sage` | **production derivation**: Poseidon (t=3, $\alpha$=5, 8 full + 56 partial rounds) and RFC-9380-style iso-SWU hash-to-curve (3-isogeny + constants computed by Sage at load, projective dual isogeny, no retries) |
| `../clean-circuits/Genesis.lean` | formally verified circuit gadgets ([clean](https://github.com/Verified-zkEVM/clean)): Poseidon rounds, exponent-chain steps, TS conditional step, QR bit, curve evaluation, complete RCB point addition — soundness **and** completeness proven; 8 `#eval` vectors pin Lean $\leftrightarrow$ Sage |

**Measured** (Pallas, single-thread Sage, same machine, both verifiers in Sage): the Genesis
verifier crosses the naive linear verifier at $n \approx 256$ and wins $2.2\times$ at
$n = 512$ (production pipeline) and $5.5\times$ at $n = 2048$ (toy pipeline, where it also
beats a pure-python-int MSM baseline $1.4\times$). Verify time grows $\sim \log n$
($\lambda$-dominated); prover $\approx 0.2$ s/lane.

**What remains unverified** (honest inventory): the Sage GKR engine (claim bookkeeping,
kernels, folding — where the one real bug of the build lived), the composed multi-round GKR
soundness (single-round Schwartz–Zippel is proven), Fiat–Shamir, the RCB-formulas ↔ group-law
link (tested on 120 cases incl. identity/doubling; formal proof needs Mathlib
`WeierstrassCurve`), the CT-TS loop invariant (endpoint identity proven), and Poseidon's
cryptographic properties (constants are SHA-derived + Cauchy MDS rather than Grain-generated
with subspace checks — swapping in official pasta parameters is mechanical).

## Comparison

| Scheme | Proof | Verifier | Transparent | Assumptions | Recursion | Practical constants |
|---|---|---|---|---|---|---|
| Bulletproofs | $O(\log n)$ | $\Theta(n)$ | yes | dlog | no | yes |
| Hyrax | $O(\sqrt n)$ | $O(\sqrt n)$ | yes | dlog | no | yes |
| Dory | $O(\log n)$ | $O(\log n)$ | yes | SXDH | no | yes |
| DARK | $O(\log n)$ | polylog | yes | unknown order | no | slow ops |
| Halo / Nova | $O(\log n)$ am. | per-step $O(\log n)$ + one decider | yes | dlog | **yes** | yes |
| Atlas | $O(\log n)$+polylog | polylog | yes | dlog | no | **galactic** |
| **Genesis** | $O(\log n)$+polylog | polylog | yes | dlog | no | **implementable** |

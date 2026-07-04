# Lens — the IPA fold *is* an FRI fold: one transcript certifies both

*Sits between Genesis (`2-genesis.md`) and Prism (`3-prism.md`) — the "solution 2½" answering: small proof **and** small verifier. Named for how it works: Prism refracts the generators into their Reed–Solomon spectrum; Lens **focuses that spectrum to a point using the IPA's own folding rounds** — no circuit (Genesis), no separate reduce/decide phases with fresh challenges (Prism). The certificate rides the IPA transcript.*

**Abstract.** Transparent, prime-order, no pairing, no unknown-order group, no recursion. The verifier's one linear step — the folded-generator MSM $G_0 = \langle \mathbf{s}, \mathbf{G}\rangle$ — is certified by FRI-folding a Merkle-committed Reed–Solomon encoding of $\mathbf{G}$ **with the IPA's own round challenges**. Two already-proven facts make this a merger rather than a bolt-on: $G_0 = (\prod_j x_j^{-1})\cdot \mathsf{MLE}_{\mathbf G}(x_1^2,\dots,x_k^2)$ (`genFinal_eq_mle`), and the per-round identity

$$x^{-1} G_{lo} + x\, G_{hi} \;=\; x^{-1}\big( G_{lo} + x^2\, G_{hi} \big)$$

— **the IPA generator fold is an FRI fold by challenge $x^2$, times a public scalar** (`lens_fold_factor`, proven). Since Fiat–Shamir draws $x_j$ *after* the round-$j$ codeword root is committed, the fold challenge is fresh randomness exactly as FRI soundness requires, even though it doubles as the IPA challenge.

## Protocol

**Setup (transparent, one-time).** $\mathbf{G} = \mathsf{H2C}(\mathsf{seed}, \cdot)$ as in Genesis. RS-encode the group-valued generator polynomial on a 2-adic domain of size $n/\rho$ in the scalar field (both Pasta fields have 2-adicity 32) — a group-valued FFT, $O(n\log n)$ scalar mults, once, public. Publish (seed, Merkle root $R_0$). Verifier key: **64 bytes**.

**Commit.** $C = \langle \mathbf{a}, \mathbf{G}\rangle$ — one group element (unchanged; compatible with existing Pedersen commitments).

**Open** (claim $\hat a(z) = v$), per IPA round $j = 1..k$:
1. Prover sends the usual $L_j, R_j$ **and** the Merkle root $R_j$ of the codeword folded by $x_{j-1}^2$ (round 1 uses the setup codeword).
2. Fiat–Shamir: $x_j \leftarrow H(\text{transcript so far})$ — *after* $R_j$.
3. After round $k$: the collapsed codeword is a single group element; with the public rescale $\prod_j x_j^{-1}$ it *is* the claimed $Q = G_0$ (`lens_foldAll_eq_genFinal`, proven).

**Verify.**
| # | check | cost |
|---|---|---|
| 1 | usual IPA: challenges, $b_0$ product, $P_0$ fold, final equation with $Q$ | $O(\log n)$ group ops |
| 2 | FRI consistency: $\lambda$ query positions walked down the $k$ levels; each level: 2 Merkle openings + check $w_{j+1}[i] = w_j[lo] + x_j^2\, w_j[hi]$ | $O(\lambda \log n)$ smul + $O(\lambda \log^2 n)$ hash |
| 3 | collapsed value $\cdot \prod_j x_j^{-1} = Q$ | $O(\log n)$ |

Level-$j$ query checks batch: $\sum_q \rho_q w_{j+1}[i_q] = \big(\sum_q \rho_q w_j[lo_q]\big) + x_j^2 \big(\sum_q \rho_q w_j[hi_q]\big)$ with short batching scalars — 2 full smuls per level + short-scalar aggregation.

## Costs (and the three-way comparison)

| | **Genesis** | **Lens** | **Prism** |
|---|---|---|---|
| verifier key | 32 B | **64 B** (+ anyone can recompute the root) | seed + root (same) |
| setup compute | none | $O(n\log n)$ smul, once | $\tilde O(n)$, once |
| proof | $O(\lambda\log^2 n)$ **field elts** (measured 3–8 MB) | **$2k$ grp + $k$ roots + $O(\lambda\log^2 n)$ hash** (est. ~0.3–0.5 MB) | $3k$ grp + $O(\lambda \log^2 n)$ hash + extra sumcheck rounds |
| verifier | $O(\lambda\log n)$ **field ops** (measured ~1–1.7 s, flat) | $O(\lambda\log n)$ **smul** + $O(\lambda\log^2 n)$ hash | same + reduce-sumcheck ($2k$ smul) |
| prover | GKR circuit, ~8× plain IPA (measured) | **fold + hash the codeword: ~2× plain IPA** | reduce + decide: ~4× MSM |
| protocol rounds | IPA + certificate walk | **just the IPA rounds** (merged) | IPA + sumcheck + BaseFold rounds |

Lens strictly improves Prism in this setting (shared challenges delete the reduce-sumcheck and the separate decide rounds; one fewer moving part) and beats Genesis on proof size (~20×) and prover (~4×). The trade against Genesis: the verifier's work shifts from *field* ops to *group* ops — asymptotically identical, concretely heavier per unit, so Genesis still wins wall-clock at small $n$ while Lens wins the proof-size axis everywhere and the verifier axis at large $n$.

## Soundness sketch (and the one paper-grade obligation)

- **Completeness** — proven in Lean (`SuccinctIPA/Lens.lean`): `lens_fold_factor` (round identity), `friFoldAll_eq_monomialEval` (folding = monomial-basis multilinear evaluation), `lens_foldAll_eq_genFinal` (collapsed codeword = $G_0$'s tensor sum), `lens_reduction`.
- **Proximity/consistency** — standard FRI round-by-round soundness over the group code (2025/1325 Lemma 7.2 / Thm 7.3 machinery): each committed level is either $\delta$-close to a fold of the previous or the $\lambda$ queries catch it; the honest chain ends at $G_0$.
- **The shared-challenge subtlety (the honest caveat):** $x_j$ plays two roles — IPA fold challenge and FRI fold challenge. Commit-then-challenge order makes it fresh for the proximity argument, and the IPA extractor rewinds on the same $x_j$ unchanged. What needs a careful write-up is the *joint* extraction argument (the rewinding for IPA must not break FRI's round-by-round bookkeeping, and vice versa). This is the analogue of Genesis's "composition unwritten" caveat — but here both halves are standard analyses of the *same* transcript rather than a circuit-wiring appendix.
- Sign/scale bookkeeping: the $\prod x_j^{-1}$ rescale is public; folds by $x_j^2 \neq 0$ are invertible.

## Status

Spec + Lean completeness core. Sage implementation is straightforward (no circuit machinery — native point ops only: encode, Merkle, fold, query) and slots into the existing benchmark harness.

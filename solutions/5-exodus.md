# Exodus — Genesis without the λ-grind: Pedersen-committed advice

*The FRI-free, hash-free answer to "small proof AND small verifier". Named for what it does: in Genesis every non-algebraic operation is imprisoned inside the circuit as a λ-deep chain of squarings; in Exodus **the advice escapes the circuit** — witnessed values (inverses, square roots, branch bits, scalar-mult traces) are committed with Pedersen over the same dlog basis and checked by one-layer relations. No Merkle trees, no FRI, no codes; hashing only as Fiat–Shamir (which Bulletproofs itself already requires).*

**Abstract.** Transparent, prime-order, no pairing, no unknown-order group, no recursion, **no hash-based commitments**. Genesis's certificate is already an information-theoretic GKR — its megabyte proofs and ~8× prover have a single cause: field inversion (~380 layers), Legendre tests (~380 each), constant-time Tonelli–Shanks (~1200), and double-and-add scalar multiplication (~510/round) are all *computed* in-circuit as λ = 255-deep squaring chains, and the sumcheck pays per layer. Exodus replaces every chain with **nondeterministic advice + a degree-≤5 check**, shrinking the circuit from ~7000 layers to **~100 wide, shallow layers**. The advice is sound without hashes because it is committed with **Pedersen over the same generator basis $\mathbf{G}$** (binding = the dlog-relation assumption, `pedersen_binding`), opened at the sumcheck endpoints by IPA instances whose terminal MSMs **random-linear-combine into the one delegated MSM claim** — so the opening regress bottoms out instead of recursing (`batch_amortization`, `advice_batch_two`).

## The transformations (each proven as a one-layer soundness atom)

| Genesis chain | depth | Exodus check | Lean |
|---|---|---|---|
| inversion `tv = den^(p−2)` | ~380 | advice `tv`; check `tv·den = 1` | `advice_inverse_sound` |
| Legendre `l = g^((p−1)/2)` + select | ~410 | advice bit `s`; checks `s(s−1)=0`, fused into sqrt check | `advice_branch_sound` |
| CT Tonelli–Shanks sqrt | ~1200 | advice `y`; check `y² = s·g₁ + (1−s)·g₂` | `advice_sqrt_sound`, `advice_branch_sound` |
| double-and-add (per fold round) | ~510 | advice = the 255-step trace, checked **in parallel** by one wide degree-4 RCB layer | RCB gadget (clean) |

Residual advice freedom (±y, both-branches-square) selects among finitely many valid SRS variants; any *fixed* choice is binding, and a prover that mixes choices between commit and open only breaks its own final IPA equation — the same argument as Genesis's sign-flexibility analysis.

## Why the advice commitment doesn't recurse

Advice vectors are committed as $C_{\text{adv}} = \langle \text{adv}, \mathbf{G} \rangle$ (same basis, pure dlog). The certificate's sumcheck endpoints demand MLE openings of the advice columns; each opening is a standard IPA whose transcript is $O(\log n)$ group elements and whose *terminal folded-generator claim* is a tensor MSM over the same $\mathbf{G}$. All such terminals — the main one and every advice opening — merge under verifier randomness into **one** MSM claim:

$$\Big\langle \textstyle\sum_i \mu_i\, \mathbf{s}_i,\ \mathbf{G} \Big\rangle \;=\; \sum_i \mu_i \big\langle \mathbf{s}_i, \mathbf{G} \big\rangle \qquad (\texttt{advice\_batch\_two} / \texttt{batch\_amortization})$$

and the delegated circuit folds the combined (sum-of-tensors) coefficient vector as 2–3 parallel tensor folds. One delegation serves everything; conservation of linear work is respected, not violated.

## Estimated costs (vs measured Genesis at $n = 2048$)

| | **Genesis** (measured) | **Exodus** (estimated) |
|---|---|---|
| circuit | ~7000 layers, λ-deep chains | **~100 layers**, deg ≤ 5, wide |
| proof | 8.4 MB field elts | **~300–400 KB** (10–15k field elts + ~1–2k commitment points) |
| verifier | ~45k sumcheck rounds ≈ 1.7 s | **~2–4k rounds** + short-scalar RLC of advice commitments — expect **3–5× faster** |
| prover | ~8× plain IPA (deep witness gen) | compute + commit advice ≈ **2–3× plain IPA** |
| commitments | none beyond Pedersen | Pedersen only (no Merkle) |
| assumptions | dlog + FS | **identical** |

## Honest caveats

- **Estimates, not measurements**: Exodus is specified and its soundness atoms are proven; the implementation (advice-column layout, the opening-batch protocol, the widened parallel RCB layer) is Genesis-scale engineering, not yet built.
- The **joint extraction** write-up (IPA extraction ∘ sumcheck ∘ batched advice openings) is the same class of paper-grade obligation as Genesis's composition caveat — all pieces are standard and share one transcript.
- Advice-column *count* management (fold traces are ~255 columns per round) costs the verifier a short-scalar RLC over the advice commitments; small-exponent batching keeps this to a few hundred cheap scalar mults.
- Genesis remains the zero-advice baseline; Lens/Prism remain the small-proof points **if** hash commitments are acceptable. Exodus is the small-proof point when they are not.

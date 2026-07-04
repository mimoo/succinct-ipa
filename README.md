# succinct-ipa

**Can a discrete-log inner-product argument (Bulletproofs) have a succinct verifier?**
This repo is a machine-checked investigation of that question — from Lean 4 impossibility
lemmas, through three original constructions, to a working Sage implementation on the
Pallas curve whose verifier **measurably beats the naive linear verifier**, with its
circuit layers formally verified in [clean](https://github.com/Verified-zkEVM/clean).

## TL;DR

The Bulletproofs verifier is linear for exactly one reason: the folded-generator MSM
$G_0 = \langle \mathbf{s}, \mathbf{G} \rangle$. Everything else is $O(\log n)$ (proven:
`bSuccinct_eq_bLinear`). The MSM cannot be removed in transparent prime-order dlog
(proven "verifier-needs-help" lemmas: `no_partial_read_verifier`,
`no_lossy_digest_verifier`) — but it can be **discharged by a prover-aided argument about
the fixed, public, seed-derived generators**. Three ways, in increasing practicality:

| # | solution | how the generator-MLE is discharged | status |
|---|---|---|---|
| 1 | [**Atlas**](solutions/1-atlas.md) | GKR delegation + Kedlaya–Umans preprocessed evaluation | spec (constants galactic) |
| 2 | [**Genesis**](solutions/2-genesis.md) | re-derive $\mathbf{G}$ from the seed *inside* the delegated GKR circuit | spec + Lean + clean gadgets + **Sage end-to-end + benchmarks** |
| 3 | [**Prism**](solutions/3-prism.md) | fold a Reed–Solomon encoding of $\mathbf{G}$ — group-native BaseFold ([Eagen–Gabizon 2025/1325](https://eprint.iacr.org/2025/1325)) | spec + Lean completeness core (`foldAll_eq_mleEval`) + **Sage benchmark vs linear IPA** |
| 4 | [**Lens**](solutions/4-lens.md) | **the IPA fold *is* an FRI fold** ($x^{-1}G_{lo}+xG_{hi} = x^{-1}(G_{lo}+x^2 G_{hi})$): the codeword folds with the IPA's own challenges, roots committed before each challenge — one merged transcript | spec + Lean core (`lens_foldAll_eq_genFinal`) + **Sage implementation + benchmarks** |
| 5 | [**Exodus**](solutions/5-exodus.md) | Genesis with **Pedersen-committed advice**: the λ-deep chains (inverse/sqrt/Legendre/double-and-add) become one-layer checks; advice openings RLC-merge into the single delegated MSM — **no FRI, no Merkle, dlog only** | spec + Lean soundness atoms (`advice_*_sound`, `advice_batch_two`) |

All three: transparent, prime-order, **no pairing, no unknown-order group, no recursion**.

## Asymptotic comparison

$n$ = vector size, $\lambda$ = 255 (field bits), sizes in group/field elements unless noted.

| scheme | verifier key / setup | commit | proof | verifier (online) | prover | assumption | recursion |
|---|---|---|---|---|---|---|---|
| Bulletproofs | $n$ points (or re-derive, $O(n)$) | 1 | $2\log n$ | $\Theta(n)$ smul | $O(n)$ smul | dlog | no |
| Hyrax | $n$ points | $\sqrt n$ | $O(\sqrt n)$ | $O(\sqrt n)$ | $O(n)$ | dlog | no |
| Dory | $O(n)$ pairing pre-processing (transparent) | 1 | $O(\log n)$ | $O(\log n)$ pairings | $O(n)$ | SXDH (pairing) | no |
| DARK | $O(1)$ | 1 | $O(\log n)$ | polylog | $O(n)$ heavy ops | unknown-order group | no |
| Halo / Nova | $O(1)$ | 1 | $O(\log n)$ | $O(1)$/step + one $\Theta(n)$ decider | ~2 MSM/step | dlog | **yes** |
| **Atlas** | $n^{1+\varepsilon}$ table (galactic) | 1 | polylog | polylog | $O(n\lambda)$ | dlog | no |
| **Genesis** | **32 B (a seed)** | 1 | $O(\lambda \log^2 n)$ field elts | $O(\lambda \log n)$ field ops | $O(n\lambda)$ (GKR, no FFT/commitments) | dlog | no |
| **Prism** | $\tilde O(n)$ RS-encode + Merkle root (transparent) | 1 | $O(\lambda \log^2 n)$ hashes | $O(\lambda \log n)$ smul + $O(\lambda\log^2 n)$ hash | $O(n)$ smul | dlog (+ROM) | no |
| **Lens** | same as Prism (**64 B vkey**) | 1 | $O(\lambda \log^2 n)$ hashes, **no extra rounds** (merged into IPA) | $O(\lambda \log n)$ smul + $O(\lambda\log^2 n)$ hash | **~2× plain IPA** | dlog (+ROM) | no |
| **Exodus** | 32 B (a seed) | 1 | est. **~300–400 KB** field elts + Pedersen points (**no hashes**) | est. ~2–4k sumcheck rounds (3–5× faster than Genesis) | est. ~2–3× plain IPA | dlog | no |

The one provably-empty cell (`LowerBound.lean`): a verifier that sees the generators only
through a **lossy linear digest** and takes no prover help cannot be sublinear. Every
construction above is an escape the lemmas themselves name: prover help, structure, or
recursion.

## Measured (Genesis, production pipeline, Pallas, single-thread Sage)

`sage/4-genesis-prod.sage` — Poseidon hash (t=3, α=5, 8 full + 56 partial rounds),
RFC-9380-style iso-SWU hash-to-curve (3-isogeny + constants computed by Sage at load),
CT Tonelli–Shanks and all curve arithmetic in-circuit, certified by a layered-sumcheck GKR.
The verifier's input is **the seed and the challenges** — it never touches the $n$ generators.

| $n$ | prove | plain IPA prove | overhead | **verify** | naive verify | **speedup** | proof size | vkey (ours / naive) |
|---|---|---|---|---|---|---|---|---|
| 64 | 11.5 s | 1.6 s | 7.4× | 0.66 s | 0.37 s | 0.6× | 3.4 MB | 32 B / 2.1 KB |
| 256 | 46.3 s | 6.2 s | 7.5× | 1.00 s | 1.27 s | **1.3×** | 5.1 MB | 32 B / 8.3 KB |
| 512 | 95.5 s | 12.2 s | 7.8× | 1.20 s | 2.51 s | **2.1×** | 6.1 MB | 32 B / 16.5 KB |
| 2048 | 391.4 s | 49.6 s | 7.9× | **1.69 s** | 9.74 s | **5.8×** | 8.4 MB | 32 B / 66 KB |

- **Verify time is ~flat in $n$** ($\lambda$-dominated); the naive verifier grows linearly.
  Crossover at $n \approx 256$; at $n = 2048$ Genesis also beats a pure-python-int MSM
  baseline on the same arithmetic backend (2.53 s, 1.5×).
- **Prover overhead is ~8× the plain Bulletproofs prover** in this setting (both in Sage;
  on an optimized EC backend the plain prover speeds up more than the certificate does, so
  expect a larger ratio there).
- **Proof size is the honest cost**: megabytes of certificate field elements
  ($O(\lambda\log^2 n)$, unoptimized). Prism trades exactly this axis: smaller
  constants via hashes instead of per-layer round polynomials.
- Run it: `GENESIS_BENCH="6,8,9,11" sage sage/4-genesis-prod.sage`
  (no env var → end-to-end demo with tamper tests).

## Measured (Lens, Pallas, single-thread Sage; rate-1/2 codeword, 20 demo queries)

`sage/6-lens.sage` — the small-proof/small-verifier point between Genesis and Prism:

| $n$ | setup (once) | prove | vs plain IPA | **verify** | naive verify | **speedup** | **proof** |
|---|---|---|---|---|---|---|---|
| 64 | 3.0 s | 3.2 s | 2.1× | 1.65 s | 0.37 s | 0.2× | **49.9 KB** |
| 256 | 8.5 s | 12.8 s | 2.1× | 2.16 s | 1.27 s | 0.6× | **76.4 KB** |
| 2048 | 98.9 s | 103.1 s | 2.1× | **3.01 s** | 9.78 s | **3.2×** | **125.7 KB** |

Versus Genesis at $n=2048$: **proof 67× smaller** (126 KB vs 8.4 MB), **prover ~4× lighter**
(2.1× plain IPA vs ~8×); the trade is a verifier that does group ops instead of field ops
(686 smuls vs Genesis's field-only walk), so Genesis still wins wall-clock verification at
small $n$ while Lens wins both proof size and verifier from $n \gtrsim 1024$. With
production-grade $\lambda \approx 80$ queries, multiply Lens's verifier/proof by ~4 — the
crossover moves out accordingly.

## Repository layout

| path | contents |
|---|---|
| `SuccinctIPA/` | Lean 4 + Mathlib theory (17 modules, no `sorry`): the $b_0$ identity, oracle framing, soundness atoms, the experiments ("conservation of linear work"), Hyrax/Dory/DARK/Nova cores, lower bounds, Genesis gate lemmas, Prism fold-=-MLE core |
| `solutions/` | the three construction specs (markdown + LaTeX) |
| `sage/` | executable demos: `2-genesis.sage` (oracle demo, secp256k1), `3-genesis-e2e.sage` (full pipeline, toy hash), `4-genesis-prod.sage` (**production**: Poseidon + iso-SWU + benchmarks), `5-prism.sage` (**Prism**: group FRI over Pallas, decide vs the linear IPA verifier + soundness tamper tests), `6-lens.sage` (**Lens**: merged IPA/FRI transcript, benchmarks + tamper tests) |
| `clean-circuits/` | formally verified circuit gadgets for clean (soundness **and** completeness proven): Poseidon rounds, exponent-chain steps, TS conditional, QR bit, curve eval, complete RCB point addition; `build.sh` clones clean and builds |
| `journal.md` | the full lab notebook: 18 entries from first diagnosis to production benchmark, including dead ends and bugs found |

## Build & run

```sh
# Lean theory (Mathlib pinned; ~5 min first time)
lake exe cache get && lake build

# clean-verified circuit gadgets
./clean-circuits/build.sh

# end-to-end demo (accept + tamper rejections), then benchmarks
sage sage/4-genesis-prod.sage
GENESIS_BENCH="6,8,9" sage sage/4-genesis-prod.sage
```

## Verification status (honest)

**Machine-checked** — the Lean theory (axioms only `propext/Classical.choice/Quot.sound`),
the clean gadgets (soundness + completeness; 8 `#eval` vectors pin Lean ↔ Sage), the
single-round sumcheck math, and the Genesis/Prism reduction cores.

**Not verified** — the Sage GKR engine internals (where the one real bug of this project
lived), the composed multi-round GKR soundness, Fiat–Shamir, the RCB-formulas ↔ group-law
link (tested on 120 cases), Poseidon parameter quality (SHA-derived constants + Cauchy MDS;
swap in Grain-generated pasta parameters for production), and Prism's proximity soundness
(cited to 2025/1325, Lemma 7.2 / Thm 7.3).

## Where the theory lives

The journey and the proofs: `journal.md`. Highlights — `bSuccinct_eq_bLinear` ($b_0$ is
log-time), `genFinal_eq_mle` (the MSM *is* a multilinear evaluation of the public
generators), `mleG_is_msm` (conservation of linear work), `no_lossy_digest_verifier` (the
wall), `genesis_reduction` + gate lemmas (Genesis), `foldAll_eq_mleEval` (Prism),
`lens_fold_factor` + `lens_foldAll_eq_genFinal` (Lens: the IPA fold *is* an FRI fold), and
the Hyrax/Dory/DARK/Halo/Nova cores that map the rest of the design space.

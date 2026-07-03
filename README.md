# succinct-ipa

A Lean 4 / Mathlib scaffolding that pins down what a **succinct verifier for a
discrete-log, IPA-style polynomial commitment** (Bulletproofs/Halo family) can and
cannot be — and certifies one solution.

## The question

Bulletproofs-style inner-product arguments have a verifier that runs `k = log₂ n`
cheap rounds but ends in **one `n`-sized multi-scalar multiplication (MSM)**, making
the verifier `Θ(n)` — *linear*. We want a *succinct* (`polylog n`) verifier, keeping
the assumption discrete-log (no pairings if possible).

## The answer this repo formalizes

The verifier's final check is

    P₀ = a·G₀ + (a·b₀)·U                                     (★)

with `G₀ = ⟨s, G⟩` (folded generators) and `b₀ = ⟨s, (z⁰,…,z^{n-1})⟩` (folded eval
scalar), where the scalar vector `s` is built from the round challenges `x₁…x_k`:
`sᵢ = Πⱼ xⱼ^{±1}` per the bits of `i`. Two facts decide succinctness:

1. **`b₀` is already succinct.** `s` is the coefficient vector of
   `g(X) = Πⱼ (xⱼ⁻¹ + xⱼ·X^{2^{j-1}})`, so `b₀ = g(z)` is an `O(k)` product even
   though `s` has `n` entries. **This is proven** as `bSuccinct_eq_bLinear`.

2. **`G₀ = ⟨s, G⟩` is *not* succinct** for unstructured generators — that's a genuine
   `Θ(n)` MSM (and matches the linear lower bound for commitments to unstructured
   generators). So a succinct verifier must obtain `G₀` another way.

We make "another way" an explicit object — a `GenOracle` carrying a claimed `G₀` plus
a `certifies` proof — instead of hiding it. Then:

> **`succinct_correct`** : given a correct `GenOracle`, the succinct verifier
> (`SuccinctAccept`, all `O(log n)` work) accepts a transcript **iff** the linear
> reference verifier (`LinearAccept`) does.

So "find a succinct dlog IPA verifier" reduces, provably, to "discharge the
`GenOracle`." Two ways to do that (discussed in `Protocol.lean`):

- **Accumulation / recursion (Halo-style)** — transparent, still plain dlog: defer
  `G₀`, fold the claim into an accumulator, pay the single linear MSM *once* per batch
  of `m` proofs → amortized `O(log n + n/m)` verifier.
- **Structured SRS** `Gᵢ = [τⁱ]` — then `⟨s,G⟩ = [g(τ)] = [bSuccinct x τ]`, one
  opening check → truly succinct, but needs trusted/updatable setup + pairings (leaves
  "plain dlog").

The honest conclusion the formalization encodes: dlog IPA has **no transparent,
non-interactive, non-recursive** succinct verifier; recursion amortizes it, structure
buys it outright. The dividing line is exactly the `GenOracle.certifies` hypothesis.

## Layout

| File | Contents |
|------|----------|
| `SuccinctIPA/Basic.lean`       | Group-as-`F`-module setting; `dot`, `msm`, `pedersen`. |
| `SuccinctIPA/SVector.lean`     | `sCoeff`, `bSuccinct`/`bLinear`, and the proof `bSuccinct_eq_bLinear`. |
| `SuccinctIPA/Protocol.lean`    | `LinearAccept`, `GenOracle`, `SuccinctAccept`, `succinct_correct`. |
| `SuccinctIPA/Soundness.lean`     | Binding, the Schnorr extractor, the oracle-necessity forgery, soundness transfer. |
| `SuccinctIPA/Experiments.lean`   | Creative attempts to kill the linear MSM, as proven identities. |
| `SuccinctIPA/Accumulation.lean`  | Halo-style fold: O(1)-per-step deferral, proven complete + knowledge-sound. |
| `SuccinctIPA/Hyrax.lean`         | √n verifier: rank-1 tensor split of the MSM (transparent, prime-order). |
| `SuccinctIPA/DARK.lean`          | Evaluation-as-division: O(1)-verifier check via unknown-order encoding. |
| `SuccinctIPA/DlogLayer.lean`     | Beneath the group: MSM = hidden inner product; structured⇔succinct⇔trapdoor. |

## Soundness (`Soundness.lean`)

Completeness says the honest transcript is accepted; soundness rules out cheating.

- **`pedersen_binding`** — under the discrete-log relation assumption (`NoDLogRelation`),
  the Pedersen commitment is injective. (Binding *is* the dlog-relation assumption.)
- **`schnorr_extract`** — the canonical special-soundness extractor, proven in full: two
  accepting transcripts with distinct challenges yield the witness. IPA's extractor is its
  `k`-fold recursion (interface `IPAExtractor`).
- **`oracle_necessary`** — a formal **forgery**: drop `GenOracle.certifies` and the succinct
  verifier accepts statements with no witness that the linear verifier rejects. The oracle
  is not optional.
- **`soundness_transfer`** — *with* a sound oracle, every soundness guarantee of the linear
  verifier transfers to the succinct one verbatim.

## Experiments (`Experiments.lean`) — can we still beat the linear MSM?

Each idea is reduced to a Lean identity; the proof assistant reports whether the `Θ(n)`
cost actually vanishes or merely relocates.

- **`sCoeff_eq_prod_ite`** — `s` is a rank-1 tensor `⊗ⱼ(xⱼ⁻¹,xⱼ)`; folding contracts it
  mode-by-mode, total `Θ(n)`. Why folding is intrinsic.
- **`genFinal_eq_mle`** — **the MSM is a multilinear evaluation**: `G₀ = (∏ⱼxⱼ⁻¹)·MLE_G(x²)`,
  with the *public* generators as coefficients. The door to sumcheck/tensor PCS.
- **`mleG_is_msm` + `mleG_add`** — …but that evaluation is *again* an `msm` over the
  generators. **Conservation of linear work**: sumcheck relocates the cost, never removes it.
- **`batch_amortization`** — the one genuine win under plain transparent dlog: `m` proofs
  share a single `Θ(n)` MSM (combined coefficient vector), so the per-proof verifier is
  `O(log n + n/m) → O(log n)`. This is the Halo amortization, proven.

The two real escapes leave a footprint in the assumptions (pairings/structured SRS, or
unknown-order groups), discussed in the file's closing notes.

## Making it happen — two constructions that actually work

The conservation result rules out *prime-order, transparent, non-recursive* succinctness.
Both standard escapes are constructed and proven here.

### Route 1 — accumulation (`Accumulation.lean`), prime-order, transparent

Defer the linear MSM into an `MSMClaim` and **fold** claims with a random challenge.

- **`MSMClaim.fold`** combines claimed values as `Q₁ + α•Q₂` — no `gens`, no MSM:
  **O(1) group ops per step**.
- **`fold_valid`** — completeness: folding valid claims stays valid.
- **`fold_sound`** — knowledge soundness: a fold valid at two distinct challenges forces
  *both* inputs valid (Schnorr-style extraction).

So `m` proofs ⇒ `m` succinct folds into one accumulator + **one** `Θ(n)` decider, ever.
This is what Halo2 does: the per-step verifier is succinct.

### Route 1b — Hyrax (`Hyrax.lean`), prime-order, transparent, non-recursive, `O(√n)`

The most direct "succinct (non-linear)" answer with **no** recursion / pairing / setup.
Reshape the `n` generators into a `√n × √n` grid; the IPA challenge vector is a full tensor,
so it factors rank-1 over any split (`sCoeff_factors`).

- **`msm_product_split`** — `⟨a⊗b, G⟩ = ⟨a, R⟩` with row commitments `R_i = ⟨b, gens(i,·)⟩`.
  The prover sends the `√n` rows; the verifier does only the `√n`-term outer MSM. **`O(√n)`
  verifier, transparent, prime-order.** Iterating the split is the Bulletproofs structure;
  *send* vs *fold* the rows is the commitment-size ↔ verifier-time dial.

### Route 2 — evaluation-as-division / DARK (`DARK.lean`), unknown-order, transparent

Encode the whole polynomial in one generator's exponent, `C = p(q)•g`, so evaluation
becomes division.

- **`dark_eval_check`** — completeness: a single witness `W` satisfies the one-line check
  `C − y•g = (q−z)•W`; the verifier does **O(1) group ops, independent of `n = deg p`**.
  Proof is the factor theorem `(q−z) ∣ p(q)−p(z)`.
- **`dark_witness_rigid`** — witnesses agree up to `(q−z)`-torsion; an unknown-order group
  (no small-order elements) pins `W`. This is a *truly* succinct, transparent,
  non-recursive verifier — bought by leaving prime-order dlog for hidden-order assumptions.

## Status

`lake build` succeeds (1281 jobs). `#print axioms` on every headline result —
`bSuccinct_eq_bLinear`, `succinct_correct`, `pedersen_binding`, `schnorr_extract`,
`oracle_necessary`, `soundness_transfer`, `genFinal_eq_mle`, `batch_amortization`,
`MSMClaim.fold_valid`, `MSMClaim.fold_sound`, `dark_eval_check`, `dark_witness_rigid` —
reports only `[propext, Classical.choice, Quot.sound]` (several use fewer; `dark_witness_rigid`
needs only `propext`). **No `sorry`, no extra axioms.** Discrete-log *hardness* enters only
as explicit hypotheses (`NoDLogRelation`, the unknown-order pinning); the multi-round IPA
forking is exposed as the `IPAExtractor` interface rather than re-derived.

## Build

```sh
lake exe cache get   # prebuilt Mathlib oleans (Mathlib pinned to v4.31.0)
lake build
```

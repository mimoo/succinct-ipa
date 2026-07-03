# Lab journal — a succinct verifier for dlog IPA

Goal: IPA/Bulletproofs-style polynomial commitments (discrete-log, transparent) have a
**linear-time verifier**. Can we get a **succinct** (polylog) verifier? Use Lean both as a
scaffolding to state precisely what a succinct verifier must satisfy, and as an adversarial
check on each idea — let the proof assistant tell us where a clever idea silently smuggles
the linear cost back in. Everything below compiles (`lake build`, Lean v4.31.0 + Mathlib),
no `sorry`, axioms limited to `propext / Classical.choice / Quot.sound`.

Group `G` is modelled as a vector space over the scalar field `F` (additive EC-point
notation, `•` = scalar mult). The `n = 2^k` coordinates are indexed by bit-sets
`t : Finset (Fin k)`; the integer coordinate is `coord t = Σ_{j∈t} 2^j`.

---

## Entry 1 — Diagnosis: where the linear cost lives

The IPA final check is `P₀ = a·G₀ + (a·b₀)·U`, after `k = log₂ n` cheap rounds. Two
"final" quantities:
- `b₀ = ⟨s, (z^i)⟩` — folded evaluation scalar,
- `G₀ = ⟨s, G⟩` — folded generator (an `n`-term **multi-scalar multiplication, MSM**),

where `s_i = Π_j x_j^{±1}` is built from the round challenges. **The MSM is the only
linear part**; everything else is already `O(log n)`. So the whole question is: can `G₀` be
obtained without the `Θ(n)` MSM?

---

## Entry 2 — `b₀` *is* succinct (the one piece that genuinely compresses)

`s` is the coefficient vector of `g(X) = Π_j (x_j⁻¹ + x_j X^{2^{j-1}})`, so
`b₀ = g(z)` is an `O(k)` product even though `s` has `n` entries.

> **`bSuccinct_eq_bLinear`** (`SVector.lean`): the `O(log n)` product form equals the
> `Θ(n)` expanded sum. Proof: distribute the product of binomials (`Finset.prod_add`),
> collect powers of `z`. ✓ proven.

This settles the `b₀` half. The fight is entirely about `G₀`.

---

## Entry 3 — Scaffolding: isolate the obstruction as an explicit oracle

Rather than hide the MSM, name it. A `GenOracle` carries a claimed `Q` for `G₀` plus a
`certifies : Q = genFinal gens x`. The succinct verifier (`SuccinctAccept`) does only
`O(log n)` field work and takes `G₀` from the oracle.

> **`succinct_correct`** (`Protocol.lean`): given a correct oracle, the succinct verifier
> accepts iff the linear reference verifier does. ✓ proven.

Net effect: "is there a succinct verifier?" reduces to "can you discharge `GenOracle`?"

---

## Entry 4 — Soundness

- **`pedersen_binding`** (`Soundness.lean`): under the discrete-log relation assumption
  `NoDLogRelation`, the Pedersen commitment is injective. (Binding *is* the dlog-relation
  assumption.) ✓
- **`schnorr_extract`**: the canonical special-soundness extractor — two transcripts with
  distinct challenges yield the witness. IPA's extractor is its `k`-fold recursion
  (interface `IPAExtractor`). ✓
- **`oracle_necessary`**: a formal **forgery** — drop `GenOracle.certifies` and the
  succinct verifier accepts statements with no witness that the linear verifier rejects.
  The oracle is not optional. ✓
- **`soundness_transfer`**: with a sound oracle, every soundness guarantee transfers. ✓

---

## Entry 5 — Experiments: trying to kill the MSM (and failing, instructively)

Each attempt reduced to a Lean identity; the assistant reported whether `Θ(n)` vanished.

- **`sCoeff_eq_prod_ite`** — `s` is a rank-1 tensor `⊗_j (x_j⁻¹, x_j)`. Folding contracts
  it mode-by-mode → still `Θ(n)`. Why folding is intrinsic.
- **`genFinal_eq_mle`** — recast: `G₀ = (Π x_j⁻¹)·MLE_G(x²)`, the multilinear extension of
  the *public* generator tensor. The door to sumcheck/tensor PCS.
- **`mleG_is_msm` + `mleG_add`** — …but that evaluation is *again* an `msm` over `gens`.
  **Conservation of linear work**: sumcheck/tensor tricks *relocate* the `Θ(n)` cost (to a
  random point, to the prover) but never remove it. The obligation never reduces to ⊥.
- **`batch_amortization`** — the one win available under plain transparent dlog: `m` proofs
  share a single MSM with combined coefficients `Σ_i ρ^i s(x_i)` → per-proof `O(log n + n/m)`.

**Dead-ends that all collapsed to conservation:** offline/online preprocessing (a single
arbitrary MLE evaluation depends on all `n` coefficients — no preprocessing helps);
Freivalds-style random projection (nothing to project away in a single inner product);
group/module sumcheck (the terminal random-point query is itself a full MSM).

Verdict: **no prime-order, transparent, non-recursive identity discharges the oracle.**

---

## Entry 6 — Two routes that actually work (constructed + proven)

The escapes leave a footprint in the assumptions.

### Route 1 — Accumulation (Halo/Halo2), prime-order, transparent (`Accumulation.lean`)
Defer the MSM into an `MSMClaim (s, Q)` and **fold** with a random `α`; the value fold is
`Q₁ + α·Q₂` — touches neither `s` nor `gens` → **O(1) group ops/step**.
- **`fold_valid`** — completeness. ✓
- **`fold_sound`** — knowledge soundness: a fold valid at two challenges forces both inputs
  valid (Schnorr-shaped). ✓

`m` proofs ⇒ `m` succinct folds + **one** `Θ(n)` decider, ever. This is the deployed answer.

### Route 1b — Hyrax: a transparent, prime-order, **non-recursive, sub-linear** verifier (`Hyrax.lean`)
The strongest *direct* answer to "succinct (non-linear)": no recursion, no pairing, no
trusted setup, **prime order** — verifier `O(√n)` (price: `O(√n)` commitment).
Reshape the `n` generators into a `√n × √n` grid `gens : I × J → G`. The IPA challenge
vector `s` is a **full tensor** (`sCoeff_eq_prod_ite`), so over any split it factors rank-1
`s(i,j) = a_i·b_j` (`sCoeff_factors`, proven). Then the size-`n` MSM becomes a `√n` *outer*
MSM over `√n` *row commitments*:

> **`msm_product_split`**: `⟨a⊗b, G⟩ = ⟨a, R⟩` with `R_i = ⟨b, gens(i,·)⟩`. ✓ proven.

The prover sends the `√n` row commitments `R` (that *is* the polynomial commitment); the
verifier computes only the `√n`-term `⟨a,R⟩`. **`O(√n)` verifier, transparent, prime-order,
non-recursive.** Iterating the split `c` times gives `O(c·n^{1/c})` — the Bulletproofs round
structure; what keeps Bulletproofs linear is that it *folds* the rows (verifier recomputes,
`Θ(n)`) instead of *sending* them (Hyrax). Send-vs-fold is the commitment ↔ verifier-time
dial, and `msm_product_split` is its hinge. **So "non-linear verifier" is achievable
transparently today at `√n`; strictly `O(log n)` transparent prime-order non-recursive is the
remaining wall.**

### Route 2 — Evaluation-as-division / DARK, unknown-order, transparent (`DARK.lean`)
Encode the whole polynomial in one generator's exponent, `C = p(q)·g`; evaluation becomes
division.
- **`dark_eval_check`** — completeness: one witness `W` satisfies `C − y·g = (q−z)·W`;
  verifier does **O(1) group ops, independent of `n`**. Proof = factor theorem
  `(q−z) ∣ p(q)−p(z)`. ✓
- **`dark_witness_rigid`** — witnesses agree up to `(q−z)`-torsion; an unknown-order group
  pins `W`. ✓ A truly succinct, transparent, non-recursive verifier — bought by leaving
  prime-order dlog.

---

## Entry 7 — One layer under: the discrete-log / exponent structure (`DlogLayer.lean`)

So far `gens : ι → G` was opaque. Go beneath the group abstraction: `G` is cyclic of prime
order, so `g_i = d_i · g` for a **secret dlog vector** `d`. Then the MSM, in the exponent,
is a single scalar inner product:

> **`msm_eq_dlog_inner`**: `⟨s, G⟩ = ⟨s, d⟩ · g`. ✓

So the verifier's linear check is really `⟨s, d⟩ = r` against a *hidden* vector `d` — i.e.,
a multilinear evaluation of the secret dlogs. This explains everything above at bedrock:

- **Structured secret dlogs ⇒ succinct.** If `d_i = τ^i`, then `⟨s, d⟩ = Σ s_i τ^i` is a
  polynomial evaluation (**`msm_structured_srs`**), and for the IPA tensor `s`,
  `genFinal = bSuccinct(x,z)·g` — a single succinctly-computable scalar
  (**`genFinal_structured`**, tying back to Entry 2). This is the KZG/structured-SRS layer.
- **But public structure ⇒ broken binding.** Geometric *public* generators have an explicit
  dlog relation `τ·g_i − g_{i+1} = 0`, so they are not binding
  (**`structured_breaks_binding`**). ✓

The two facts pincer the problem: succinctness needs the dlogs *structured* (so `⟨s,d⟩`
compresses) **and** *hidden* (so binding survives) — i.e., a **trapdoor** (`τ` secret =
trusted setup), or a **pairing** to evaluate the hidden structure (KZG/Dory), or you give
up prime-order and use hidden order (DARK). There is no transparent prime-order escape, and
now we can see *why* at the level of the discrete logs, not just the group elements.

---

## Entry 8 — Search: small proof **and** sublinear verifier

New constraint: polylog/small proof *and* sublinear verifier. Hyrax fails it — its proof is
`√n`. Searched the prime-order space again:

- **Nesting Bulletproofs to shrink Hyrax's proof = Bulletproofs itself** (log proof, linear
  verifier). The intermediate row-folds the verifier needs are `√n` group elements; to avoid
  sending them you must *commit* to a vector of group elements and open it homomorphically —
  which needs a **bilinear map**. No pairing ⇒ no compression below `√n`.
- This is the same wall as `structured_breaks_binding`: compressing generators ⇔ a public
  dlog relation ⇔ broken binding. So **small-proof + sublinear-verifier is unavailable in
  transparent prime-order dlog.** It requires leaving prime order.

Concrete recommendation — **DARK** (unknown-order, e.g. transparent class groups): commitment
and per-opening proof are **`O(1)` group elements** (vs Hyrax's `√n`), verifier polylog, no
trusted setup. Strengthened the formalization toward a full protocol:
- **`dark_commit_split`** — `Commit(p_L + X^m p_R) = Commit(p_L) + q^m·Commit(p_R)`: the
  commitment splits with the polynomial, giving the `O(log n)` degree-halving recursion with
  `O(1)` verifier work per round. ✓
- **`dark_eval_batch`** — many openings batch under a random `α` into **one** `O(1)` witness
  and **one** check. ✓ (axioms: only `propext`.)

Net: DARK gives transparent, `O(1)`-proof, polylog-verifier — the small-proof sublinear
protocol the prime-order world can't provide. The prime-order alternative with small proofs
is recursion (Halo), already covered by `fold_sound`.

## Entry 9 — Better than Bulletproofs: polylog proof **and** polylog verifier (`Dory.lean`)

Goal restated sharply: beat Bulletproofs — `O(log n)` proof *and* `o(n)` verifier. The
prime-order wall (Entry 8) said you must compress the generator-folds, which needs a
**bilinear map**. So stop avoiding pairings — *use* one. A pairing is a dlog construction
(SXDH), and **Dory** (Lee, TCC'21) is transparent (no trusted setup): `O(log n)` proof,
`O(log n)` verifier.

Mechanism, formalized: model the pairing as `e : G₁ →ₗ[F] G₂ →ₗ[F] T` and define the
**inner-pairing-product** `ipp(G,H) = Σ e(G_i,H_i)` — a binding, *bilinear* commitment to the
generator vector.
- **`ipp_add_left/right`, `ipp_smul_left/right`** — `ipp` is bilinear. ✓
- **`ipp_fold`** — folding `a↦a+x·b`, `c↦c+y·d` decomposes the commitment into four
  sub-products; the two **diagonals** depend only on public `G,H` (precomputable,
  transparent), the two cross-terms are sent by the prover. Verifier folds the generator
  commitment in **O(1) per round** → `log n` rounds, never the `Θ(n)` MSM. ✓
- **`msm_pairing`** — the exact MSM that made the IPA verifier linear, paired against a fixed
  `h`, becomes a combination of *precomputable* `e(G_i,h)`; the fold then collapses it to
  `O(log n)`. ✓

This is the genuine win: the bilinear map is precisely the "foldable commitment to group
elements" prime-order lacks (`structured_breaks_binding`). **Verdict on the landscape:**
polylog-proof + polylog-verifier + transparent is achievable — with a pairing (Dory) or in
an unknown-order group (DARK). It is *not* achievable in prime-order dlog without recursion;
there `√n` (Hyrax) is the floor. The choice is which structure to spend, and every option is
now a checked theorem here.

## Entry 10 — The lower bound, and the verdict (`LowerBound.lean`, `Dory.dory_round`)

To stop hand-waving "the verifier must be linear," proved it. **`no_partial_read_verifier`**:
if `s` has all entries nonzero, any verifier that decides `⟨s,d⟩ = Q` while reading only a
*strict* subset `S ⊊ univ` of coordinates is unsound — pick `j ∉ S`, flip `d_j`, the verdict
can't change (it didn't read `j`) but the truth did. **`ipa_verifier_must_read_all`**
specializes to the IPA challenge vector (`sCoeff_ne_zero`: every entry nonzero). So an
*unaided, transparent* dlog verifier is information-theoretically **linear**. This is the
matching impossibility to all the constructions — it says sublinearity *requires* one of:
prover help (Hyrax), a pairing (Dory), an unknown-order group (DARK), or recursion (Halo).

**Verdict — the requested object (simple dlog, polylog proof, polylog verifier):**
- **In prime-order dlog: impossible** without recursion (lower bound above).
- **Achievable, and simple, with a pairing — Dory** (transparent, no setup). Its complete
  per-round reduction is proven: **`dory_round`** — `C' = (precomputed diagonal) + x·L + x⁻¹·R`
  equals `ipp(G',H')` for the folded half-length vectors, **O(1) verifier work/round**,
  `log n` rounds ⇒ **O(log n) proof, O(log n) verifier**. This *is* the Bulletproofs IPA with a
  foldable pairing commitment, so the verifier is logarithmic instead of linear.
- **Also achievable in an unknown-order group — DARK** (transparent class groups): O(1)
  commitment & opening, polylog verifier (`dark_eval_check`, `dark_commit_split`).

So the solution exists and is formalized; the lower bound proves the pairing / unknown-order
is *necessary*, not a shortcut. Prime-order + polylog-verifier + no-recursion is the one
provably empty cell.

## Entry 11 — Closing the prime-order question: the digest lower bound

User constraint hardened: **no pairing, no unknown-order group.** So the question is whether a
*prime-order* transparent scheme can have polylog proof **and** polylog verifier. My earlier
bound only ruled out a verifier that reads `G` directly. A real scheme gives the verifier a
*digest* (preprocessing / a commitment) — so I strengthened it.

**`no_lossy_digest_verifier`**: model the verifier's entire view of the generators as a
**linear digest** `D : (ι→F) →ₗ M` (this is exactly the "algebraic / dlog" restriction —
every transparent prime-order view of `G` is linear in `G`: Pedersen commitments, precomputed
tables, partial reads, folds).  If `D` collapses any direction `v` the inner product sees
(`D v = 0`, `dot s v ≠ 0`), sound verification is impossible — `G = 0` and `G = v` share a
digest but differ in truth.  By rank–nullity a sound digest needs rank `≥ n−1`, so **the
verifier's view of the generators is Ω(n)**.

This is the bilinear-map-free wall, now a theorem: in prime-order transparent dlog, *any*
linear compression of the generators that still verifies is Ω(n).  The only escapes are
exactly the ones the user forbade (a pairing makes the digest of *group elements* foldable —
Dory; unknown order makes the integer-encoding succinct — DARK) or **recursion** (defer the
Ω(n) check into an accumulator — Halo, not forbidden, but it keeps one linear decider).

**CORRECTION (do not trust the earlier phrasing).**  The lower bounds proved here are weaker
than "no sublinear argument system exists".  They model a verifier that (i) takes **no proof /
prover message** — only a (linear) digest of `G` and the claim `Q`, and (ii) decides the
relation as a perfect `↔`.  So what is actually proven is: *the verifier cannot do the MSM
check by itself from sublinear/linear info about the generators* — i.e. the **necessity of
prover help or structure**.  This does NOT rule out a proof-aided sublinear verifier, and the
`Ω(n)` rank–nullity claim was prose, not formalized.  A genuine impossibility for prime-order
*argument systems* is much harder, lives in idealized (GGM/AGM) models, and is closer to
open/folklore than cleanly proven.  Treat these as "verifier needs help" lemmas, not an
impossibility theorem.

## Entry 12 — The scheme, within the constraints (`Scheme.lean`)

Constraints held firm: prime-order, transparent, **no pairing, no unknown-order**. The lower
bounds (correctly read: "the verifier can't do the MSM alone") force the one linear op to be
*relocated*, not removed. The scheme that does this and meets every constraint is
**accumulation** (Halo-style split-accumulation) — recursion/deferral was never forbidden.

- Commit = Pedersen; open = Bulletproofs IPA → `O(log n)` proof, yielding a deferred claim
  `(s, Q)` where `s` is implicit (recomputable from the `O(log n)` challenges).
- **`MSMClaim.fold_Q_is_local`** — the verifier's per-fold group work is exactly `Q_acc + α·Q`,
  a function of `(Q₁,Q₂,α)` alone, **independent of `gens`, `s`, `n`**. ✓ (`rfl`)
- **`MSMClaim.accumulate_valid`** — folding a base claim with any list of individually-valid
  per-proof claims yields one valid accumulated claim. ✓ So `m` proofs are certified by `m`
  cheap `O(1)` folds + **one** MSM decider, not `m` deciders.
- Soundness of a fold: **`MSMClaim.fold_sound`** (Entry 6).

Honest cost accounting: per-proof **online** verifier `O(log n)`; the single `Θ(n)` decider
runs once per batch/chain (amortized `O(log n + n/m)`), or never under recursion (IVC), where
the accumulator is carried into the next proof. **This is a real prime-order scheme with a
polylog per-proof verifier — no pairing, no unknown-order.** The one caveat, stated plainly:
it does not give a *single-shot, non-amortized, non-recursive* polylog verifier — that object
is (believed) not achievable in prime-order dlog, and the honest lower bounds above say the
verifier cannot avoid the linear anchor by itself. Accumulation moves it off the per-proof path
with `O(1)` work; that is the achievable target and it is proven here.

## Entry 13 — The prover objection, and the answer: pre-proof recursion / folding (`Nova.lean`)

New constraint: Halo-style accumulation is **post-proof recursion** — the prover generates a
full proof *every step*, and the next step proves "I verified the last proof." Prover-heavy.

The fix is to invert the order: **fold first, prove once — Nova**. Two *unproven* computation
claims (relaxed R1CS instances `(Az)∘(Bz) = u·(Cz) + E`) fold under a random challenge; the
plain-R1CS cross terms are absorbed into the error vector `E` and scalar `u` — that is the
entire reason "relaxed" exists. Per step the prover computes **one cross-term `T` and one
Pedersen commitment to it** (native group ops, no FFT blowup, no proof generation, no
verifier-in-circuit); the verifier folds commitments with **O(1) group ops**. One single
(IPA-style) proof is produced at the very end of the chain.

Proven, axiom-clean:
- **`nova_fold`** — the folding identity (completeness): satisfying instances fold to a
  satisfying instance with `E' = E₁ + r·T + r²·E₂`, `u' = u₁ + r·u₂`, `z' = z₁ + r·z₂`, and
  `T` computable from the two instances alone. ✓
- **`quadratic_vanish`** — knowledge-soundness core: the folded defect is *quadratic* in `r`;
  vanishing at **three** distinct challenges forces all coefficients (both original defects)
  to zero. The degree-2 analogue of `fold_sound`; why 3-transcript rewinding extracts. ✓
- **`nova_commitment_fold`** — the verifier's entire group work is homomorphic commitment
  folding; it never touches a generator. ✓

Cost per step: prover ≈ 2 MSM commits (vs. full proof generation + verifier circuit in Halo);
verifier O(1) group ops. Prime-order, transparent, Pedersen-only — no pairing, no unknown
order. This is the light-prover scheme the objection asks for: recursion cost paid in *native
field/group ops*, proving paid **once**.

## Entry 14 — The divide-and-conquer unlock: delegation + preprocessing (`Delegation.lean`)

User intuition: "there must be a divide-and-conquer algorithm somewhere." There is — and it
came with **two tools we had never reached for**, because both live outside the
commitment-scheme toolbox we'd been searching in:

1. **Interactive proofs (sumcheck/GKR) — delegation, not arguments.** The verifier's linear
   step `G₀ = ⟨s,G⟩` is a *deterministic computation on public inputs* — no witness. Certifying
   it needs no cryptography: sumcheck climbs the MSM's binary addition tree (the D&C tree),
   `O(1)` verifier work per level, *information-theoretic* soundness (no new assumption). The
   D&C engine is now proven: `sum_split`/`msm_split` (the halving step, field and group level),
   `sumcheck_round_complete` (round check), `disagreement_is_root` + `cheating_caught`
   (1-variable Schwartz–Zippel round soundness: a lying round polynomial survives a random
   challenge with prob ≤ d/|F|). ✓ all axiom-clean.
2. **Preprocessing polynomial evaluation (Kedlaya–Umans).** After `log n` rounds the D&C
   bottoms out in one MLE evaluation of the circuit input = (challenges — tiny, handled by the
   proven tensor identity) + (coordinates of the **fixed public** generators). The latter is a
   fixed public polynomial: one-time public `n^{1+ε}` preprocessing gives **any** later
   evaluation in `polylog` — the circularity that killed every earlier attempt terminates in a
   *data structure*, not another proof. Recursion replaced by algorithmics.

**Assembled scheme:** transparent, prime-order, no pairing, no unknown-order, **no recursion**:
Pedersen commit + Bulletproofs transcript (`O(log n)`) + Fiat–Shamir'd GKR certificate for the
MSM (`polylog`, unconditionally sound) + KU evaluation for the generator MLE (`polylog` online).
Verifier: polylog. Proof: polylog. Prover: linear, no commitments/FFTs/verifier-in-circuit.

Caveats, honestly: KU preprocessing is asymptotic (galactic constants today, `n^{1+ε}` table);
the end-to-end composition (BP extraction + FS'd GKR + KU oracle) needs a paper-grade proof;
setup rises from `Θ(n)` to `n^{1+ε}` one-time public work. But as an *asymptotic answer* to
"transparent prime-order dlog, polylog proof, sublinear verifier, non-recursive" — this
composition does it, and the divide-and-conquer intuition was exactly right: the missing move
was delegating the D&C tree information-theoretically and bottoming out in preprocessing.

## Open threads / next

1. **Self-eliminating accumulation (full IVC / cycle of curves).** Recurse the single
   decider through a 2-cycle so even the final `Θ(n)` op is amortized to zero per step.
   Needs a model of "the accumulator-check inside the next circuit."
2. **A genuine lower bound** for prime-order transparent verifiers — model the verifier as a
   query machine over `gens` and prove it must read `Θ(n)` of them. Turns "conservation of
   linear work" from an endpoint-identity into a computation-model theorem.
3. **Functional-commitment view of `d`.** The dlog layer says the generators are a
   commitment to `d`; a transparent succinct evaluation of `d` is exactly the missing piece
   — is there any transparent assumption (lattices? unknown order on the *coefficients*?)
   that gives it without pairings?

## Theorem index (all proven, `lake build` green, 1281 jobs)

| Theorem | File | Reading |
|---|---|---|
| `bSuccinct_eq_bLinear` | SVector | `b₀` is `O(log n)` |
| `succinct_correct` | Protocol | succinct ⇔ linear, given oracle |
| `pedersen_binding` | Soundness | binding = dlog-relation assumption |
| `schnorr_extract` | Soundness | special-soundness extractor |
| `oracle_necessary` | Soundness | forgery without the oracle |
| `soundness_transfer` | Soundness | soundness carries over |
| `genFinal_eq_mle` | Experiments | MSM = MLE of public generators |
| `mleG_is_msm` | Experiments | conservation of linear work |
| `batch_amortization` | Experiments | m proofs, one MSM |
| `MSMClaim.fold_valid/_sound` | Accumulation | Halo fold complete + sound |
| `msm_product_split` | Hyrax | rank-1 ⇒ √n outer MSM |
| `sCoeff_factors` | Hyrax | IPA s-vector is rank-1 over any split |
| `dark_eval_check` | DARK | O(1) verifier, unknown order |
| `dark_witness_rigid` | DARK | unknown order pins the witness |
| `msm_eq_dlog_inner` | DlogLayer | MSM = hidden inner product |
| `msm_structured_srs` | DlogLayer | geometric dlogs = poly eval |
| `genFinal_structured` | DlogLayer | structured ⇒ `bSuccinct·g` |
| `structured_breaks_binding` | DlogLayer | public structure ⇒ not binding |

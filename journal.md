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

## Entry 14 — **Atlas**: the divide-and-conquer unlock — delegation + preprocessing (`Delegation.lean`)

> **Named construction: Atlas** — the verifier consults a giant precomputed map (the
> Kedlaya–Umans table). Full spec: `solutions/1-atlas.md`.

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

## Entry 15 — **Genesis**: de-galacticizing — the SRS is a program, not a table (`Genesis.lean`)

> **Named construction: Genesis** — the generators are grown from a seed *inside* the
> delegated circuit. Full spec: `solutions/2-genesis.md`. Gate-level correctness verified in
> `SuccinctIPA/Genesis.lean`: `genesis_reduction` (certifying the seed-composed computation
> certifies the SRS claim), `double_and_add_step` (scalar-mult layer),
> `square_and_multiply_step` (exponent-chain layer), `sqrt_exp_correct` (the deterministic
> in-circuit square root is correct, via Euler's criterion).

The galactic constants in Entry 14 come only from Kedlaya–Umans, and KU was only needed
because the delegated circuit's *input* contained the `n`-sized generator table. But the table
is not incompressible data — we generated it: `G_i = HashToCurve(seed, i)`. Fix:

> **Feed the circuit the seed, not the generators; derive the SRS inside the delegated
> circuit.** Input shrinks to `O(log n)` (seed + challenges); the final input-MLE check —
> the only reason KU existed — becomes trivial. KU deleted, galactic constants gone.

Everything in-circuit is deterministic, uniform, shallow: Poseidon-style algebraic
hash-to-curve (GKR-friendly), sqrt as a fixed exponentiation `a^((p+1)/4)` (depth `O(λ)`,
**no nondeterministic advice** — advice would be `n`-sized input and reintroduce the
circularity), double-and-add + addition tree (depth `O(λ + log n)`).

Why this doesn't contradict `no_lossy_digest_verifier`: the bound bites verifiers that *view*
`G` through sublinear info, and truly random generators are incompressible. But binding only
needs *pseudorandom* generators (the standard BP assumption), which have `O(1)` description —
and the verifier never views them; it verifies the program that computes them. "SRS = data"
was the mistake; "SRS = program" is the unlock.

Resulting costs: setup = publish a seed; verifier polylog with small concrete constants;
proof = Virgo/Libra-style polylog field elements (~tens of KB); prover = linear,
`~n·O(λ)` GKR gates at a few field ops each, no commitments/FFTs — est. 100–1000× the raw
MSM. Zk-prover-grade, not galactic.

Remaining design problem (honest): the two-field issue — curve ops over `F_p`, tensor/scalars
over `F_q`. Either non-native `F_q` arithmetic inside the `F_p` GKR (tens-of-× constant
blowup, simplest) or a linked `F_q`-sumcheck + `F_p`-GKR pair via bit-decomposition claims.
Engineering, not a conceptual barrier; where a paper would spend its pages.

## Entry 16 — Genesis runs end-to-end on Pallas (`sage/3-genesis-e2e.sage`)

Everything implemented, no oracle stand-ins: the verifier **never touches the n generators**.
The delegated circuit spans the entire pipeline, certified layer-by-layer by a hand-rolled
GKR (layered sumcheck with eq-wiring, multi-claim kernels, split/transfer steps):

- **derivation**: toy algebraic hash (x^5 rounds) → 4-candidate window → in-circuit Legendre
  symbols (fixed exponentiation chains) → first-QR selection → **constant-time 31-iteration
  Tonelli–Shanks sqrt in-circuit** (both Pasta fields are 2-adic; the ±1-test bits are linear
  gadgets, validated natively first);
- **fold**: k rounds of the IPA generator fold via **complete Renes–Costello–Batina point
  addition** (a=0, b3=15; complete ⇒ one formula covers add/double/identity) with
  double-and-add over **public challenge bits** — Pasta dissolves the two-field problem
  because each fold layer's scalar is a single public constant;
- **input check**: the circuit input is (seed, challenges) — the verifier's terminal MLE
  evaluation is the closed form `seed + Σ pt_t·2^(nv−1−t)`, O(log n). The Genesis endpoint.

Results (k=2/3, Pallas, single-thread Sage): ~1700–2200 layers; prover 0.6–1.3s; verifier
0.2–0.3s ≈ 230k field ops, **λ·log n–dominated, flat in n**; proof ≈ 26–40k Fp elements.
Honest run accepts; four tamper tests reject (off-curve Q, on-curve-but-wrong Q, corrupted
certificate polynomial, wrong evaluation value). One engine bug found and fixed en route:
`eq_array` built kernels with reversed variable order — invisible at nv≤1, caught by the
prover-side invariant assert at the first nv=2 kernel and a minimal reproduction.

Demo-grade caveats stay caveats: toy hash (not Poseidon), Legendre-window hash-to-curve
(production: iso-SWU), λ=255 exponent grind dominates constants, un-optimized single-thread
GKR. The architecture is the point: **setup = a seed; the generators never leave the prover.**

## Entry 17 — Formally verified circuits (clean) + the benchmark

Goal: circuits formally verified in **clean** (Verified-zkEVM's Lean 4 circuit framework),
mirrored in Sage, and a measured wall-clock **win over the naive linear verifier**.

**clean gadgets** (`clean-repo/Clean/Gadgets/Genesis.lean`, `lake build` green, 1664 jobs,
axiom-clean): six `FormalCircuit`s with soundness *and* completeness proven —
- `HashRound` — `out = (x+rc)^5` (the toy-hash round)
- `SquareStep` / `SquareMulStep` — the two fixed-exponent-chain layers (public bit ⇒ two
  branch-free gadgets, exactly matching how the Sage builder emits layers; clean's
  elaborator rejects Lean-level `if` inside `main`, which forced — correctly — the same
  design the Sage circuit already had)
- `CondMulConst` + theorem `condMul_spec_ite` — the constant-time Tonelli–Shanks
  conditional step, with its `if t=1 then w else w·z` meaning proven for `t ∈ {±1}`, char ≠ 2
- `QrBit` — Legendre-to-selector `(1+l)/2`
- `RcbAdd` — the complete Renes–Costello–Batina projective addition (a=0), the fold's
  point operation, verified against `rcbSpec` (the identical chain the Sage `rcb_add` runs)

**Lean↔Sage link**: `#eval` test vectors over `ZMod pallasP` printed by the Lean build
(`100000, 275, 36, 0, (p−430, 379, 228)`) are asserted in Sage (`clean_vectors_check`)
against the *actual* Sage layer functions. Specs are plain Lean functions mirrored verbatim.

**A real bug found by scaling the benchmark**: the transparent setup retried seeds until
*every* index found a QR among 4 hash-to-curve candidates — success probability
`(15/16)^n`, which is ~2% at n=64 and ~e^-64 at n=1024: the setup could never terminate at
useful sizes. Fixed by widening the window to `CAND=8` (per-index failure `2^-8`) and making
the first-QR selection *iterative* (deg-2 `s_c = q_c·np`, `np ← np·(1-q_c)` layers) instead
of one degree-C layer. Re-verified end-to-end. Also optimized: identity-carry layers now
share list objects instead of copying (memory/witness-gen ×3).

**Benchmark** (`GENESIS_BENCH=... sage sage/3-genesis-e2e.sage`, Pallas, same machine,
both verifiers in Sage; py-int = naive MSM re-done on the sumcheck verifier's
plain-arithmetic backend):

| n | prover | **Genesis verify** | naive linear (Sage) | naive (py-int) | speedup |
|---|---|---|---|---|---|
| 64 | 13.4s | 0.70s | 0.36s | 0.08s | 0.5× |
| 256 | 55.5s | 1.05s | **1.27s** | 0.31s | **1.2×** |
| 512 | 113.2s | 1.25s | **2.47s** | 0.61s | **2.0×** |

| **2048** (CAND=12) | 530.9s | **1.79s** | **9.90s** | 2.44s | **5.5×** |

**Verdict: the Genesis verifier beats the naive linear verifier from n ≈ 256, reaching
2.0× at n = 512 and 5.5× at n = 2048 — where it also beats the backend-parity py-int
naive MSM (2.44s vs 1.79s, 1.4×).** Genesis verify grows ~log n (λ-dominated: 0.70 →
1.79s while n grows 32×); the naive verifier grows linearly (~4.8 ms/term). Goal met on
both baselines, with formally verified circuits (clean) pinned to the Sage implementation.

## Entry 18 — Production derivation: Poseidon + iso-SWU (`sage/4-genesis-prod.sage`)

Upgrades from the review of Entry 16/17's honest gaps:

1. **clean sources moved into our repo** (`clean-circuits/`: `Genesis.lean`,
   `GenesisCheck.lean`, `build.sh`, README) — symlinked into the gitignorable `clean-repo/`
   checkout for building; pushable.
2. **Toy hash → Poseidon**: t=3, α=5, 8 full + 56 partial rounds over the Pallas base
   field; SHA-derived round constants, Cauchy MDS (invertible; swapping in official
   Grain-generated pasta parameters is mechanical). One deg-5 circuit layer per round —
   64 layers, 3 state columns per lane.
3. **Legendre-window hack → RFC-9380-style iso-SWU**: simplified SWU on the 3-isogenous
   curve (found by Sage at load: `E.isogenies_prime_degree(3)`, A·B ≠ 0), SWU constant
   Z = −5 computed by the RFC criteria, in-circuit inversion via a `x^(p−2)` chain, and the
   dual 3-isogeny back to Pallas evaluated **projectively** (no inversions). **No candidate
   windows, no seed retries** — SWU guarantees one of gx1/gx2 is square, killing Entry 17's
   `(1−2^−C)^n` setup-probability problem structurally. Exceptional inputs (probability
   ~2^−250) checked at setup. Single-u encode_to_curve (NU variant); sgn0 canonicalization
   skipped (deterministic + consistent, noted).
4. **clean gadgets extended**: `PoseidonRound.circuitFull/-Partial` and `CurveEval`
   (g(x) = x³+Ax+B given a verified square) — soundness + completeness proven, first
   build; 8 `#eval` vectors now pin Lean ↔ Sage (all assert in `clean_vectors_check`).

**Production benchmark** (Poseidon + iso-SWU pipeline, Pallas):

| n | prover | Genesis verify | naive linear (Sage) | speedup |
|---|---|---|---|---|
| 64 | 11.6s | 0.67s | 0.37s | 0.6× |
| 256 | 46.1s | 1.11s | 1.31s | 1.2× |
| 512 | 111.5s | 1.79s | **3.93s** | **2.2×** |

| **2048** | 423.6s | **1.72s** | **10.18s** | **5.9×** |

Same crossover shape as the toy pipeline (win from n ≈ 256), now with a production-shaped
derivation — and at n=2048 the production verifier (1.72s) also beats the backend-parity
py-int naive MSM (2.46s, 1.4×), with all 8 Lean-verified vectors pinning the circuits.

**Extended bench** (with sizes + plain-Bulletproofs-prover baseline; canonical table now in
`README.md`): prover overhead is **~7.5–8× the plain IPA prover** (both in Sage); proof
size 3.4–8.4 MB of certificate field elements (O(λ·log²n), the honest cost axis Prism
targets); verifier key **32 B (the seed)** vs the naive verifier's n·33 B generator table.

**Entry 18b — Prism lands in Lean.** `SuccinctIPA/Prism.lean` (solution 3,
`solutions/3-prism.md`): the group-native BaseFold core — `foldStep`/`foldAll`,
`eqW_cons`, and **`foldAll_eq_mleEval`** (repeated FRI-style folding = multilinear
evaluation of the generator codeword), plus `prism_reduction` and `mleEval_eq_msm`
(conservation still holds; succinctness comes from checking the fold against a Merkle-
committed codeword, the "prover help + nonlinear digest" escape the lower bound permits).
Three proof holes fixed (dead tactics after a self-closing `congr`, `Subsingleton.elim` →
`funext elim0` in the base case, and a flipped `show`); full Lean build green (1419 jobs),
axiom-clean. README rewritten as the canonical map: solutions, asymptotic comparison table,
measured benchmarks.

## Entry 19 — **Lens**: the IPA fold *is* an FRI fold (`solutions/4-lens.md`)

Goal: something between Genesis (fat proof, field-op verifier) and Prism (extra
reduce/decide phases) — small proof AND small verifier — with the user's hint: *use the IPA
folding itself to help prove the linear part*. The unlock was already in our theorems:

> `genFinal_eq_mle`: G₀ = (∏xⱼ⁻¹)·MLE_G(x²) — and per round,
> **x⁻¹·G_lo + x·G_hi = x⁻¹·(G_lo + x²·G_hi)**: the IPA generator fold IS an FRI fold by
> challenge x², times a public scalar.

So the prover Merkle-commits an RS encoding of **G** (bit-reversed so round-1's IPA split is
the first folded variable) and folds it **with the IPA's own challenges**, committing each
level's root *before* the next challenge — proper commit-then-challenge order, which also
closes the ordering gap flagged as a stand-in in `5-prism.sage`'s decide (its fold challenges
were the IPA's x² but the roots weren't in the transcript before the challenges). One merged
transcript; no circuit; no separate decide rounds.

**Lean** (`SuccinctIPA/Lens.lean`, first-attempt build, axiom-clean): `lens_fold_factor`
(round identity), `friFoldAll_eq_monomialEval` (folding = monomial-basis MLE),
`lens_foldAll_eq_genFinal` (collapsed codeword = folded generator), `lens_reduction`.
Full project: 19 modules, 1420 jobs, no `sorry`.

**Sage** (`sage/6-lens.sage`, first-run pass incl. tamper rejects; in-prover assert checks
the Lean identity numerically):

| n | setup(once) | prove | vs plain IPA | verify | naive | speedup | proof |
|---|---|---|---|---|---|---|---|
| 64 | 3.0s | 3.2s | 2.1× | 1.65s | 0.37s | 0.2× | 49.9 KB |
| 256 | 8.5s | 12.8s | 2.1× | 2.16s | 1.27s | 0.6× | 76.4 KB |
| 2048 | 98.9s | 103.1s | 2.1× | **3.01s** | 9.78s | **3.2×** | **125.7 KB** |

vs Genesis @2048: **proof 67× smaller, prover ~4× lighter**; trade: verifier does group ops
(686 smuls) instead of field ops, so Genesis wins verification wall-clock at small n, Lens
wins proof size everywhere and the verifier from n ≳ 1024. Honest caveats: 20 demo queries
(~2^-20; production ~80-100 multiplies verifier/proof ~4×); the joint IPA+FRI extraction
argument (shared challenges) is the paper-grade obligation — analogous to but smaller than
Genesis's unwritten composition, since both halves analyze the *same* transcript.

## Entry 20 — **Exodus**: no FRI, no hashes — Genesis's proof size fixed with advice

Constraint hardened again: no FRI, no hash-based commitments. First, the reframe: **Genesis
already satisfies the letter of this** — its certificate is an information-theoretic
sumcheck; SHA appears only as Fiat–Shamir (which Bulletproofs itself needs). Its real
problem is the megabyte proof / ~8× prover, and both have one cause: the λ-deep chains
(inversion ~380 layers, Legendre ~380, CT-TS ~1200, double-and-add ~510/round).

**Exodus** deletes the chains with nondeterministic advice, made hash-free by committing
advice vectors with **Pedersen over the same basis G**:
- inversion → one check `t·d = 1` (`advice_inverse_sound`)
- sqrt → one check `y² = g`, ± freedom harmless by the binding argument
  (`advice_sqrt_sound`)
- Legendre/branch → boolean `s` + fused `y² = s·g₁ + (1−s)·g₂` (`advice_branch_sound`)
- double-and-add → the trace as advice columns, checked by ONE wide parallel deg-4 layer

Why the advice commitment doesn't recurse (the crux): every advice-opening IPA's terminal
MSM is a tensor over the same G, and all terminals RLC-merge into the ONE delegated claim
(`advice_batch_two`, i.e. `batch_amortization`; soundness converse `fold_sound`). The
circuit shrinks ~7000 → ~100 wide shallow layers; estimated proof ~300–400 KB (vs 8.4 MB),
verifier ~2–4k rounds (vs 45k), prover ~2–3× plain IPA. All four soundness atoms proven,
axiom-clean; full Lean build green (20 modules, 1426 jobs). Spec: `solutions/5-exodus.md`.

Status: design + formalized atoms; the implementation (advice-column layout, multi-point
opening batch, wide RCB layer) is Genesis-scale engineering, not yet built.

## Entry 21 — Exodus v1 implemented and measured (`sage/7-exodus.sage`)

Built: assertion-claim injection in the engine (assert-zero columns checked against the
zero-MLE at fresh transcript points), advice as input-boundary columns (tv = 1/den, branch
bit s, root y — statement-independent, computed at setup), the shallow derivation (~85
layers replacing ~1250: Poseidon + 10 SWU/advice layers + isogeny; circuit 1755→981 layers
at k=2), and Pedersen advice commitments at setup.

**Two findings worth the build:**
1. **The advice-opening regress is real and the spec's RLC argument alone doesn't stop it**
   — each certificate pass regenerates advice claims at fresh points. Fixes found:
   statement-independent advice → committed at setup (public, recomputable); opening IPA
   **reuses the main IPA's challenges** so its terminal is the already-certified Q.
2. **The two-field problem resurfaces at the advice opening**: advice values live in F_p
   (circuit field) but Pedersen-over-Pallas opens in F_q — an F_p-MLE claim can't be an
   F_q inner product. The correct completion: **commit advice over Vesta** (scalar field =
   F_p!) with a symmetric second-curve certificate terminating via mutual challenge-reuse —
   the Pasta cycle finally earning its keep in a non-recursive design. v1 ships with a
   native O(n)-field-op advice check (~60ms, clearly labeled) pending the Vesta pairing.

**Measured** (vs Genesis at the same sizes):

| n | prove | verify | naive | speedup | proof |
|---|---|---|---|---|---|
| 64 | 9.1s (G 11.5) | 0.52s (G 0.66) | 0.37s | 0.7× | 2.4 MB (G 3.4) |
| 256 | 36.0s (G 46.3) | 0.81s (G 1.00) | 1.28s | 1.6× | 3.8 MB (G 5.1) |
| 512 | 74.9s (G 95.5) | 1.00s (G 1.20) | 2.47s | 2.5× | 4.7 MB (G 6.1) |
| 2048 | 358.9s (G 391.4) | **1.38s** (G 1.69) | 9.49s | **6.9×** | **6.6 MB** (G 8.4) |

Verify −18%, proof −22%, prover −8–20% — the derivation-slash delivered; the remaining MBs
are the FOLD certificate (as the accounting predicted). The designed-but-unbuilt **wide
cross-round fold restructure** (510·k → 510 layers via prefix-block indexing, public
bit-schedule columns, wiring sumchecks) is the ~4× proof lever; with it Exodus targets
~1.5 MB, and with GLV ~1 MB. All hash-free.

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
| `sum_split` / `msm_split` | Delegation | the sumcheck D&C halving step (Atlas/Genesis) |
| `sumcheck_round_complete` | Delegation | round-check completeness |
| `disagreement_is_root`, `cheating_caught` | Delegation | round soundness (1-var Schwartz–Zippel) |
| `genesis_reduction` | Genesis | seed-composed certificate ⇒ SRS claim |
| `double_and_add_step` | Genesis | scalar-mult circuit layer |
| `square_and_multiply_step` | Genesis | exponent-chain circuit layer |
| `sqrt_exp_correct` | Genesis | deterministic in-circuit sqrt is correct |
| `dark_eval_check` | DARK | O(1) verifier, unknown order |
| `dark_witness_rigid` | DARK | unknown order pins the witness |
| `msm_eq_dlog_inner` | DlogLayer | MSM = hidden inner product |
| `msm_structured_srs` | DlogLayer | geometric dlogs = poly eval |
| `genFinal_structured` | DlogLayer | structured ⇒ `bSuccinct·g` |
| `structured_breaks_binding` | DlogLayer | public structure ⇒ not binding |

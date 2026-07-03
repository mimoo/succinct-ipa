/-
# The IPA verifier: linear vs. succinct

The final IPA check (Bulletproofs form) is

    P₀  =  a • G₀  +  (a · b₀) • U                                   (★)

where, after `k = log₂ n` rounds with challenges `x`,
  * `G₀ = ⟨s, G⟩`  is the folded generator (an `n`-term MSM),
  * `b₀ = ⟨s, (z^i)⟩` is the folded evaluation scalar,
  * `a`  is the single scalar the prover sends last,
  * `P₀` is the verifier's folded commitment (already `O(k)` to maintain).

`b₀` is succinct: by `bSuccinct_eq_bLinear` it equals an `O(k)` product.
`G₀` is **not** succinct for unstructured `G` — and that is fundamental, not an
artifact of this encoding: an MSM against generators with no exploitable structure
costs `Θ(n)`.  So a succinct verifier must obtain `G₀` some other way.  We make that
"other way" an explicit object — a `GenOracle` — instead of hiding it.  The whole
content of "is this verifier succinct and correct?" then becomes a single, provable
statement (`succinct_correct`), and the *assumption* you must discharge to deploy it
is laid bare as the oracle's `certifies` field.

Two ways to instantiate `GenOracle` are discussed at the bottom of the file.
-/
import SuccinctIPA.SVector

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]
variable {k : ℕ}

/-- The folded generator `G₀ = ⟨s, gens⟩` — the linear (`Θ(2^k)`) MSM.
    Generators are indexed by bit-sets to match `sCoeff`. -/
def genFinal (gens : Finset (Fin k) → G) (x : Fin k → F) : G :=
  ∑ t : Finset (Fin k), sCoeff x t • gens t

/-- The reference **linear-time verifier**'s acceptance predicate: it forms `b₀` the
    expanded way (`bLinear`) and `G₀` by the full MSM (`genFinal`), then checks (★). -/
def LinearAccept
    (gens : Finset (Fin k) → G) (U P₀ : G) (x : Fin k → F) (z a : F) : Prop :=
  P₀ = a • genFinal gens x + (a * bLinear x z) • U

/-- A **generator-commitment oracle**: an external mechanism that certifies a claimed
    value `Q` of the folded generator `G₀`, without the verifier recomputing the MSM.
    The `certifies` field is the assumption a deployment must discharge. -/
structure GenOracle (gens : Finset (Fin k) → G) (x : Fin k → F) where
  /-- The point the oracle hands the verifier as `G₀`. -/
  Q : G
  /-- Its correctness guarantee: `Q` really is the folded generator. -/
  certifies : Q = genFinal gens x

/-- The **succinct verifier**'s acceptance predicate.  It does **no** `n`-term MSM:
    `b₀` is the `O(k)` product `bSuccinct`, and `G₀` is taken from the oracle as `Ω.Q`.
    All field work here is `O(k) = O(log n)`. -/
def SuccinctAccept
    {gens : Finset (Fin k) → G} {x : Fin k → F}
    (Ω : GenOracle gens x) (U P₀ : G) (z a : F) : Prop :=
  P₀ = a • Ω.Q + (a * bSuccinct x z) • U

/-- **Correctness of the succinct verifier.**  Given a correct oracle, the succinct
    verifier accepts a transcript *iff* the linear reference verifier does — yet it only
    ever performs `O(log n)` work.  The proof is exactly the two facts we isolated:
    `b₀` succinctness (`bSuccinct_eq_bLinear`) and the oracle's certificate. -/
theorem succinct_correct
    {gens : Finset (Fin k) → G} {x : Fin k → F}
    (Ω : GenOracle gens x) (U P₀ : G) (z a : F) :
    SuccinctAccept Ω U P₀ z a ↔ LinearAccept gens U P₀ x z a := by
  unfold SuccinctAccept LinearAccept
  rw [bSuccinct_eq_bLinear, Ω.certifies]

/-!
## Discharging the oracle — i.e. *finding* a succinct dlog verifier

`succinct_correct` reduces "succinct verifier" to "a `GenOracle` whose `certifies`
holds".  There is no way to build that oracle for free under a plain, transparent dlog
setup — computing `⟨s, gens⟩` is genuinely `Θ(n)`, and that matches the known linear
lower bound for commitments to unstructured generators.  Succinctness is bought by
adding structure.  Two concrete instantiations:

1. **Accumulation / recursion (Halo-style), still plain dlog, transparent.**
   Do not certify `Q` now.  Send `Q` as a claim and *fold* the statement
   "`Q = ⟨s, gens⟩`" into a running accumulator.  Each proof's per-verifier cost is the
   succinct `SuccinctAccept` check; the single linear MSM is paid **once**, at the end of
   a batch of `m` proofs, so the amortised verifier is `O(log n + (n/m))`.  Formally this
   is a `GenOracle` whose `certifies` is discharged later by one MSM shared across the batch.

2. **Structured SRS, `gensₜ = [τ^{coord t}]` for a hidden `τ`.**  Then
   `⟨s, gens⟩ = [ Σ s_i τ^i ] = [ g(τ) ]`, and by `bSuccinct_eq_bLinear` (with `z := τ`)
   this equals `[bSuccinct x τ]` — a *single* group element the verifier checks with one
   pairing/opening.  This yields a true (non-amortised) succinct verifier, at the price of
   a trusted/updatable setup and pairing assumptions — i.e. it leaves "plain dlog".

The trichotomy is the real answer to "can dlog IPA have a succinct verifier?":
*not transparently and non-interactively without recursion* (option 1 amortises it,
option 2 changes the assumption).  The Lean above makes the dividing line a single,
checkable hypothesis. -/

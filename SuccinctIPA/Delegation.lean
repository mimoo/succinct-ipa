/-
# Divide and conquer — delegating the verifier's MSM (sumcheck/GKR + preprocessing evaluation)

Reframe the bottleneck.  The IPA verifier's linear step is checking `G₀ = ⟨s, G⟩` — a
**deterministic computation on public inputs** (`s` from the Fiat–Shamir challenges, `G` the
fixed SRS).  There is no witness and nothing secret.  Certifying a public computation does not
need *cryptography* at all — it is the **delegation** problem, solved information-theoretically
by sumcheck/GKR.  And sumcheck is exactly a divide-and-conquer proof system: the MSM is a
binary addition tree of depth `log n`; each sumcheck round splits the sum in half
(`sum_split`/`msm_split` below), the verifier does `O(1)` work per round, and after `log n`
rounds the whole tree has collapsed to **one evaluation of the input's multilinear extension**
at a random point.

Where the divide-and-conquer bottoms out, the input MLE splits in two:

  * the **challenge side** — the circuit takes only the `k = log n` challenges `x₁…x_k` as
    input and computes the tensor `s` internally (a perfectly uniform, log-depth circuit); the
    verifier handles this side in `O(log n)` directly (this is the tensor identity already
    proven: `bSuccinct_eq_bLinear`, `sCoeff_factors`);
  * the **generator side** — one evaluation of the MLE of the *coordinates of `G`*: a
    **fixed public polynomial, known to everyone at setup, forever**.

The new tool for the generator side: **polynomial evaluation with preprocessing**
(Kedlaya–Umans 2008; Bhargava–Ghosh–Kumar–Mohapatra 2022).  A one-time, public, transparent
preprocessing of the fixed coefficient table (`n^{1+ε}` time/space, reusable for all proofs
for all time) yields a data structure that evaluates the MLE at **any** point in
`polylog(n) · polylog(q)` time.  The recursion of proofs is replaced by an *algorithmic* data
structure: the D&C terminates in preprocessing, not in another proof.

The assembled scheme — transparent, prime-order, **no pairing, no unknown order, no
recursion**:
  * Setup (one-time, public, deterministic): `G = hash_to_curve(0…n−1)`; build the KU data
    structure for the coordinate MLEs of `G`.
  * Commit: Pedersen `⟨a, G⟩` — one group element.
  * Open: Bulletproofs IPA transcript (`O(log n)` group elements) **plus** a Fiat–Shamir'd
    GKR/sumcheck certificate for the claim `G₀ = ⟨s, G⟩` over the base field (`polylog`
    field elements; the MSM double-and-add circuit is uniform and log-depth, so the wiring
    MLEs are polylog-evaluable).
  * Verify: `O(log n)` IPA checks + `polylog` sumcheck rounds + one KU evaluation — **polylog
    total online**; soundness of the delegated part is *unconditional* (it is an interactive
    proof, not an argument, so no extra assumption enters).
  * Prover: the honest MSM work `O(n·λ)` plus the GKR prover (linear in circuit size, **no
    commitments, no FFTs, no proof generation per step, no verifier-in-circuit**).

This file proves the divide-and-conquer core: the split identity at field and group level
(the addition-tree step sumcheck climbs), the round-check identity (completeness), and the
one-variable Schwartz–Zippel bound (round soundness: a cheating round polynomial agrees with
the honest one on at most `deg` points, so a random challenge catches it w.h.p.).  These are
the exact engine parts of sumcheck; the full GKR stack is engineering on top of them.
-/
import SuccinctIPA.Basic
import Mathlib.Algebra.Polynomial.Roots

open Finset Polynomial

namespace SuccinctIPA

variable {F : Type*} [Field F]

/-- **The divide-and-conquer step (field level).**  A sum over an `m`-cube splits into two
    sums over the `(m−1)`-cube along the first coordinate — the identity sumcheck applies
    once per round, `log n` times in total. -/
theorem sum_split {κ : Type*} [Fintype κ] (f : Bool × κ → F) :
    ∑ p : Bool × κ, f p
      = (∑ b : κ, f (true, b)) + ∑ b : κ, f (false, b) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]

/-- **The divide-and-conquer step (group level).**  The verifier's MSM is a binary addition
    tree: it splits along the top bit into two half-size MSMs.  This is the tree that the
    GKR delegation climbs with `O(1)` verifier work per level. -/
theorem msm_split {κ : Type*} [Fintype κ]
    {G : Type*} [AddCommGroup G] [Module F G]
    (s : Bool × κ → F) (P : Bool × κ → G) :
    msm s P
      = msm (fun b => s (true, b)) (fun b => P (true, b))
        + msm (fun b => s (false, b)) (fun b => P (false, b)) := by
  unfold msm
  rw [Fintype.sum_prod_type, Fintype.sum_bool]

/-- **Sumcheck round check (completeness).**  The prover sends a univariate `p`; if `p`
    honestly interpolates the two half-sums at `0` and `1`, the verifier's round check
    `p(0) + p(1) = claim` accepts the true claim.  All the verifier computes is two
    evaluations of a degree-`d` polynomial: `O(1)` per round. -/
theorem sumcheck_round_complete {κ : Type*} [Fintype κ] (f : Bool × κ → F) (p : F[X])
    (h0 : p.eval 0 = ∑ b : κ, f (false, b))
    (h1 : p.eval 1 = ∑ b : κ, f (true, b)) :
    p.eval 1 + p.eval 0 = ∑ q : Bool × κ, f q := by
  rw [h0, h1, sum_split]

/-- **Round soundness, part 1.**  If a (possibly cheating) round polynomial `p` agrees with
    the honest one `q` at the verifier's challenge `r`, then `r` is a root of `p − q`. -/
theorem disagreement_is_root (p q : F[X]) (hne : p ≠ q) (r : F)
    (hr : p.eval r = q.eval r) : r ∈ (p - q).roots := by
  rw [mem_roots']
  exact ⟨sub_ne_zero.mpr hne, by simp [IsRoot, eval_sub, hr]⟩

/-- **Round soundness, part 2 (one-variable Schwartz–Zippel).**  A cheating round polynomial
    survives the challenge only on a set of size `≤ max(deg p, deg q)` — so a uniformly random
    challenge from `F` catches the lie except with probability `≤ d/|F|`.  Iterated over
    `log n` rounds this is the full information-theoretic soundness of the delegation: **no
    cryptographic assumption enters the MSM certificate.** -/
theorem cheating_caught [DecidableEq F] (p q : F[X]) :
    (p - q).roots.toFinset.card ≤ max p.natDegree q.natDegree :=
  le_trans (Multiset.toFinset_card_le _)
    (le_trans (Polynomial.card_roots' _) (Polynomial.natDegree_sub_le p q))

/-!
## Where the recursion bottoms out — and why nothing circular remains

After `log n` rounds the delegated MSM claim has collapsed to evaluating the input MLE at one
random point.  The input of the (uniform, log-depth) MSM circuit is:

1. the `k = log n` **challenges** — the verifier reads them itself; the tensor expansion to
   `s` happens *inside* the delegated circuit, and the corresponding wiring/eval structure is
   the already-proven tensor identity (`bSuccinct_eq_bLinear`);
2. the **coordinates of the fixed public generators** — one MLE evaluation of a polynomial
   fixed at setup.  This is where every previous attempt went circular (evaluating it is
   another `n`-sized job; committing to it needs another PCS; pairing it needs bilinearity).
   The escape is *algorithmic*, not cryptographic: **preprocessing polynomial evaluation**
   (Kedlaya–Umans).  One-time public `n^{1+ε}` preprocessing of the fixed coefficient table;
   then *every* subsequent evaluation, at any point, for any proof, costs `polylog(n)`.

So the divide-and-conquer terminates in a data structure instead of a proof.  No pairing, no
unknown order, no recursion, prime-order dlog, transparent — verifier `polylog`, proof
`polylog`, prover linear with small constants (no commitments beyond the original Pedersen,
no FFTs, no circuit-encoded verifier).

Honest caveats, clearly stated: (i) Kedlaya–Umans-style preprocessing is asymptotic — the
constants and the `n^{1+ε}` table are currently galactic in practice; (ii) the end-to-end
composition (Bulletproofs extraction + Fiat–Shamir'd GKR certificate + KU input oracle) needs
a careful paper-grade security proof — the parts proven here are the D&C engine (split,
round completeness, round soundness) and the tensor side; (iii) the setup cost was always
`Θ(n)` (sampling `G`) — preprocessing raises it to `n^{1+ε}`, still one-time, public and
deterministic, hence transparent. -/

end SuccinctIPA

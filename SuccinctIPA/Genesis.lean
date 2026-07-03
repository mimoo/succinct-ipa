/-
# Genesis — formal correctness of the seed-derived delegation (`solutions/2-genesis.md`)

Genesis replaces Atlas's Kedlaya–Umans table with **in-circuit SRS derivation**: the delegated
circuit takes only the seed and the `log n` challenges, derives the generators internally by
hash-to-curve, and computes the MSM.  The delegation machinery itself is proven in
`Delegation.lean` (`sum_split`, `msm_split`, `sumcheck_round_complete`, `disagreement_is_root`,
`cheating_caught`).  This file verifies what is *new* in Genesis — the reduction and the
gate-level correctness of each nonstandard circuit stage:

* `genesis_reduction` — certifying the seed-composed computation certifies the claim about
  the published SRS (determinism of the derivation is exactly what makes the composition
  sound; nothing else is needed).
* `double_and_add_step` — one layer of the scalar-multiplication circuit: the binary
  (Horner) recurrence `(2e + b) • P = 2 • (e • P) + [b] • P`.  Iterated over the `λ` bits of a
  scalar this is the whole double-and-add stage.
* `square_and_multiply_step` — the multiplicative analogue, one layer of the fixed-exponent
  chain `a^{(p+1)/4}` used for deterministic square roots in point decompression (no
  nondeterministic advice — advice would be an `n`-sized input and reintroduce the
  circularity that Genesis exists to remove).
* `sqrt_exp_correct` — completeness of the deterministic square root: if `a^m = 1`
  (for quadratic residues mod `p` this is Euler's criterion with `m = (p−1)/2`, mathlib's
  `ZMod.euler_criterion`) and `2t = m + 1` (i.e. `t = (p+1)/4` for `p ≡ 3 mod 4`), then
  `(a^t)² = a` — the exponent chain really outputs a square root.

Together with the tensor identity (`bSuccinct_eq_bLinear`) for the challenge-expansion stage
and `msm_split` for the addition tree, every circuit stage of Genesis has a machine-checked
correctness lemma.
-/
import SuccinctIPA.Delegation

open Finset

namespace SuccinctIPA

variable {F : Type*} [Field F]

/-- **The Genesis reduction.**  If the published SRS is (by definition) the seed-derived
    family, then a certificate for the *composed* computation `Q = ⟨s, derive(seed)⟩` is a
    certificate for the claim `Q = ⟨s, gens⟩` about the published generators.  Determinism of
    the derivation is the entire content — no cryptographic property of `derive` is used here
    (binding enters only through the usual dlog assumption on hash outputs). -/
theorem genesis_reduction {S ι : Type*} [Fintype ι]
    {G : Type*} [AddCommGroup G] [Module F G]
    (derive : S → ι → G) (seed : S) (gens : ι → G)
    (hpub : ∀ i, gens i = derive seed i)
    (s : ι → F) (Q : G)
    (hcert : Q = msm s (derive seed)) :
    Q = msm s gens := by
  rw [hcert]
  unfold msm
  exact Finset.sum_congr rfl (fun i _ => by rw [hpub i])

/-- **One double-and-add layer.**  The scalar-multiplication stage processes the scalar's
    bits by the Horner recurrence: `(2e + b) • P = 2 • (e • P) + [b] • P`.  Applied `λ` times
    this is the entire in-circuit scalar multiplication — each layer is one doubling, one
    conditional addition. -/
theorem double_and_add_step {G : Type*} [AddCommMonoid G] (b : Bool) (e : ℕ) (P : G) :
    (2 * e + b.toNat) • P = 2 • (e • P) + (if b then P else 0) := by
  cases b <;> simp [add_nsmul, mul_nsmul, smul_comm e 2 P]

/-- **One square-and-multiply layer.**  The multiplicative analogue, used for the fixed
    exponentiations in the deterministic square-root chain of point decompression:
    `a^(2e + b) = (a^e)² · a^[b]`. -/
theorem square_and_multiply_step {M : Type*} [Monoid M] (b : Bool) (e : ℕ) (a : M) :
    a ^ (2 * e + b.toNat) = (a ^ e) ^ 2 * (if b then a else 1) := by
  cases b <;> simp [pow_add, pow_mul, mul_comm]

/-- **The deterministic square root is correct.**  If `a^m = 1` and `2t = m + 1`, then
    `(a^t)² = a`.  Instantiate `m = (p−1)/2`, `t = (p+1)/4` for a prime `p ≡ 3 mod 4`: for a
    quadratic residue `a`, Euler's criterion gives `a^m = 1`, so the in-circuit chain
    `a ↦ a^t` (built from `square_and_multiply_step` layers) outputs a genuine root —
    deterministically, with no advice. -/
theorem sqrt_exp_correct {M : Type*} [Monoid M] (a : M) (t m : ℕ)
    (hm : a ^ m = 1) (ht : 2 * t = m + 1) :
    (a ^ t) ^ 2 = a := by
  rw [← pow_mul, mul_comm, ht, pow_succ, hm, one_mul]

end SuccinctIPA

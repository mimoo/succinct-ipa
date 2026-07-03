/-
# Making it happen, route 2 — evaluation-as-division (DARK), unknown-order, transparent

This is the route that *does* give a truly succinct, transparent, non-recursive verifier —
by leaving prime-order dlog for a group of **unknown order** (class group / RSA group),
which is still a discrete-log–flavoured assumption (hardness of order/root extraction).

The trick (Bünz–Fisch–Szepieniec, "DARK"): instead of committing to the coefficient
vector with `n` generators (Pedersen/IPA), encode the *whole* polynomial in the exponent
of a **single** generator using a large public integer base `q`:

    C  =  p(q) • g            (q chosen larger than any coefficient ⇒ injective encoding)

To open `p(z) = y`, the prover sends one witness `W = ((p(q) − p(z)) / (q − z)) • g`, and
the verifier checks the single group equation

    C − y•g  =  (q − z) • W.

The verifier performs **O(1) group operations**, independent of `n = deg p` — it never
looks at the coefficients.  Completeness is exactly the factor theorem `(q−z) ∣ p(q)−p(z)`;
soundness is the unknown-order assumption that pins `W` (no `(q−z)`-torsion to exploit).

Here `g : G` with `G` a module over a commutative ring `R` (take `R = ℤ` for the
unknown-order instantiation; `ℤ`-module structure exists for every `AddCommGroup`).
-/
import SuccinctIPA.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Abel

open Polynomial

namespace SuccinctIPA

variable {R : Type*} [CommRing R] {G : Type*} [AddCommGroup G] [Module R G]

/-- **DARK evaluation check — completeness.**  There is a single witness `W` making the
    verifier's one-line check `C − y•g = (q − z)•W` hold, where `C = p(q)•g`, `y = p(z)`.
    The verifier does O(1) group ops, *independent of `deg p`*.  The witness exists because
    of the factor theorem: `(q − z) ∣ p(q) − p(z)`. -/
theorem dark_eval_check (g : G) (p : R[X]) (z q : R) :
    ∃ W : G, (p.eval q) • g - (p.eval z) • g = (q - z) • W := by
  obtain ⟨w, hw⟩ := sub_dvd_eval_sub q z p
  exact ⟨w • g, by rw [← sub_smul, hw, mul_smul]⟩

/-- **Soundness ingredient.**  Any two accepted witnesses agree up to `(q − z)`-torsion:
    `(q − z) • (W − W') = 0`.  In a group of *unknown order* with no small-order elements
    (strong-RSA / adaptive-root) the only such element is `0`, forcing `W = W'` and pinning
    the opening.  This is precisely the step that needs to leave prime-order dlog. -/
theorem dark_witness_rigid (z q : R) (C ywg W W' : G)
    (h : C - ywg = (q - z) • W) (h' : C - ywg = (q - z) • W') :
    (q - z) • (W - W') = 0 := by
  rw [smul_sub, ← h, ← h', sub_self]

/-- The encoding is additively homomorphic: `Commit(p₁+p₂) = Commit(p₁)+Commit(p₂)`. -/
theorem dark_commit_linear (g : G) (p₁ p₂ : R[X]) (q : R) :
    (p₁ + p₂).eval q • g = p₁.eval q • g + p₂.eval q • g := by
  rw [eval_add, add_smul]

/-- **Commitment splits with the polynomial — the engine of the `O(log n)` recursion.**
    Writing `p = p_L + X^m·p_R`, the commitment factors as `Commit(p) = Commit(p_L) +
    q^m·Commit(p_R)`.  So the prover sends the two half-commitments, the verifier folds them
    in **one** group operation, and a random challenge halves the degree — `log₂ n` rounds,
    `O(1)` verifier work each, `O(log n)` proof.  Combined with `dark_eval_check`, the whole
    evaluation argument is logarithmic in both proof size and verifier time, with an `O(1)`
    commitment (one group element). -/
theorem dark_commit_split (g : G) (pL pR : R[X]) (m : ℕ) (q : R) :
    (pL + X ^ m * pR).eval q • g = pL.eval q • g + q ^ m • (pR.eval q • g) := by
  rw [eval_add, eval_mul, eval_pow, eval_X, add_smul, mul_smul]

/-- **Openings batch into a single `O(1)` proof.**  Two evaluation proofs at the same point
    combine, under a random `α`, into *one* witness `W₁ + α•W₂` satisfying *one* check.  So
    `m` openings cost one group equation and one combined witness — the proof stays `O(1)`,
    unlike Hyrax where each opening carries `√n`. -/
theorem dark_eval_batch (z q : R) (C₁ y₁g C₂ y₂g W₁ W₂ : G) (α : R)
    (h₁ : C₁ - y₁g = (q - z) • W₁) (h₂ : C₂ - y₂g = (q - z) • W₂) :
    (C₁ + α • C₂) - (y₁g + α • y₂g) = (q - z) • (W₁ + α • W₂) := by
  rw [show (q - z) • (W₁ + α • W₂) = (C₁ - y₁g) + α • (C₂ - y₂g) from by
        rw [smul_add, ← h₁, smul_smul, mul_comm (q - z) α, ← smul_smul, ← h₂],
     smul_sub]
  abel

end SuccinctIPA
